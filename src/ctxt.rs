use std::any::{Any, TypeId};
use std::cell::RefCell;

use rusqlite::{Connection, OptionalExtension};
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::sync::Lrc;
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
use rustc_serialize::{Decodable, Encodable};
use rustc_span::{Span, DUMMY_SP};

use crate::preempt_count::UseSite;

pub(crate) trait Query: 'static {
    const NAME: &'static str;

    type Key<'tcx>;
    type Value<'tcx>;
}

pub(crate) trait QueryValueDecodable: Query {
    fn encode_value<'tcx>(value: &Self::Value<'tcx>, cx: &mut crate::serde::EncodeContext<'tcx>);

    fn decode_value<'a, 'tcx>(cx: &mut crate::serde::DecodeContext<'a, 'tcx>) -> Self::Value<'tcx>;
}

impl<Q: Query> QueryValueDecodable for Q
where
    for<'a, 'tcx> Q::Value<'tcx>: Encodable<crate::serde::EncodeContext<'tcx>>
        + Decodable<crate::serde::DecodeContext<'a, 'tcx>>,
{
    fn encode_value<'tcx>(value: &Self::Value<'tcx>, cx: &mut crate::serde::EncodeContext<'tcx>) {
        Encodable::encode(value, cx)
    }

    fn decode_value<'a, 'tcx>(cx: &mut crate::serde::DecodeContext<'a, 'tcx>) -> Self::Value<'tcx> {
        Decodable::decode(cx)
    }
}

pub(crate) trait PersistentQuery: QueryValueDecodable {
    type LocalKey<'tcx>: Encodable<crate::serde::EncodeContext<'tcx>>;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>);
}

pub struct AnalysisCtxt<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub local_conn: Connection,
    pub sql_conn: RefCell<FxHashMap<CrateNum, Option<Lrc<Connection>>>>,

    pub call_stack: RefCell<Vec<UseSite<'tcx>>>,
    pub query_cache: RefCell<FxHashMap<TypeId, Lrc<dyn Any>>>,
}

impl<'tcx> std::ops::Deref for AnalysisCtxt<'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.tcx
    }
}

macro_rules! memoize {
    ($(#[$attr:meta])* $vis:vis fn $name:ident<$tcx: lifetime>($cx:ident: $($_: ty)?, $($key:ident: $key_ty:ty),* $(,)?) -> $ret: ty { $($body: tt)* }) => {
        #[allow(non_camel_case_types)]
        $vis struct $name;

        impl crate::ctxt::Query for $name {
            const NAME: &'static str = core::stringify!($name);

            #[allow(unused_parens)]
            type Key<$tcx> = ($($key_ty),*);
            type Value<$tcx> = $ret;
        }

        impl<'tcx> crate::ctxt::AnalysisCtxt<'tcx> {
            $vis fn $name(&self, $($key: $key_ty,)*) -> $ret {
                $(#[$attr])*
                fn $name<$tcx>($cx: &crate::ctxt::AnalysisCtxt<$tcx>, $($key: $key_ty),*) -> $ret {
                    $($body)*
                }
                let pack = ($($key),*);
                let cache = self.query_cache::<$name>();
                {
                    let guard = cache.borrow();
                    if let Some(val) = guard.get(&pack) {
                        return <$ret>::clone(val);
                    }
                }
                let val = $name(self, $($key),*);
                let mut guard = cache.borrow_mut();
                guard.insert(pack, <$ret>::clone(&val));
                val
            }
        }
    }
}

const SCHEMA_VERSION: u32 = 1;

impl Drop for AnalysisCtxt<'_> {
    fn drop(&mut self) {
        self.local_conn.execute("commit", ()).unwrap();
    }
}

impl<'tcx> AnalysisCtxt<'tcx> {
    pub(crate) fn query_cache<Q: Query>(
        &self,
    ) -> Lrc<RefCell<FxHashMap<Q::Key<'tcx>, Q::Value<'tcx>>>> {
        let key = TypeId::of::<Q>();
        let mut guard = self.query_cache.borrow_mut();
        let cache = guard
            .entry(key)
            .or_insert_with(|| {
                let cache = Lrc::new(RefCell::new(
                    FxHashMap::<Q::Key<'static>, Q::Value<'static>>::default(),
                ));
                cache
            })
            .clone()
            .downcast::<RefCell<FxHashMap<Q::Key<'static>, Q::Value<'static>>>>()
            .unwrap();
        // Everything stored inside query_cache is conceptually `'tcx`, but due to limitation
        // of `Any` we hack around the lifetime.
        unsafe { std::mem::transmute(cache) }
    }

    pub(crate) fn sql_connection(&self, cnum: CrateNum) -> Option<Lrc<Connection>> {
        if let Some(v) = self.sql_conn.borrow().get(&cnum) {
            return v.clone();
        }

        let mut guard = self.sql_conn.borrow_mut();
        if let Some(v) = guard.get(&cnum) {
            return v.clone();
        }

        let mut result = None;
        for path in self.tcx.crate_extern_paths(cnum) {
            let Some(ext) = path.extension() else {
                continue;
            };
            if ext == "rlib" || ext == "rmeta" {
                let redpen_path = path.with_extension("redpen");
                if !redpen_path.exists() {
                    continue;
                }
                let conn = Connection::open_with_flags(
                    &redpen_path,
                    rusqlite::OpenFlags::SQLITE_OPEN_READ_ONLY,
                )
                .unwrap();

                // Check the schema version matches the current version
                let mut schema_ver = 0;
                conn.pragma_query(None, "user_version", |r| {
                    schema_ver = r.get::<_, u32>(0)?;
                    Ok(())
                })
                .unwrap();

                if schema_ver != SCHEMA_VERSION {
                    info!(
                        "schema version of {} mismatch, ignoring",
                        redpen_path.display()
                    );
                }

                result = Some(Lrc::new(conn));
                break;
            }
        }

        if result.is_none() {
            warn!(
                "no redpen metadata found for crate {}",
                self.tcx.crate_name(cnum)
            );
        }

        guard.insert(cnum, result.clone());
        result
    }

    pub(crate) fn sql_create_table<Q: Query>(&self) {
        self.local_conn
            .execute_batch(&format!(
                "CREATE TABLE {} (key BLOB PRIMARY KEY, value BLOB);",
                Q::NAME
            ))
            .unwrap();
    }

    pub(crate) fn sql_load_with_span<Q: PersistentQuery>(
        &self,
        key: Q::Key<'tcx>,
        span: Span,
    ) -> Option<Q::Value<'tcx>> {
        let (cnum, local_key) = Q::into_crate_and_local(key);

        let mut encode_ctx = crate::serde::EncodeContext::new(self.tcx, span);
        local_key.encode(&mut encode_ctx);
        let encoded = encode_ctx.finish();

        let value_encoded: Vec<u8> = self
            .sql_connection(cnum)?
            .query_row(
                &format!("SELECT value FROM {} WHERE key = ?", Q::NAME),
                rusqlite::params![encoded],
                |row| row.get(0),
            )
            .optional()
            .unwrap()?;
        let mut decode_ctx = crate::serde::DecodeContext::new(self.tcx, &value_encoded, span);
        let value = Q::decode_value(&mut decode_ctx);
        Some(value)
    }

    pub(crate) fn sql_load<Q: PersistentQuery>(&self, key: Q::Key<'tcx>) -> Option<Q::Value<'tcx>> {
        self.sql_load_with_span::<Q>(key, DUMMY_SP)
    }

    pub(crate) fn sql_store_with_span<Q: PersistentQuery>(
        &self,
        key: Q::Key<'tcx>,
        value: Q::Value<'tcx>,
        span: Span,
    ) {
        let (cnum, local_key) = Q::into_crate_and_local(key);
        assert!(cnum == LOCAL_CRATE);

        let mut encode_ctx = crate::serde::EncodeContext::new(self.tcx, span);
        local_key.encode(&mut encode_ctx);
        let key_encoded = encode_ctx.finish();

        let mut encode_ctx = crate::serde::EncodeContext::new(self.tcx, span);
        Q::encode_value(&value, &mut encode_ctx);
        let value_encoded = encode_ctx.finish();

        self.local_conn
            .execute(
                &format!(
                    "INSERT OR REPLACE INTO {} (key, value) VALUES (?, ?)",
                    Q::NAME
                ),
                rusqlite::params![key_encoded, value_encoded],
            )
            .unwrap();
    }

    pub(crate) fn sql_store<Q: PersistentQuery>(&self, key: Q::Key<'tcx>, value: Q::Value<'tcx>) {
        self.sql_store_with_span::<Q>(key, value, DUMMY_SP);
    }

    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let crate_name = tcx.crate_name(LOCAL_CRATE);
        let output_filenames = tcx.output_filenames(());
        let rmeta_path =
            rustc_session::output::filename_for_metadata(tcx.sess, crate_name, output_filenames);
        let rmeta_path = rmeta_path.as_path();

        // Double check that the rmeta file is .rlib or .rmeta
        let ext = rmeta_path.extension().unwrap();
        let conn;
        if ext == "rlib" || ext == "rmeta" {
            let redpen_out = rmeta_path.with_extension("redpen");
            let _ = std::fs::remove_file(&redpen_out);
            conn = Connection::open(&redpen_out).unwrap();
        } else {
            info!("redpen called on a binary crate");
            conn = Connection::open_in_memory().unwrap();
        }

        // Check the schema version matches the current version
        let mut schema_ver = 0;
        conn.pragma_query(None, "user_version", |r| {
            schema_ver = r.get::<_, u32>(0)?;
            Ok(())
        })
        .unwrap();
        conn.execute("begin immediate", ()).unwrap();
        conn.pragma_update(None, "user_version", &SCHEMA_VERSION)
            .unwrap();

        let ret = Self {
            tcx,
            local_conn: conn,
            sql_conn: Default::default(),
            call_stack: Default::default(),
            query_cache: Default::default(),
        };
        ret.sql_create_table::<crate::preempt_count::annotation::preemption_count_annotation>();
        ret.sql_create_table::<crate::preempt_count::annotation::drop_preemption_count_annotation>(
        );
        ret.sql_create_table::<crate::preempt_count::adjustment::instance_adjustment>();
        ret.sql_create_table::<crate::preempt_count::expectation::instance_expectation>();
        ret.sql_create_table::<crate::mir::analysis_mir>();
        ret
    }
}
