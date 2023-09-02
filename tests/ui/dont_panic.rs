struct S;

impl S {
    fn foo(&self) {
        panic!("");
    }
}

trait A {
    fn from_trait(&self) {
        panic!();
    }
    fn from_a_impl(&self);
}
trait B {
    fn from_impl(&self);
}

impl A for S {
    fn from_a_impl(&self) {
        panic!();
    }
}
impl B for S {
    fn from_impl(&self) {
        panic!();
    }
}

#[redpen::wont_panic]
fn might_panic() {
    panic!()
}

#[deny(redpen::dont_panic)]
fn impl_fn(x: impl A) {
    x.from_trait();
    x.from_a_impl();
}
#[deny(redpen::dont_panic)]
fn trait_object(x: Box<dyn A>) {
    x.from_trait();
    x.from_a_impl();
}

#[deny(redpen::dont_panic)]
fn foo() {
    panic!("shouldn't happen!");
    S.foo();
    S.from_trait();
    S.from_a_impl();
    S.from_impl();
    #[allow(redpen::dont_panic)]
    (|| {
        panic!();
    })();
    #[allow(redpen::dont_panic)]
    let x =  || panic!();
    x();
    let mut x = vec![];
    x.push("");
    let _ = x[1];
    might_panic();
}

#[deny(redpen::dont_panic)]
fn bar() {
    foo();
}

#[deny(redpen::dont_panic)]
fn baz() {
}

fn main() {
    foo();
    bar();
    baz();
}