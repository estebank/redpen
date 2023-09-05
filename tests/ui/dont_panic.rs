#![allow(redpen::infallible_allocation)]
#![deny(redpen::dont_panic)]
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
    #[deny(redpen::dont_panic)]
    fn from_impl(&self) {
        panic!();
    }
}

struct X;
impl A for X {
    fn from_trait(&self) {}
    fn from_a_impl(&self) {}
}

#[redpen::wont_panic]
fn might_panic() {
    panic!()
}

fn impl_fn(x: impl A) {
    x.from_trait();
    x.from_a_impl();
}
fn trait_object(x: Box<dyn A>) {
    x.from_trait();
    x.from_a_impl();
}

fn foo() {
    S.foo();
    S.from_trait();
    S.from_a_impl();
    S.from_impl();
    X.from_trait();
    X.from_a_impl();
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
    panic!("shouldn't happen!");
}

fn bar() {
    foo();
}

fn baz() {
}

fn boxed() -> Box<dyn A> {
    unimplemented!();
}
fn main() {
    foo();
    bar();
    baz();
    trait_object(Box::new(S));
    trait_object(Box::new(X));
    trait_object(boxed());
    impl_fn(S);
    impl_fn(X);
}