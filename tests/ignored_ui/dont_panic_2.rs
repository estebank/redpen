#![allow(redpen::infallible_allocation)]
#![deny(redpen::dont_panic)]
struct S<T: Trait>(T);

struct X;
impl Trait for X {}
trait Trait {
    fn panic() {
        panic!();
    }
}

impl<T: Trait> S<T> {
    fn foo(&self) {
        T::panic();
    }
}

trait A<T: Trait> {
    fn from_trait(&self) {
        T::panic();
    }
    fn from_a_impl(&self);
}
trait B<T> {
    fn from_impl(&self);
}

impl<T: Trait> A<T> for S<T> {
    fn from_a_impl(&self) {
        self.foo();
    }
}
impl<T: Trait> B<T> for S<T> {
    fn from_impl(&self) {
        self.foo();
    }
}

fn impl_fn<T: Trait>(x: impl A<T>) {
    x.from_trait();
    x.from_a_impl();
}
fn trait_object<T: Trait>(x: Box<dyn A<T>>) {
    x.from_trait();
    x.from_a_impl();
}

fn foo1() {
    panic!("shouldn't happen!");
}
fn foo2() {
    S(X).foo();
}
fn foo3() {
    S(X).from_trait();
}
fn foo4() {
    S(X).from_a_impl();
}
fn foo5() {
    S(X).from_impl();
}
fn foo6() {
    (|| {
        panic!();
    })();
}
fn foo7() {
    #[allow(redpen::dont_panic)]
    let x =  || panic!();
    x();
}
fn foo8() {
    let mut x = vec![];
    x.push("");
    x.swap_remove(0);
    let _ = x[1];
}

fn bar() {
    foo1();
}

fn baz() {
}

fn main() {
    foo1();
    foo2();
    foo3();
    foo4();
    foo5();
    foo6();
    foo7();
    bar();
    baz();
}