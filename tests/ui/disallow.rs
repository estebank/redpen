#[redpen::disallow(T = "Pineapple")]
#[redpen::disallow(T = "&Pineapple")]
#[redpen::disallow(T = "std::string::String")]
struct Pizza<T>(T);

struct Pineapple;

type Alias = Pizza<Pineapple>; //~ ERROR
type Alias2 = Pizza<String>; //~ ERROR

fn foo(p: Pizza<Pineapple>) -> Pizza<Pineapple> {
    p
}

fn main() {
    let _ = Pizza(Pineapple);
    let _ = Pizza(String::new());

    let _ = &vec!(Pizza(&Pizza(Pineapple)));
    let _ = &vec!(Pizza(&Pizza(&Pineapple)));
}