# Disallow specific types for type parameter

This lint allows you to annotate an item (`struct`, `enum`, `fn`, etc.)
with generic parameters with a restriction that a specific parameter can
*not* be of a specific type. For example, if a `fn` accepts anything that
might implement `Display`, we could use this annotation to exclude `String`
from being used when calling it.

```rust
#[redpen::disallow(T = "Pineapple")] // Here the str is the *full path* as seen by rustc, like `std::string::String`.
struct Pizza<T>(T);
struct Pineapple;

// The lint also on expressions
let _ = Pizza(Pineapple); // error

// The lint also works on all paths for types
type Alias = Pizza<Pineapple>; // error
fn foo(p: Pizza<Pineapple>) -> Pizza<Pineapple> { // two errors
    p // error, because it is an expression
}

```