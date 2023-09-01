# Don't Panic 👍

This lint allows you to annotate `fn` with a requirement that they will
never be able to invoke `panic!()` directly or transitively.

If a specific `fn` might invoke `panic!()`, but as a developer you want to
assert that it will never do so, you can use `#[redpen::wont_panic]` to
inform the lint of that.

```rust
fn bar() {
    panic!();
}

#[redpen::wont_panic]
fn baz() {
    panic!();
}
#[redpen::dont_panic]
fn foo() {
    bar();
    baz();
}
```

```
error: `foo` can panic
  --> $DIR/dont_panic.rs:47:1
   |
46 |   #[redpen::dont_panic]
   |   --------------------- the function can't panic due to this annotation
47 |   fn foo() {
   |   ^^^^^^^^ this function can panic
48 |       bar();
   |       --- panic can occur here
```

## Limitations

For now, indexing operations are always treated as potentially panicking,
*even if the invoked `impl` will never panic*. This is because the
necessary `rustc` API is currently private. This will change in the future.