Why does this compile?

```rust
Bytecode::Branch(_, then_label, else_label, cond) =>
  branch(s.local_state.get_ctx(), &s.label_to_offset, *cond, then_label, else_label, s.local_state)
  .into_iter()
  .map(|local_state| MoveState {
    local_state,
    ..s
  }).collect(),
```

```rust
--> src/state.rs:125:51
    |
122 |   fn bitand(self, rhs: Constraint<'ctx>) -> Self::Output {
    |                   --- captured outer variable
...
125 |       locals: self.locals.into_iter().map(|x| x & rhs).collect(),
    |                                           --------^^^
    |                                           |       |
    |                                           |       move occurs because `rhs` has type `z3::ast::Bool<'_>`, which does not implement the `Copy` trait
    |                                           captured by this `FnMut` closure
```