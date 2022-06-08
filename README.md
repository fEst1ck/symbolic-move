# Symbolic Move
This is an in-progress symbolic executor for the [Move](https://github.com/diem/move) language.

# Basic Example
Here's an example
```move
// in module 0x2::foo
fun bar(a: u8, b: u8) {
      let x = 1;
      let y = 0;
      if (a != 0) {
        y = 3 + x;
        if (b == 0) {
          x = 2 * (a + b);
        }
      };
      assert(x - y != 0, 42);
}
```
The symbolic execution engine will explore all execution paths, and detect potential assertion violations.
```console
$ cargo run -- -t 0x2::foo::bar demo.move
...
Evaluation result #0:
Aborts with error code (U64(#x000000000000002a) ↩ (and (or (= a #x00)
         (and (not (= a #x00)) (not (= b #x00)))
         (and (not (= a #x00)) (= b #x00)))
     (= (bvmul #x02 a) (bvadd #x04 (bvmul #xfe b)))
     (not (= a #x00))
     (= b #x00))).

Evaluation result #1:
Returns with values:
```
Here the result says that the program aborts for input `a` and `b` satisfying the logical constraint
```
(and (or (= a #x00)
         (and (not (= a #x00)) (not (= b #x00)))
         (and (not (= a #x00)) (= b #x00)))
     (= (bvmul #x02 a) (bvadd #x04 (bvmul #xfe b)))
     (not (= a #x00))
     (= b #x00)))
```
We can then invoke a SMT solver to generate a test case with concrete values for `a` and `b`, say `a = 2, b = 0`, which triggers
the assertion at runtime.

# Todo
The symbolic executor currently handles only finitized programs. I am currently working on encoding loops with z3 recursive functions and fixedpoints.
