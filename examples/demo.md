```console
$ cargo run -- -t 0x2::foo::bar demo.move
Testing function target:
fun foo::bar($t0|a: u8, $t1|b: u8) {
     var $t2|tmp#$2: bool
     var $t3|tmp#$3: u64
     var $t4|x: u8
     var $t5|y: u8
     var $t6: u8
     var $t7: u8
     var $t8: u8
     var $t9: bool
     var $t10: u8
     var $t11: u8
     var $t12: num
     var $t13: u8
     var $t14: bool
     var $t15: u8
     var $t16: u8
     var $t17: u8
     var $t18: u8
     var $t19: u8
     var $t20: bool
     var $t21: u64
  0: assume WellFormed($t0)
  1: assume WellFormed($t1)
  2: trace_local[a]($t0)
  3: trace_local[b]($t1)
  4: $t6 := 1
  5: $t4 := $t6
  6: trace_local[x]($t6)
  7: $t7 := 0
  8: $t5 := $t7
  9: trace_local[y]($t7)
 10: $t8 := 0
 11: $t9 := !=($t0, $t8)
 12: if ($t9) goto 13 else goto 27
 13: label L0
 14: $t10 := 3
 15: $t11 := +($t10, $t6) on_abort goto 44 with $t12
 16: $t5 := $t11
 17: trace_local[y]($t11)
 18: $t13 := 0
 19: $t14 := ==($t1, $t13)
 20: if ($t14) goto 21 else goto 27
 21: label L3
 22: $t15 := 2
 23: $t16 := +($t0, $t1) on_abort goto 44 with $t12
 24: $t17 := *($t15, $t16) on_abort goto 44 with $t12
 25: $t4 := $t17
 26: trace_local[x]($t17)
 27: label L2
 28: $t18 := -($t4, $t5) on_abort goto 44 with $t12
 29: $t19 := 0
 30: $t20 := !=($t18, $t19)
 31: $t21 := 42
 32: trace_local[tmp#$3]($t21)
 33: trace_local[tmp#$2]($t20)
 34: if ($t20) goto 35 else goto 37
 35: label L5
 36: goto 41
 37: label L7
 38: trace_abort($t21)
 39: $t12 := move($t21)
 40: goto 44
 41: label L8
 42: label L9
 43: return ()
 44: label L10
 45: abort($t12)
}

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