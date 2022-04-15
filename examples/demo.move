address 0x2 {
  module foo {
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
  }
}