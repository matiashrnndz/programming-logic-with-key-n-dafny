public class IntegerDivision {

  private int q;
  private int r;

  /*@ public normal_behavior
    @  requires D >= 0;
    @  requires d > 0;
    @  ensures 0 <= r < d;
    @  ensures D == d * q + r;
    @*/
  public void integerDivision(int D, int d) {
    r = D;
    q = 0;

    /*@  loop_invariant r >= 0;
      @  loop_invariant D == d * q + r;
      @  decreases r;
      @*/
    while(r >= d) {
      r = r - d;
      q = q + 1;
    }
  }
}
