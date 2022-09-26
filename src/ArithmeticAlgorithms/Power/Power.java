public class Power {

  /*@ model_behavior
    @  requires exp >= 0;
    @  model int pow(int base, int exp) {
    @    return (exp == 0) ? 1 : base * pow(base, exp-1);
    @  }
    @*/

  /*@ public normal_behavior
    @  requires exp >= 0;
    @  ensures \result == pow(base, exp);
    @*/
  public int power(int base, int exp) {

    int e = exp;
    int result = 1;

    /*@  loop_invariant e >= 0;
      @  loop_invariant result * pow(base, e) == pow(base, exp);
      @  decreases e;
      @*/
    while(e > 0) {
      result = result * base;
      e = e - 1;
    }

    return result;
  }
}
