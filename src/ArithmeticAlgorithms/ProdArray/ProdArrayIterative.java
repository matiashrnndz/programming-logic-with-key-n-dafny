public class ProdArrayIterative {

  /*@ public normal_behavior
    @  ensures \result == (\product int k;
    @                               0 <= k && k < arr.length;
    @                               arr[k]);
    @  assignable \nothing;
    @*/
  public int prodArrayIterative(int[] arr) {
    int N = arr.length;
    int result = 1;
    int i = 0;
    
    /*@  loop_invariant 0 <= i && i <= N;
      @  loop_invariant result == (\product int k;
      @                                  0 <= k && k < i;
      @                                  arr[k]);
      @  assignable \nothing;
      @  decreases N - i;
      @*/
    while (i != N) {
      result = result * arr[i];
      i = i + 1;
    }
    return result;
  }
}
