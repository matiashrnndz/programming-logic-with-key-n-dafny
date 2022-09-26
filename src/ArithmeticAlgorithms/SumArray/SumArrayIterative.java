public class SumArrayIterative {

  /*@ public normal_behavior
    @  requires arr != null;
    @  ensures \result == (\sum int k;
    @                           0 <= k && k < arr.length;
    @                           arr[k]);
    @  assignable \nothing;
    @*/
  public int sumArrayIterative(int[] arr) {
    int N = arr.length;
    int result = 0;
    int i = 0;
    
    /*@  loop_invariant 0 <= i && i <= N;
      @  loop_invariant result == (\sum int k;
      @                              0 <= k && k < i;
      @                              arr[k]);
      @  assignable \nothing;
      @  decreases N - i;
      @*/
    while (i != N) {
      result = result + arr[i];
      i = i + 1;
    }
    return result;
  }
}
