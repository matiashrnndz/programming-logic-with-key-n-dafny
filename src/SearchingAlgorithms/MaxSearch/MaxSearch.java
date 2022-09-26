public class MaxSearch {

  /*@ public normal_behavior
    @  requires arr.length > 0;
    @  ensures 0 <= result < arr.length;
    @  ensures (\forall int k;
    @                 0 <= k < arr.length;
    @                 arr[result] >= arr[k]);
    @  assignable \nothing;
    @*/
  public int maxSearch(int[] arr) {
    int N = arr.length;
    int result = 0;
    int i = 0;
    
    /*@  loop_invariant 0 <= i && i <= N;
      @  loop_invariant 0 <= result && result < N;
      @  loop_invariant (\forall int k;
      @                         0 <= k && k < i;
      @                         arr[result] >= arr[k]);
      @  decreases N - i;
      @  assignable \nothing;
      @*/
    while (i != N) {
      if (arr[i] > arr[result]) {
        result = i;
      }
      i = i + 1;
    }
    return result;
  }
}
