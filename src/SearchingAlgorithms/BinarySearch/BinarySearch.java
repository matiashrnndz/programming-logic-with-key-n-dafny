public class BinarySearch {
  
  /*@ public normal_behavior
    @ requires (\forall int a, b;
    @                   0 <= a && a <= b && b < arr.length;
    @                   arr[a] <= arr[b]);
    @ ensures (0 <= \result && \result < arr.length ==> arr[\result] == key);
    @ ensures (\result == -1 ==> (\forall int k;
    @                                     0 <= k && k < arr.length;
    @                                     arr[k] != key));
    @*/
  public int binarySearch(int[] arr, int key) {
    int N = arr.length;
    int l = 0;
    int r = N;
    int m = (l + r) / 2;
    
    /*@ loop_invariant 0 <= l && l <= r && r <= N;
      @ loop_invariant m == (l + r) / 2;
      @ loop_invariant (\forall int k;
      @                         0 <= k < l;
      @                         arr[k] != key);
      @ loop_invariant (\forall int k;
      @                         r <= k < N;
      @                         arr[k] != key);
      @ assignable \strictly_nothing;
      @ decreases r - l;
      @*/
    while (l != r && key != arr[m]) {
      if (key < arr[m]) r = m;
      else l = m + 1;
      m = (l + r) / 2;
    }
    return (l == r ? -1 : m);
  }
}
