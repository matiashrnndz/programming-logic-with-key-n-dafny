public class BubbleSort {

  /*@ public normal_behavior
    @  requires arr.length > 0;
    @  ensures (\forall  int a, b;
    @                    0 <= a && a <= b && b < arr.length;
    @                    arr[a] <= arr[b]);
    @  ensures \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
    @  assignable arr[*];
    @*/
  public void bubbleSort(int[] arr) {
    int N = arr.length;
    int i = N - 1;
    
    /*@  loop_invariant 0 <= i && i < N;
      @  loop_invariant (\forall int a, b;
      @                          i <= a && a <= b && b < N;
      @                          arr[a] <= arr[b]);
      @  loop_invariant (\forall int a, b;
      @                          0 <= a && a <= i && i < b && b < N;
      @                          arr[a] <= arr[b]);
      @  loop_invariant \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
      @  assignable arr[*];
      @  decreases i;
      @*/
    while(i != 0) {
      int j = 0;

      /*@  loop_invariant 0 <= j && j <= i;
        @  loop_invariant (\forall int a, b;
        @                          i <= a && a <= b && b < N;
        @                          arr[a] <= arr[b]);
        @  loop_invariant (\forall int a, b;
        @                          0 <= a && a <= i && i < b && b < N;
        @                          arr[a] <= arr[b]);
        @  loop_invariant (\forall int k;
        @                          0 <= k && k <= j;
        @                          arr[k] <= arr[j]);
        @  loop_invariant \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
        @  assignable arr[*];
        @  decreases i-j;
        @*/
      while(j != i) {
        if (arr[j] > arr[j + 1]) {
          int temp = arr[j + 1];
          arr[j + 1] = arr[j];
          arr[j] = temp;
        }
        j = j + 1;
      }
      i = i - 1;
    }
  }
}
