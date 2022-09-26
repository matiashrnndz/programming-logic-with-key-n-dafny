public class InsertionSort {

  /*@ public normal_behavior
    @  requires arr.length > 0;
    @  ensures (\forall int a, b;
    @                   0 <= a && a <= b && b < arr.length;
    @                   arr[a] <= arr[b]);
    @  ensures \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
    @  assignable arr[*];
    @*/
  public void insertionSort(int[] arr) {
    int N = arr.length;
    int i = 1;

    /*@  loop_invariant 1 <= i && i <= N;
      @  loop_invariant (\forall int a, b;
      @                          0 <= a && a <= b && b < N && b < i;
      @                          arr[a] <= arr[b]);
      @  loop_invariant \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
      @  assignable arr[*];
      @  decreases N - i;
      @*/
    while (i != N) {
      int j = i;
      
      /*@  loop_invariant 0 <= j && j <= i;
        @  loop_invariant (\forall int a, b;
        @                          0 <= a && a < b && b <= i && b != j;
        @                          arr[a] <= arr[b]);
        @  loop_invariant \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
        @  assignable arr[*];
        @  decreases j;
        @*/
      while (j != 0 && arr[j - 1] > arr[j]) {
        int temp = arr[j];
        arr[j] = arr[j-1];
        arr[j-1] = temp;

        j = j - 1;
      }
      i = i + 1;
    }
  }
}
