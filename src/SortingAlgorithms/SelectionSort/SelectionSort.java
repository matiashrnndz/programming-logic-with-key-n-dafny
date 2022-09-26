public class SelectionSort {

  /*@ public normal_behavior
    @  requires arr.length > 0;
    @  ensures (\forall  int a, b;
    @                    0 <= a && a <= b && b < arr.length;
    @                    arr[a] <= arr[b]);
    @  ensures \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
    @*/
  public void selectionSort(int[] arr) {
    int N = arr.length;
    int i = 0;

    /*@  loop_invariant 0 <= i && i < N;
      @  loop_invariant (\forall int a, b;
      @                          0 <= a && a < i && i <= b && b < N;
      @                          arr[a] <= arr[b]);
      @  loop_invariant (\forall int a, b;
      @                          0 <= a && a <= b && b <= i;
      @                          arr[a] <= arr[b]);
      @  loop_invariant \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
      @  decreases N - 1 - i;
      @  assignable arr[*];
      @*/
    while(i != N - 1) {
      int j = i + 1;
      int min = i;
      
      /*@  loop_invariant i < j && j <= N;
        @  loop_invariant i <= min && min < N;
        @  loop_invariant (\forall int k;
        @                          i <= k && k < j;
        @                          arr[min] <= arr[k]);
        @  loop_invariant \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
        @  decreases N - j;
        @  assignable \strictly_nothing;
        @*/
      while(j != N) {
        if (arr[j] < arr[min]) {
          min = j;
        }
        j = j + 1;
      }
      int temp = arr[min];
      arr[min] = arr[i];
      arr[i] = temp;
      
      i = i + 1;
    }
  }
}
