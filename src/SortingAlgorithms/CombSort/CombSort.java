public class CombSort {

  /*@ public normal_behavior
    @  requires arr.length > 1;
    @  ensures (\forall int k;
    @                   0 <= k && k < arr.length - 1;
    @                   arr[k] <= arr[k + 1]);
    @  ensures \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
    @  diverges true;
    @  assignable arr[*];
    @*/
  public void combSort(int[] arr) {
    int N = arr.length;
    int gap = N;
    boolean sorted = false;

    /*@  loop_invariant 1 <= gap && gap <= N;
      @  loop_invariant sorted == true ==> (\forall int k;
      @                                             0 <= k && k < N - gap;
      @                                             arr[k] <= arr[k + gap]);
      @  loop_invariant \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
      @  assignable arr[*];
      @  diverges true;
      @*/
    while(gap != 1 || sorted == false) {
      gap = newGap(gap, N);
      sorted = true;
      int i = 0;
      
      /*@  loop_invariant 0 <= i && i < i + gap && i + gap <= N;
        @  loop_invariant sorted == true ==> (\forall int k;
        @                                             0 <= k && k < i;
        @                                             arr[k] <= arr[k + gap]);
        @  loop_invariant \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
        @  decreases N - (i + gap);
        @  assignable arr[*];
        @*/
      while(i + gap != N) {
        if (arr[i] > arr[i + gap]) {
          int temp = arr[i];
          arr[i] = arr[i + gap];
          arr[i + gap] = temp;

          sorted = false;
        }
        i = i + 1;
      }
    }
  }

  /*@ public normal_behavior
    @  requires 1 <= prevGap && prevGap <= length;
    @  ensures 1 <= \result && \result <= length;
    @  ensures prevGap == 1 ==> \result == prevGap && prevGap == 1;
    @  ensures prevGap > 1 ==> \result < prevGap;
    @*/
  private int newGap(int prevGap, int length) {
    int gap = (prevGap * 10) / 13;
    if (gap < 1) {
      gap = 1;
    }
    return gap;
  }
}
