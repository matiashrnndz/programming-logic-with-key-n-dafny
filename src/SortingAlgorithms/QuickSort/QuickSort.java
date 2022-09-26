public class QuickSort {

  /*@ public normal_behaviour
    @  requires array.length > 0;
    @  ensures (\forall int a, b;
    @                   0 <= a && a <= b && b < array.length;
    @                   array[a] <= array[b]);
    @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
    @  assignable array[*];
    @*/
  public void quicksortWrapper(int[] array) {
    int N = array.length;
    quicksort(array, 0, N - 1);
  }

  /*@ public normal_behavior
    @  requires 0 <= from && from <= array.length;
    @  requires -1 <= to && to < array.length;
    @  requires from <= to + 1;
    @  requires from > 0 ==> (\forall int i;
    @                                 from <= i && i <= to;
    @                                 array[from - 1] <= array[i]);
    @  requires to < array.length - 1 ==> (\forall int i;
    @                                              from <= i && i <= to;
    @                                              array[i] <= array[to + 1]);
    @  ensures (\forall int a, b;
    @                   from <= a && a <= b && b <= to;
    @                   array[a] <= array[b]);
    @  ensures from > 0 ==> (\forall int i;
    @                                from <= i && i <= to;
    @                                array[from - 1] <= array[i]);
    @  ensures to < array.length - 1 ==> (\forall int i;
    @                                             from <= i && i <= to;
    @                                             array[i] <= array[to + 1]);
    @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
    @  measured_by to - from + 1;
    @  assignable array[from..to];
    @*/
  private static void quicksort(int[] array, int from, int to) {
    if (from < to) {
      int m = partition(array, from, to);
      quicksort(array, from, m - 1);
      quicksort(array, m + 1, to);
    }
  }

  /*@ public normal_behavior
    @  requires 0 <= from && from <= to && to < array.length;
    @  requires from > 0 ==> (\forall int i;
    @                                 from <= i && i <= to;
    @                                 array[from - 1] <= array[i]);
    @  requires to < array.length - 1 ==> (\forall int i;
    @                                              from <= i && i <= to;
    @                                              array[i] <= array[to + 1]);
    @  ensures from <= \result && \result <= to;
    @  ensures (\forall int k;
    @                   from <= k && k < \result;
    @                   array[k] < array[\result]);
    @  ensures (\forall int k;
    @                   \result < k && k <= to;
    @                   array[k] >= array[\result]);
    @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
    @  ensures (\forall int k;
    @                   0 <= k && k < from;
    @                   array[k] == \old(array[k]));
    @  ensures (\forall int k;
    @                   to < k && k < array.length;
    @                   array[k] == \old(array[k]));
    @  ensures from > 0 ==> (\forall int i;
    @                                from <= i && i <= to;
    @                                array[from - 1] <= array[i]);
    @  ensures to < array.length - 1 ==> (\forall int i;
    @                                             from <= i && i <= to;
    @                                             array[i] <= array[to + 1]);
    @  assignable array[from..to];
    @*/
  private static int partition(int[] array, int from, int to) {

    int l = from;
    int r = to;
    int pivot = array[from];

    /*@  loop_invariant from <= l && l <= r && r <= to;
      @  loop_invariant pivot == array[l];
      @  loop_invariant (\forall int k;
      @                          from <= k && k < l;
      @                          array[k] < pivot);
      @  loop_invariant (\forall int k;
      @                          r < k && k <= to;
      @                          array[k] >= pivot);
      @  loop_invariant \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
      @  loop_invariant (\forall int k;
      @                          0 <= k && k < from;
      @                          array[k] == \old(array[k]));
      @  loop_invariant (\forall int k;
      @                          to < k && k < array.length;
      @                          array[k] == \old(array[k]));
      @  loop_invariant from > 0 ==> (\forall int i;
      @                                       from <= i && i <= to;
      @                                       array[from - 1] <= array[i]);
      @  loop_invariant to < array.length - 1 ==> (\forall int i;
      @                                                    from <= i && i <= to;
      @                                                    array[i] <= array[to + 1]);
      @  assignable array[from..to];
      @  decreases r - l;
      @*/
    while (l != r) {
      if (pivot <= array[r]) {
        r = r - 1;
        
      } else {
        array[l] = array[r];
        array[r] = array[l + 1];

        array[l + 1] = pivot;
        l = l + 1;
      }
    }
    return l;
  }
}
