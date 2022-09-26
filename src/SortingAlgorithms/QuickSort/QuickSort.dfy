method QuicksortWrapper(arr: array<int>)
  requires arr.Length > 0
  ensures forall a, b :: 0 <= a <= b < arr.Length ==> arr[a] <= arr[b]
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  modifies arr
{
  var N: nat := arr.Length;
  Quicksort(arr, 0, N - 1);
}

method Quicksort(arr: array<int>, from: int, to: int)
  requires 0 <= from <= arr.Length
  requires -1 <= to < arr.Length
  requires from <= to + 1
  requires from > 0 ==> forall i :: from <= i <= to ==> arr[from - 1] <= arr[i]
  requires to < arr.Length - 1 ==> forall i :: from <= i <= to ==> arr[i] <= arr[to + 1]
  ensures forall a, b :: from <= a <= b <= to ==> arr[a] <= arr[b]
  ensures from > 0 ==> forall i :: from <= i <= to ==> arr[from - 1] <= arr[i]
  ensures to < arr.Length - 1 ==> forall i :: from <= i <= to ==> arr[i] <= arr[to + 1]
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  ensures forall k :: 0 <= k < from ==> arr[k] == old(arr[k])
  ensures forall k :: to < k < arr.Length ==> arr[k] == old(arr[k])
  decreases to - from
  modifies arr
{
  if (from < to)
  {
    var m: int := Partition(arr, from, to);
    Quicksort(arr, from, m - 1);
    Quicksort(arr, m + 1, to);
  }
}

method Partition(arr: array<int>, from: int, to: int) returns (l: int)
  requires 0 <= from <= to < arr.Length
  requires from > 0 ==> forall i :: from <= i <= to ==> arr[from - 1] <= arr[i]
  requires to < arr.Length - 1 ==> forall i :: from <= i <= to ==> arr[i] <= arr[to + 1]
  ensures from <= l <= to
  ensures forall k :: from <= k < l ==> arr[k] < arr[l]
  ensures forall k :: l < k <= to ==> arr[k] >= arr[l]
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  ensures forall k :: 0 <= k < from ==> arr[k] == old(arr[k])
  ensures forall k :: to < k < arr.Length ==> arr[k] == old(arr[k])
  ensures from > 0 ==> forall i :: from <= i <= to ==> arr[from - 1] <= arr[i]
  ensures to < arr.Length - 1 ==> forall i :: from <= i <= to ==> arr[i] <= arr[to + 1]
  modifies arr
{
  l := from;
  var r: int := to;
  var pivot: int := arr[from];

  while (l != r)
    invariant from <= l <= r <= to
    invariant pivot == arr[l]
    invariant forall k :: from <= k < l ==> arr[k] < pivot
    invariant forall k :: r < k <= to ==> arr[k] >= pivot
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    invariant forall k :: 0 <= k < from ==> arr[k] == old(arr[k])
    invariant forall k :: to < k < arr.Length ==> arr[k] == old(arr[k])
    invariant from > 0 ==> forall i :: from <= i <= to ==> arr[from - 1] <= arr[i]
    invariant to < arr.Length - 1 ==> forall i :: from <= i <= to ==> arr[i] <= arr[to + 1]
    decreases r - l
    modifies arr
  {
    if (pivot <= arr[r])
    {
      r := r - 1;
    } 
    else
    {
      arr[l] := arr[r];
      arr[r] := arr[l + 1];

      arr[l + 1] := pivot;
      l := l + 1;
    }
  }
}
