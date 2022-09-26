method BubbleSort(arr: array<int>)
  requires arr.Length > 0;
  ensures forall a, b :: 0 <= a <= b < arr.Length ==> arr[a] <= arr[b]
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  modifies arr;
{
  var N: nat := arr.Length;
  var i: nat := N - 1;

  while(i != 0)
    invariant 0 <= i < N
    invariant forall a, b :: i <= a <= b < N ==> arr[a] <= arr[b]
    invariant forall a, b :: 0 <= a <= i < b < N ==> arr[a] <= arr[b]
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    decreases i;
    modifies arr;
  {
    var j: int := 0;

    while(j != i)
      invariant 0 <= j <= i;
      invariant forall a, b :: i <= a <= b < N ==> arr[a] <= arr[b]
      invariant forall a, b :: 0 <= a <= i < b < N ==> arr[a] <= arr[b]
      invariant forall k :: 0 <= k <= j ==> arr[k] <= arr[j]
      invariant multiset(arr[..]) == multiset(old(arr[..]))
      decreases i - j;
      modifies arr;
    {
      if (arr[j] > arr[j + 1]) {
        var temp: int := arr[j + 1];
        arr[j + 1] := arr[j];
        arr[j] := temp;
      }
      j := j + 1;
    }
    i := i - 1;
  }
}
