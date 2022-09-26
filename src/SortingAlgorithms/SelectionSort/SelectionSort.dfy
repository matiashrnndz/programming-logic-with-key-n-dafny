method SelectionSort(arr: array<int>)
  requires arr.Length > 0
  ensures forall a, b :: 0 <= a <= b < arr.Length ==> arr[a] <= arr[b]
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  modifies arr
{
  var N: nat := arr.Length;
  var i: nat := 0;

  while(i != N - 1)
    invariant 0 <= i < N
    invariant forall a, b :: 0 <= a < i <= b < N ==> arr[a] <= arr[b]
    invariant forall a, b :: 0 <= a <= b <= i ==> arr[a] <= arr[b]
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    decreases N - 1 - i
    modifies arr
  {
    var j: int := i + 1;
    var min: int := i;

    while(j != N)
      invariant i < j <= N
      invariant i <= min < N
      invariant forall k :: i <= k < j ==> arr[min] <= arr[k]
      invariant multiset(arr[..]) == multiset(old(arr[..]))
      decreases N - j;
      modifies arr
    {
      if (arr[j] < arr[min])
      {
        min := j;
      }
      j := j + 1;
    }
    var temp: int := arr[min];
    arr[min] := arr[i];
    arr[i] := temp;

    i := i + 1;
  }
}
