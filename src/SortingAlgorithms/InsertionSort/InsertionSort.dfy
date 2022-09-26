method InsertionSort(arr: array<int>)
  requires arr.Length > 0;
  ensures forall a, b :: 0 <= a <= b < arr.Length ==> arr[a] <= arr[b]
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  modifies arr
{
  var N: nat := arr.Length;
  var i: nat := 1;

  while (i != N)
    invariant 1 <= i <= N;
    invariant forall a, b :: 0 <= a <= b < N && b < i ==> arr[a] <= arr[b]
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    decreases N - i;
    modifies arr;
  {
    var j: nat := i;

    while (j != 0 && arr[j - 1] > arr[j])
      invariant 0 <= j <= i;
      invariant forall a, b :: 0 <= a < b <= i && b != j ==> arr[a] <= arr[b]
      invariant multiset(arr[..]) == multiset(old(arr[..]))
      decreases j;
      modifies arr;
    {
      var temp: int := arr[j];
      arr[j] := arr[j-1];
      arr[j-1] := temp;
      
      j := j - 1;
    }
    i := i + 1;
  }
}
