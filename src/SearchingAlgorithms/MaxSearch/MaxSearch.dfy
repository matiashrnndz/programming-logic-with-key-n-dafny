method MaxSearch(arr: array<int>) returns (result: int)
  requires arr.Length > 0
  ensures 0 <= result < arr.Length
  ensures forall k :: 0 <= k < arr.Length ==> arr[result] >= arr[k]
{
  var N: nat := arr.Length;
  result := 0;
  var i: nat := 0;

  while (i != N)
    invariant 0 <= i <= N
    invariant 0 <= result < N
    invariant forall k :: 0 <= k < i ==> arr[result] >= arr[k]
    decreases N - i;
  {
    if (arr[i] > arr[result])
    {
      result := i;
    }
    i := i + 1;
  }
}
