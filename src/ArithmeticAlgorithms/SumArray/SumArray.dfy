method SumArrayIterative(arr: array<int>) returns (result: int)
  ensures result == SumArrayRecursive(arr, arr.Length-1)
{
  var N: nat := arr.Length;
  result := 0;
  var i: nat := 0;

  while (i != N)
    invariant 0 <= i <= N
    invariant result == SumArrayRecursive(arr, i-1);
    decreases N - i;
  {
    result := result + arr[i];
    i := i + 1;
  }
}

function SumArrayRecursive (arr: array<int>, to: int): int
  requires -1 <= to < arr.Length
  decreases to
  reads arr
{
  if to == -1 then 0
  else arr[to] + SumArrayRecursive(arr, to - 1)
}
