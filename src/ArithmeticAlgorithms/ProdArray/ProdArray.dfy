method ProdArrayIterative(arr: array<int>) returns (result: int)
  ensures result == ProdArrayRecursive(arr, arr.Length-1)
{
  var N: nat := arr.Length;
  result := 1;
  var i: nat := 0;

  while (i != N)
    invariant 0 <= i <= N
    invariant result == ProdArrayRecursive(arr, i-1);
    decreases arr.Length - i;
  {
    result := result * arr[i];
    i := i + 1;
  }
}

function ProdArrayRecursive (arr: array<int>, to: int): int
  requires -1 <= to < arr.Length
  decreases to
  reads arr
{
  if to == -1 then 1
  else arr[to] * ProdArrayRecursive(arr, to - 1)
}
