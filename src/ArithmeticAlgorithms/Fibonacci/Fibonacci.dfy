function FibonacciRecursive(n: nat): nat
  decreases n
{
  if (n == 0) then 1 else
  if (n == 1) then 1 else
  FibonacciRecursive(n-2) + FibonacciRecursive(n-1)
}

method FibonacciIterative(n: int) returns (a: int)
  requires n >= 0
  ensures a == FibonacciRecursive(n)
  decreases n
{
  a := 1;
  var b: int := 1;
  var i: int := 0;

  while (i != n)
    invariant 0 <= i <= n
    invariant a == FibonacciRecursive(i)
    invariant b == FibonacciRecursive(i+1)
    decreases n - i
  {
    var olda: int := a;
    a := b;
    b := olda + b;
    i := i + 1;
  }
}
