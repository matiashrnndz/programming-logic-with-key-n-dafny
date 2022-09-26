method IsUnique(s: array<char>) returns (b: bool)
  ensures b <==> forall a, b :: 0 <= a < s.Length
                             && 0 <= b < s.Length
                             && a != b ==> s[a] != s[b]
{
  var N: nat := s.Length;
  b := true;
  var i: nat := 0;

  while (b && i != N)
    invariant 0 <= i <= N;
    invariant b <==> forall a, b :: 0 <= a < i
                                 && 0 <= b < i
                                 && a != b ==> s[a] != s[b]
    decreases N - i;
  {
    var j: nat := 0;

    while (j != i && s[j] != s[i])
      invariant 0 <= j <= i;
      invariant forall k :: 0 <= k < j ==> s[k] != s[i]
      decreases i - j;
    {
      j := j + 1;
    }
    b := j == i;
    i := i + 1;
  }
}
