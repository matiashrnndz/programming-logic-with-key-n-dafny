method IntegerDivision (D: int, d: int) returns (q: int, r: int)
  requires D >= 0
  requires d > 0
  ensures 0 <= r < d
  ensures D == d * q + r
{
  r := D;
  q := 0;

  while (r >= d)
    invariant r >= 0
    invariant D == d * q + r
    decreases r
  {
    r := r - d;
    q := q + 1;
  }
}
