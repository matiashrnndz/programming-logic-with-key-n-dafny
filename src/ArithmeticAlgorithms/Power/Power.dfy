method Power(base: int, exp: nat) returns (result: int)
  ensures result == Pow(base, exp)
{
  var e := exp;
  result := 1;

  while(e != 0)
    invariant e >= 0
    invariant result * Pow(base, e) == Pow(base, exp)
    decreases e
  {
    result := result * base;
    e := e - 1;
  }
}

function Pow(base: int, exp: nat):int
{
	if (exp == 0) then 1
  else base * Pow(base, exp-1)
}
