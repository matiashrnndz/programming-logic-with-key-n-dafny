method CombSort(arr: array<int>)
  requires arr.Length > 1;
  ensures forall k :: 0 <= k < arr.Length - 1 ==> arr[k] <= arr[k + 1]
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  modifies arr
  decreases *
{
  var N: nat := arr.Length;
  var gap: nat := N;
  var sorted: bool := false;

  while(gap != 1 || sorted == false)
    invariant 1 <= gap <= N
    invariant sorted == true ==> forall k: nat :: 0 <= k < N - gap ==> arr[k] <= arr[k + gap]
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    decreases *
  {
    gap := NewGap(gap, N);
    sorted := true;
    var i: int := 0;

    while(i + gap != N)
      invariant 0 <= i < i + gap <= N
      invariant sorted == true ==> forall k: nat :: 0 <= k < i ==> arr[k] <= arr[k + gap]
      invariant multiset(arr[..]) == multiset(old(arr[..]))
      decreases N - (i + gap)
    {
      if (arr[i] > arr[i + gap])
      {
        var temp: int := arr[i];
        arr[i] := arr[i + gap];
        arr[i + gap] := temp;

        sorted := false;
      }
      i := i + 1;
    }
  }
}

method NewGap(prevGap: nat, length: nat) returns (gap: nat)
  requires 1 <= prevGap <= length
  ensures 1 <= gap <= length
  ensures prevGap == 1 ==> gap == prevGap == 1
  ensures prevGap > 1 ==> gap < prevGap
{
  gap := (prevGap * 10) / 13;
  if (gap < 1)
  {
    gap := 1;
  }
}

// decreases if gap > 1 then gap else |inversions(arr[..])|

function inversions (s: seq<int>): set<(nat, nat)>
{
  set i: nat, j :nat | 0 <= i < j < |s| && s[i] > s[j] :: (i, j)
}
