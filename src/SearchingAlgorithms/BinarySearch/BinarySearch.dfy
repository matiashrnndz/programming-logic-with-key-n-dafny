method BinarySearch(arr: array<int>, key: int) returns (m: int) 
  requires forall a, b :: 0 <= a <= b < arr.Length ==> arr[a] <= arr[b]
  ensures 0 <= m < arr.Length ==> arr[m] == key
  ensures m == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != key
{
  var N: nat := arr.Length;
  var l: int := 0;
  var r: int := N;
  m := (l + r) / 2;

  while (l != r && key != arr[m])
    invariant 0 <= l <= r <= N
    invariant m == (l + r) / 2
    invariant forall k :: 0 <= k < l ==> arr[k] != key
    invariant forall k :: r <= k < N ==> arr[k] != key
    decreases r - l
  {
    if (key < arr[m]) {
      r := m;
    } else {
      l := m + 1;
    }
    m := (l + r) / 2;
  }

  if (l == r) {
    m := -1;
  }
}
