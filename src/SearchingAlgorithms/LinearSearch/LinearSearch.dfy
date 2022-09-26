method LinearSearch (arr: array<int>, key: int) returns (i: int)
  ensures 0 <= i < arr.Length ==> arr[i] == key
  ensures i == -1 ==> key !in arr[..]
{
  i := 0;

  while (i != arr.Length && arr[i] != key)
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> arr[k] != key
    decreases arr.Length - i
  {
    i := i + 1;
  }

  if (i == arr.Length) {
    i := -1;
  }
}
