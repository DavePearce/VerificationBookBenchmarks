function linearSearch(int[] A, int x) -> (int r)
// Input array is known to hold x
requires some { j in 0..|A| | A[j] == x }
// Return value identifies x in input array
ensures A[r] == x
// Return value identifies greatest match in input array
ensures all { j in r+1 .. |A| | A[j] != x }:
    //
    int i = |A| - 1
    //
    while A[i] != x
    // i remains within the bounds of A
    where i >= 0 && i < |A|
    // A match remains within the unseen portion of A
    where some { j in 0..i+1 | A[j] == x }
    // No match exists within the seen portion of A
    where all { j in i+1 .. |A| | A[j] != x }:
        i = i - 1
    //
    return i