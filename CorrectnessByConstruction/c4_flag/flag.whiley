import whiley.lang.System

constant RED is 0
constant WHITE is 1
constant BLUE is 2

type Color is (int n) 
// The dutch national flag has three colours
where n == RED || n == WHITE || n == BLUE 

function partition(Color[] cols) -> (Color[] r)
ensures |r| == |cols|
// resulting array in sorted order
ensures all { k in 1..|r| | r[k] < r[k+1] }:
    //
    int lo = 0
    int mid = 0
    int hi = |cols|
    int[] gcols = cols // ghost

    while mid < hi
    // size of cols does not change
    where |cols| == |gcols|
    // invariants between markers
    where lo >= 0 && lo <= mid && hi <= |cols|:
    // All elements up to lo are below white
    where all { k in 0 .. lo | cols[k] < WHITE }:
    // All elements from hi upwards are above white:
    where all { k in hi .. |cols| | cols[k] > WHITE }:
        //
        if cols[mid] < WHITE:
            int tmp = cols[lo]
            cols[lo] = cols[mid]
            cols[mid] = tmp
            lo = lo + 1
            mid = mid + 1
        else if cols[mid] > WHITE:
            hi = hi - 1
            int tmp = cols[mid]
            cols[mid] = cols[hi]
            cols[hi] = tmp
        else:
            mid = mid + 1
    //
    return cols
