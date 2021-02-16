type sorted is (int[] items)
where all { i in 1..|items| | items[i-1] <= items[i] }

function binarySearch(sorted A, int x) -> (int r)
// Index returned is either value or -1
ensures r >= -1 && r < |A|
// If negative return, no matching item
ensures (r == -1) ==> all { i in 0..|A| | A[i] != r }:
    //
    int l = 0
    int h = |A|
    //
    while h > (l+1)
    where l <= h && 0 <= l && h <= |A|:
        int pivot = (l+h) / 2
        if x < A[pivot]:
            h = pivot
        else if x == A[pivot]:
            return pivot
        else:
            l = pivot
    //
    return -1
        
