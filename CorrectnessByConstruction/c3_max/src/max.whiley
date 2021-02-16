function max(int[] xs) -> (int r)
// Need at least one element in array
requires |xs| > 0
// Result valid index into array
ensures r >= 0 && r < |xs|
// Result larger than all elements of array
ensures all { k in 0..|xs| | xs[r] >= xs[k] }
// Result is lowest matching index
ensures all { k in 0..r | xs[k] < xs[r] }:
    //
    int j = 1
    int i = 0
    //
    while j < |xs|
    where j >= 0 && i >= 0 && i <= j
    // All so far below-or-equal to candidate
    where all { l in 0..j | xs[i] >= xs[l] }
    // All upto candidate are below it
    where all { l in 0..i | xs[l] < xs[i] }:
        if xs[i] < xs[j]:
            i = j
        j = j + 1
    //
    return i
