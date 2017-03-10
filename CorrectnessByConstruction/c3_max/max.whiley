function max(int[] xs) -> (int r)
requires |xs| > 0
//ensures r >= 0 && r < |xs|
ensures all { k in 0..|xs| | xs[r] >= xs[k] }:
    //
    int j = 1
    int i = 0
    //
    while j < |xs| 
    where j >= 0 && i >= 0 && i <= j
    where all { l in 0..j | xs[i] >= xs[l] }:
        if xs[i] < xs[j]:
            i = j
        j = j + 1
    //
    return i