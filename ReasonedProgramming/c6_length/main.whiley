import whiley.lang.Array

function length(int[] xs) -> (int r)
ensures r == |xs|:
    //
    if |xs| == 0:
        return 0
    else:
        int[] rest = Array.slice(xs,1,|xs|)
        return 1 + length(rest)