function hd(int[] xs) -> (int|null x)
ensures (x is int) ==> xs[0] == x
ensures (x is null) <==> |xs| == 0:
    //
    if |xs| == 0:
        return null
    else:
        return xs[0]