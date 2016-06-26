import whiley.lang.Array

function isin(int x, int[] ys) -> (bool r)
ensures r <==> some { i in 0..|ys| | ys[i] == x }:
    //
    if |ys| == 0:
        return false
    else if ys[0] == x:
        return true
    else:
        int[] rest = Array.slice(ys,1,|ys|)
        return isin(x,rest)