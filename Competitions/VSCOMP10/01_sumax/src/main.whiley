type nat is (int x) where x >= 0

function sumax(int[] items) -> (int sum, int max)
requires |items| > 0
requires all { i in 0 .. |items| | items[i] >= 0 }
ensures sum <= |items| * max:
    //
    int s = 0 
    int m = 0 
    int i = 0
    //
    while i < |items|
        // 
        where i >= 0 && i <= |items| && s >= 0 && m >= 0
        // 
        where s <= i * m:
        //
        s = s + items[i]
        if m <= items[i]:
            m = items[i]
        i = i + 1
    //
    return s,m
