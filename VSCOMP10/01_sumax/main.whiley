import whiley.lang.*

type nat is (int x) where x >= 0

function sumax(int[] items) -> (int sum, int max)
requires |items| > 0
requires all { i in 0 .. |items| | items[i] >= 0 }
ensures sum <= |items| * max:
    //
    int sum = 0 
    int max = 0 
    int i = 0
    //
    while i < |items|
        // 
        where i >= 0 && i <= |items| && sum >= 0 && max >= 0
        // 
        where sum <= i * max:
        //
        sum = sum + items[i]
        if max <= items[i]:
            max = items[i]
        i = i + 1
    //
    return sum,max
