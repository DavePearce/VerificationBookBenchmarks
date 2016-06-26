import whiley.lang.Array

type Sorted is (int[] items) where all { i in 0..|items|, j in 0..|items| | i < j ==> items[i] <= items[j] }

function insert(int a, Sorted xs) -> (Sorted ys)
ensures |ys| == |xs| + 1
ensures some { i in 0..|ys| | ys[i] == a }
ensures some { i in 0..|ys| | all { j in 0..i | xs[j] == ys[j] } }
ensures some { i in 0..|ys| | all { j in i+1..|ys| | xs[j] == ys[j] } }:
    //
    if |xs| == 0:
        return [a]
    else if a <= xs[0]:
        return Array.append(a,xs)
    else:
        int[] tail = Array.slice(xs,1,|xs|)
        return Array.append(xs[0],insert(a,tail))
        