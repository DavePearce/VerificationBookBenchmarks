// computes the sequence of left neighbours from an input sequence s, using -1 to indicate that a position has no left neighbour
function left_neighbors(int[] s) -> (int[] output)
ensures |s| == |output|
ensures all {i in 0..|output| | output[i] < i} // left neighbour of i in s is smaller than i
ensures all {i in 0..|output| | output[i] != -1 ==> s[output[i]] < s[i]} // if i has a left neighbour in s, then the value stored in s at the position of the left neighbour is smaller than s[i]
ensures all {i in 0..|output| | all {j in (output[i]+1)..i | s[j] >= s[i]}}: // there are no values smaller than s[i] between left[i] + 1 and i
    int[] left = [-1; |s|]
    int[] stack = [-1; |s|]
    int height = 0

    for x in 0..|s|
    where |left| == |s|
    where |stack| == |s|
    where 0 <= height && height <= x
    where all {i in 0..x | left[i] < i}
    where all {i in 0..x | left[i] != -1 ==> s[left[i]]< s[i]}
    where all {i in 0..x | all {j in (left[i]+1)..i | s[j] >= s[i]}}
    where all {i in 0..height | 0 <= stack[i] && stack[i] < x}
    where x > 0 ==> height > 0
    where height > 0 ==> stack[height-1] == x-1
    where all {i in 1..height | all {j in (stack[i-1]+1)..stack[i] | s[j] >= s[stack[i]]}}
    where height > 0 ==> all {j in 0..stack[0] | s[j] >= s[stack[0]]}:
        while (height > 0 && s[stack[height - 1]] >= s[x])
        where 0 <= height && height <= x
        where all {i in 0..x | left[i] < i}
        where all {i in 0..height | 0 <= stack[i] && stack[i] < x}
        where all {i in 1..height | all {j in (stack[i-1]+1)..stack[i] | s[j] >= s[stack[i]]}}
        where height > 0 ==> all {j in (stack[height-1]+1)..x | s[j] >= s[x]}
        where height == 0 ==> all {j in 0..x | s[j] >= s[x]}:
            height = height - 1
        
        if height == 0:
            left[x] = -1
        else:
            left[x] = stack[height-1]
        stack[height] = x
        height = height + 1
    return left