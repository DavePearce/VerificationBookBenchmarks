type uint is (int u) where u >= 0

function findCutPoints(int[] s) -> (int rl):
    uint x = 0
    uint n = 0
    //
    while (x+1) < |s|:
        uint y = advance(s,x)
        // mark cut point
        x = y
    //
    return n

function advance(int[] s, uint i) -> (uint r)
requires (i+1) < |s|
ensures (i+1) <= r:
    uint j = i + 1
    bool increasing = (s[i] < s[j])
    //
    while j < |s| && (s[j-1] < s[j]) == increasing
    where j >= (i+1):
        j = j + 1
    //
    return j
