/*
  Example Whiley solution to problem 1 of the VerifyThis 2019 competition.

  Verified implementation of an algorithm that computes the
  maximal monotonic cutpoints of an array of integers.

  Based on the Dafny solution by Carlo A. Furia:
  See: https://www.pm.inf.ethz.ch/research/verifythis/Archive/2019.html

  Translated and adapted into Whiley by Liam Kent, March 2021, UQ.
  Verified with Boogie 2.8.1 and Z3 4.8.10 (may take 5-6 minutes).

  Note that the sequences of Dafny were translated into fixed size arrays in Whiley,
  plus the 'insert' function below that appends an element to an array.
*/

type uint is (int u) where u >= 0

function insert(int[] array, int x) -> (int[] out)
ensures |out| == |array| + 1 && all {i in 0..|array| | array[i] == out[i]} && out[|array|] == x:
    int[] output = [x; |array| + 1]
    for i in 0..|array|
    where |output| == |array| + 1 && output[|array|] == x && all {j in 0..i | array[j] == output[j]}:
        output[i] = array[i]
    return output   

property ordered(int[] s, int a, int b)
where all {j in a..b, k in a..b | j < k ==> s[j] <= s[k]}

property increasing(int[] s, int a, int b)
where all {j in a..b, k in a..b | j < k ==> s[j] < s[k]}

property decreasing(int[] s, int a, int b)
where all {j in a..b, k in a..b | j < k ==> s[j] >= s[k]}

property monotonic(int[] s, int a, int b)
where increasing(s,a,b) || decreasing(s,a,b)

property monotonic_cuts(int[] s, int[] c, int b)
where increasing(c, 0, |c|) && |c| > 0 &&
    all {k in 0..|c| | 0 <= c[k] && c[k] <= b} &&
    c[0] == 0 && c[|c|-1] == b &&
    all {k in 1..|c| | |s| >= 1 && c[k] <= |s| ==> monotonic(s, c[k-1], c[k])}

property maximal_cuts(int[] s, int[] c, int b)
where monotonic_cuts(s, c, b) &&
    all {k in 1..(|c|-1) | |s| >= 1 && c[k]+1 <= |s| ==> !monotonic(s, c[k-1], c[k]+1)}

function findCutPoints(int[] s) -> (int[] c)
ensures maximal_cuts(s, c, |s|):
    int[] cut = [0]
    uint x = 0
    uint y = 1
    int p = 0 // ghost
    while y < |s|
    where 0 <= x && x < y && y <= |s| + 1
    where y == x + 1
    where 0 <= p && p <= x
    where monotonic_cuts(s, cut, x)
    where all {k in 1..(|cut|-1) | |s| >= 1 && cut[k] + 1 <= |s| ==> !monotonic(s, cut[k-1], cut[k]+1)}
    where 0 < x && x + 1 <= |s| ==> !monotonic(s, p, x+1)
    where |cut| > 0 && cut[0] == 0
    where |cut| > 1 ==> cut[|cut|-2] == p:
        bool increase = (s[x] < s[y])

        while y < |s| && (s[y-1] < s[y] <==> increase)
        where 0 <= x && x < y && y <= |s|
        where monotonic_cuts(s, cut, x)
        where monotonic(s, x, y)
        where monotonic_cuts(s, insert(cut, y), y)
        where increase ==> increasing(s, x, y)
        where !increase ==> decreasing(s, x, y):
            y = y + 1
        assume monotonic(s, x, y)
        assume y < |s| ==> !monotonic(s, x, y+1)  
        cut = insert(cut, y)
        p = x
        x = y
        y = x + 1
    if x < |s|:
        cut = insert(cut, |s|)
    return cut
