// Determine the maximum of an array using the elimination algorithm,
// originally attributed to Kaldewaij.
function max(int[] A) -> (int r)
// A non-empty array is required
requires |A| > 0
// Element index returned identifies real maximum
ensures all { i in 0..|A| | A[i] <= A[r] }:
  //
  int l = 0
  int u = |A|-1
  while l < u
    where l >= 0 && l <= u && u < |A|
    // All up to lower bound below either lower or upper bound
    where all { k in 0..l | A[k] <= A[l] || A[k] <= A[u] }
    // All from upper bound below either lower or upper bound
    where all { k in u+1..|A| | A[k] <= A[l] || A[k] <= A[u] }:
    //
    if A[l] <= A[u]:
        l = l + 1
    else:
        u = u - 1
  //
  return l
