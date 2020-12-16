// This function finds a duplet in the given array.  It is assumed
// that such a duplet exists.
function findDuplet(int[] A, int start) -> (int r1, int r2)
// Need at least two elements in the subregion
requires start >= 0 && start < |A|
// Some duplet exists in the initial array
requires some { 
    i in start..|A|, j in start..|A| | i != j && A[i] == A[j] 
}
// The indices returned are indeed a duplet
ensures r1 != r2 && A[r1] == A[r2]:
  //
  if start + 1 == |A|:
    // This is the base case where the postcondition follows
    // immediately from the precondition.
    return 0,1
  else:
    // This is the (potentially) recursive case.  The goal here is
    // to check whether A[start] is part of a duplet or not.
    int i = start + 1
    while i < |A|
      where i > start && i <= |A|
      // A[start] doesn't match any subsequent element (thus far)
      where all { k in start+1 .. i | A[start] != A[k] }:
      //
      if A[start] == A[i]:
        return start,i
      i = i + 1
    //
    // Precondition for recursive call follows as we have ruled out 
    // A[start] as being part of a duplet.  Hence, at least one duplet
    // must exist in subregion beginning at start+1.
    return findDuplet(A,start+1)
    