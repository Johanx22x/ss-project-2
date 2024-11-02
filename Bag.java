/*
 * This assignment is based on Erik Poll's assignment (Radboud University, Nijmegen).
 */

/* OpenJML Exercise: 
   
   This class implements a Bag of integers, using an array.

   Add JML specs to this class, to stop OpenJML from complaining.

   NB there may be errors in the code that you have to fix to stop 
   OpenJML from complaining, as these complaints of OpenJML 
   point to real bugs in the code. But keep changes to the code to
   a minimum of what is strictly needed. 
   Mark any changes you have made in the code with a comment,
   eg to indicate that you replaced <= by <.

   While developing your specs, it may be useful to use the keywords
      assert
   to add additional assertions in source code, to find out what 
   OpenJML can - or cannot - prove at a given program point.
  
*/

//@ nullable_by_default                      // Do not remove this annotation
class Bag {
    /*@ spec_public @*/ int[] contents;
    //@ public invariant n >= 0;
    /*@ spec_public @*/ int n;

    /*@ 
      @ requires input != null;
      @ ensures n == input.length;
      @ ensures contents != null;
      @ ensures contents.length == n;
      @ ensures (\forall int i; 0 <= i && i < n; contents[i] == input[i]);
      @*/
    Bag(int[] input) {
        n = input.length;
        contents = new int[n];
        arraycopy(input, 0, contents, 0, n);
    }

    /*@
      @ ensures n == 0;
      @ ensures contents != null;
      @ ensures contents.length == 0;
      @ ensures contents.length == n;
      @*/
    Bag() {
        n = 0;
        contents = new int[0];
    }

    /*@
      @ requires contents != null;
      @ requires n > 0 && n <= contents.length;
      @*/
    void removeOnce(int elt) {
        /*@
          @ loop_invariant n > 0 && n <= contents.length;
          @ loop_invariant 0 <= i && i <= n;
          @*/
        for (int i = 0; i < n; i++) {  // replaced <= by <
            if (contents[i] == elt ) {
                n--;
                contents[i] = contents[n];
                return;
          }
        }
    }

    /*@
      @ requires contents != null;
      @ requires n > 0 && n <= contents.length;
      @*/
    void removeAll(int elt) {
        /*@
          @ loop_invariant n >= 0 && n <= contents.length;
          @ loop_invariant 0 <= i && i <= n;
          @ loop_invariant (\forall int j; 0 <= j && j < i; contents[j] != elt);
          @ decreases n - i;
          @*/
        for (int i = 0; i < n; i++) {  // replaced <= by <
            if (contents[i] == elt) {
                n--;
                contents[i] = contents[n];
                i--; // Re-check the current index after swapping
            }
        }
    }

    /*@
      @ requires contents != null;
      @ requires n > 0 && n <= contents.length;
      @ ensures \result >= 0 && \result <= n;
      @*/
    int getCount(int elt) {
        int count = 0;
        /*@
          @ loop_invariant 0 <= i && i <= n;
          @ loop_invariant 0 <= count && count <= i;
          @ decreases n - i;
          @*/
        for (int i = 0; i < n; i++) { // replaced <= by <
            if (contents[i] == elt) count++;
        }
        return count;
    }

    /*@
      @ requires contents != null;
      @ requires n >= 0 && n <= contents.length;
      @ requires 0 <= 2*n && 2*n <= Integer.MAX_VALUE;
      @ assignable contents, contents[*], n;
      @ ensures n == \old(n) + 1;
      @ ensures contents != null;
      @ ensures contents.length >= n;
      @ ensures contents[n - 1] == elt;
      @*/
    void add(int elt) {
        if (n == contents.length) {
            int[] new_contents = new int[2 * n + 1];
            arraycopy(contents, 0, new_contents, 0, n);
            contents = new_contents;
        }
        contents[n] = elt;
        n++;
    }

    /*@
      @ requires contents != null;
      @ requires b != null;
      @ requires b.contents != null;
      @ requires n >= 0 && n <= contents.length;
      @ requires b.n >= 0 && b.n <= b.contents.length;
      @ requires 0 <= n + b.n && n + b.n <= Integer.MAX_VALUE;
      @*/
    void add(Bag b) {
        int[] new_contents = new int[n + b.n];

        arraycopy(contents, 0, new_contents, 0, n);
        if (b.contents != new_contents) { // added this line to avoid OpenJML copying the array to itself
            arraycopy(b.contents, 0, new_contents, n, b.n);
        }

        contents = new_contents;
        n += b.n; // added this line to update the size of the bag
    }

   /*@ 
     @ requires a != null;
     @ requires contents != null;
     @ requires n >= 0 && n <= contents.length;
     @ requires 0 <= n + a.length && n + a.length <= Integer.MAX_VALUE;
     @*/
   void add(int[] a) {
       // Modified this method to use arraycopy directly for adding elements.
       // This approach improves the OpenJML static verification process by
       // simplifying the method's logic and reducing the dependency on
       // external method calls (e.g., creating a Bag object). By handling
       // array operations directly within this method, it minimizes potential
       // sources of verification issues, ensuring clearer preconditions,
       // postconditions, and invariants for OpenJML to check.
       int[] new_contents = new int[n + a.length];

       arraycopy(contents, 0, new_contents, 0, n);
       arraycopy(a, 0, new_contents, n, a.length);

       contents = new_contents;
       n += a.length;
   }

    /*@
      @ requires b != null;
      @ requires b.contents != null;
      @ requires b.n >= 0 && b.n <= b.contents.length;
      @ requires b.contents.length >= 0 && b.contents.length <= Integer.MAX_VALUE;
      @ ensures contents != null;
      @ ensures n == b.n;
      @ ensures n >= 0 && n <= contents.length;
      @ ensures (\forall int i; 0 <= i && i < b.n; contents[i] == b.contents[i]);
      @*/
    Bag (Bag b) {
        // Changed the approach, instead of doing this.add(b), we do it
        // manually to ensure that the contents array is initialized
        n = b.n;
        contents = new int[n];
        if (contents != b.contents) { // added this line to avoid OpenJML copying the array to itself
            arraycopy(b.contents, 0, contents, 0, n);
        }
    }

    /*@
      @ requires src != null && dest != null;
      @ requires src != dest;
      @ requires 0 <= length && length <= src.length - srcOff && length <= dest.length - destOff;
      @ requires 0 <= srcOff && srcOff <= src.length;
      @ requires 0 <= destOff && destOff <= dest.length;
      @ ensures (\forall int i; 0 <= i && i < length; dest[destOff + i] == src[srcOff + i]);
      @ assignable dest[destOff..destOff + length - 1];
      @*/
    private static void arraycopy(int[] src,
            int srcOff,
            int[] dest,
            int destOff,
            int length) {
        /*@
          @ loop_invariant 0 <= i && i <= length;
          @ loop_invariant (\forall int k; 0 <= k && k < destOff; dest[k] == \old(dest[k]));
          @ loop_invariant (\forall int k; destOff + i <= k && k < dest.length; dest[k] == \old(dest[k]));
          @ loop_invariant (\forall int k; destOff <= k && k < destOff + i; dest[k] == src[srcOff + k - destOff]);
          @ decreases length - i;
          @*/
        for (int i = 0; i < length; i++) { // replaced <= by <
            dest[destOff + i] = src[srcOff + i];
        }
    }
}
