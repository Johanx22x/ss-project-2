/*
 * This assignment is based on Erik Poll's assignment (Radboud University, Nijmegen).
 */

/* OpenJML exercise

   Objects of this class represent euro amounts. For example, an Amount 
   object with
   euros == 1
   cents == 55
   represents 1.55 euro. 

   Specify the class with JML and check it OpenJML.  

   NB there may be errors in the code that you have to fix to stop 
   OpenJML from complaining, as these complaints of OpenJML 
   point to real bugs in the code. But keep changes to the code to
   a minimum of what is strictly needed. 
   Mark any changes you have made in the code with a comment,
   eg to indicate that you replaced <= by <.

   You should add enough annotations to stop OpenJML complaining,
   but you should ALSO specify invariants discussed below:

   1) We do not want to represent 1.55 euro as an object with
   euro  == 0
   cents == 155
   (Note that the "equals" method will not be correct if we allow 
   this.)
   Specify an invariant that rules this out.

   2) We do not want to represent 1.55 euro as an object with
   euros =  2
   cents =  -45
   Specify one (or more) invariant(s) that rule this out. But note that
   we DO want to allow negative amounts, otherwise the method negate 
   can't be allowed.
   It may be useful to use the JML notation ==> (for implication) in 
   your invariants.

   While developing your specs, it may be useful to use the keywords
   assert
   to add additional assertions in source code, to find out what 
   OpenJML can - or cannot - prove at a given program point.

*/
//@ nullable_by_default                      // Do not remove this annotation
public class Amount {

    private /*@ spec_public @*/ int euros;
    private /*@ spec_public @*/ int cents;

    /*@ requires euros >= Integer.MIN_VALUE && euros <= Integer.MAX_VALUE;
      @ requires cents >= -99 && cents <= 99;
      @ requires (euros > 0 ==> cents >= 0) && (euros < 0 ==> cents <= 0);
      @
      @ ensures this.euros == euros;
      @ ensures this.cents == cents;
      @*/
    public Amount(int euros, int cents) {
        this.euros = euros;
        this.cents = cents;
    }

    /*@ requires euros >= Integer.MIN_VALUE && euros <= Integer.MAX_VALUE;
      @ requires cents >= -99 && cents <= 99;
      @ requires (euros > 0 ==> cents >= 0) && (euros < 0 ==> cents <= 0);
      @
      @ ensures \result != null;
      @ ensures \result.euros >= Integer.MIN_VALUE && \result.euros <= Integer.MAX_VALUE;
      @ ensures \result.cents >= -99 && \result.cents <= 99;
      @ ensures (\result.euros > 0 ==> \result.cents >= 0) && (\result.euros < 0 ==> \result.cents <= 0);
      @*/
    public Amount negate() {
        // Check for Integer.MIN_VALUE to prevent overflow when negating
        if (euros == Integer.MIN_VALUE || cents == Integer.MIN_VALUE) {
            throw new ArithmeticException("Cannot negate Integer.MIN_VALUE");
        }
        return new Amount(-euros, -cents); // replaced (-cents, -euros) by (-euros, -cents)
    }

    /*@ requires a != null;
      @ requires a.euros >= Integer.MIN_VALUE && a.euros <= Integer.MAX_VALUE;
      @ requires a.cents >= -99 && a.cents <= 99;
      @ requires (a.euros > 0 ==> a.cents >= 0) && (a.euros < 0 ==> a.cents <= 0);
      @
      @ requires euros >= Integer.MIN_VALUE && euros <= Integer.MAX_VALUE;
      @ requires cents >= -99 && cents <= 99;
      @ requires (euros > 0 ==> cents >= 0) && (euros < 0 ==> cents <= 0);
      @
      @ ensures \result != null;
      @ ensures \result.euros >= Integer.MIN_VALUE && \result.euros <= Integer.MAX_VALUE;
      @ ensures \result.cents >= -99 && \result.cents <= 99;
      @ ensures (\result.euros > 0 ==> \result.cents >= 0) && (\result.euros < 0 ==> \result.cents <= 0);
      @*/
    public Amount subtract(Amount a) {
        // There's a bug if in the original code when using OpenJML to check the code.
        // After we call negate() the values of euros and cents are changed.
        // To fix this, we store the original values of euros and cents.
        int euros = this.euros;
        int cents = this.cents;
        
        Amount negated = a.negate();

        this.euros = euros;
        this.cents = cents;

        return this.add(negated);
    }

    /*@ requires a != null;
      @ requires euros >= Integer.MIN_VALUE && euros <= Integer.MAX_VALUE;
      @ requires cents >= -99 && cents <= 99;
      @ requires (euros > 0 ==> cents >= 0) && (euros < 0 ==> cents <= 0);
      @ requires a.euros >= Integer.MIN_VALUE && a.euros <= Integer.MAX_VALUE;
      @ requires a.cents >= -99 && a.cents <= 99;
      @ requires (a.euros > 0 ==> a.cents >= 0) && (a.euros < 0 ==> a.cents <= 0);
      @
      @ ensures \result != null;
      @ ensures \result.euros >= Integer.MIN_VALUE && \result.euros <= Integer.MAX_VALUE;
      @ ensures \result.cents >= -99 && \result.cents <= 99;
      @ ensures (\result.euros > 0 ==> \result.cents >= 0) && (\result.euros < 0 ==> \result.cents <= 0);
      @*/
    public Amount add(Amount a) {
        // Check for overflow and underflow before adding euros
        if ((a.euros > 0 && euros > Integer.MAX_VALUE - a.euros) ||
                (a.euros < 0 && euros < Integer.MIN_VALUE - a.euros)) {
            throw new ArithmeticException("Overflow or underflow in euros addition");
                }

        int new_euros = euros + a.euros;
        int new_cents = cents + a.cents;

        if (new_cents < -99) { // replaced -100 by -99
            new_cents = new_cents + 100;
            // Check for underflow before subtracting 1 from euros
            if (new_euros == Integer.MIN_VALUE) {
                throw new ArithmeticException("Underflow in euros");
            }
            new_euros = new_euros - 1;
        }
        if (new_cents > 99) { // replaced 100 by 99
            new_cents = new_cents - 100;
            // Check for overflow before adding 1 to euros
            if (new_euros == Integer.MAX_VALUE) {
                throw new ArithmeticException("Overflow in euros");
            }
            new_euros = new_euros + 1; // replaced -1 by +1
        } 

        // Ensure the cents have the correct sign relative to euros
        if (new_cents < 0 && new_euros > 0) {
            new_cents = new_cents + 100;
            new_euros = new_euros - 1;
        }
        if (new_cents > 0 && new_euros < 0) {
            new_cents = new_cents - 100;
            new_euros = new_euros + 1;
        }

        return new Amount(new_euros, new_cents);
    }


    /*@ requires a != null;
      @ ensures \result == (euros == a.euros && cents == a.cents);
      @*/
    public boolean equal(Amount a) {
        if (a == null) return false;
        return (euros == a.euros && cents == a.cents);
    }
}

