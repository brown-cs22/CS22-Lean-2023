import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs

/-

# First order logic in Lean

We were a little vague in class about what function symbols, predicate symbols,
etc. we were going to allow in our formulas. 
In Lean, we need to be more precise.

Symbols in Lean must have *types*: 
a predicate holds on `ℕ`, or on `ℤ`, or on some arbitrary type `T`,
but not on all at once.

We can introduce a new predicate symbol that takes one natural number argument
as follows:

-/

variable (P : ℕ → Prop)

#check P 3

/- 

Notice that we don't need to write parentheses around the argument.
We can, though:

-/

#check P (3)

/- 

If we want a predicate symbol that takes two arguments:

-/

variable (R : ℕ → ℕ → Prop)

#check R 3 4

-- this doesn't work!
-- #check R (3, 4)

/- 

Finally, Lean has lots of predicates and function symbols built in. 
Want to use `+`, `*`, `=`, all that familiar stuff? It's here already.

-/


/- 

## Universal introduction


We said that to prove `∀ x : T, ...` goals, we got to introduce a new 
`x : T`. The tactic for this proof rule is familiar. The pattern here
sounds a lot like implication: move something from the goal to the context.

We use the tactic `intro` again!

The `reflexivity` tactic will prove things equal to themselves.
This is a very basic property of `=`.

-/

example : ∀ x : ℤ, x = x := by 
  intro x
  reflexivity


 -- Every even integer greater than two is the sum of two primes.
example : ∀ n : ℕ, Even n ∧ (n > 2) → ∃p q : ℕ, Prime p ∧ Prime q ∧ (n = p + q) := by
  intro n 
  intro h_and 
  sorry 


/-

## Universal elimination

If we know `hall : ∀ x : T, H x`, we can conclude `H t` for any `t : T`. 
We again do this just like implication elimination: 
`have ht : H t := hall t`.

We can also use `apply`.


Note: I've started this example with the hypothesis `hxp` "pre-intro'ed."
Putting it left of the `:` means it is in my context at the beginning. 
This saves us a line.

-/

example (hxp : ∀ x : ℕ, P x) : P 5 ∧ P 6 := by 
  split_goal 

  -- method 1: using `have`
  { have hP5 : P 5 := hxp 5 
    assumption }
  
  -- method 2: using apply
  { apply hxp }



/- 

## Existential introduction 

To prove an `exists` goal, we provide a witness.
The tactic for giving a witness is `existsi` (for "exists introduction," creatively).

The tactic `numbers` proves silly obvious facts about explicit numbers. 
(It doesn't know anything about variables, like `x`.)

-/

example : ∃ x : ℕ, x > 10 := by 
  existsi 1000 
  numbers


/-

## Existential elimination 

This will be familiar again! 
To use an `exists` hypothesis, we can use the good old `eliminate` tactic 
to get a witness and a hypothesis about that witness.

-/

example (hex : ∃ x : ℕ, P x) : 0 = 0 := by 
  eliminate hex with k hPk
  numbers  

example (hex : ∃ x : ℕ, P x) (hall : ∀ x : ℕ, P x → P (x + 1)) : 
    ∃ x : ℕ, P x ∧ P (x + 1) := by 
  eliminate hex with k hPk
  have hk : P k → P (k + 1) := hall k 
  have hPk1 : P (k + 1) := hk hPk 
  existsi k 
  split_goal 
  { assumption }
  { assumption }
