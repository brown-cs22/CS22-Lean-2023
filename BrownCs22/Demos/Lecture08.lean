import BrownCs22.Library.Tactics

variable (U : Type)

/-

# Sets in Lean

Today we'll talk about sets in Lean!

Remember that, when we take the *complement* of a set `A`,
we have to do this relative to some "universe" of objects. 
Otherwise, the set of things not in `A` would be gigantic. 

Lean enforces this even more strongly. Every set must be 
relative to some universe. `A : set ℕ` means that 
"`A` is a set of natural numbers," i.e., the universe is `ℕ`. 
Similarly, `A : set U` means that the elements of `A` come 
from some generic kind of objects that we call `U`. 


## The set-element method 

To prove that two sets are equal, one technique we saw was 
to transform the equality into a universal statement about
membership : `A = B` means `∀ x : U, x ∈ A ↔ x ∈ B`.
The tactic for doing this is called `ext`, for "extensionality."
You give it a name for the variable `x`. 

## Some new useful tactics 

* `ext x`: if your goal is to show that two sets `A` and `B` 
  are equal, `ext x` changes the goal to showing that 
  `x ∈ A ↔ x ∈ B`. Remember, `split_goal` will then turn an `↔` 
  statement into two implications!

* `set_simplify`: this one is fun! If you have any "set membership"
  statements, like `x ∈ Aᶜ`, in your hypothesis or goals,
  `set_simplify` will turn these statements into "logic."
  For example, `x ∈ Aᶜ` will become `¬ (x ∈ A)`.
  `x ∈ A ∩ B` will become `x ∈ A ∧ x ∈ B`.

* `rewrite`: stands for "rewrite." `rewrite` will let us substitute patterns
  in place of equivalent or equal patterns. A good example here is
  De Morgan's laws, which are logical equivalences. If we are 
  ever looking to prove a goal of the form `¬ (p ∧ q)`, 
  `rewrite [not_and_or]` will use De Morgan's law to change the goal to 
  `¬p ∨ ¬q`. The word `not_and_or` is the name Lean gives to this form
  of De Morgan's law.

  There are lots of laws (patterns, equivalences) that we can use with 
  `rewrite`. For now, we'll just use a few. More information about `rewrite` 
  and a longer list of rules will come soon to the quick reference. 

  You can figure out what a rule states using `#check`:

-/

#check not_and_or   -- De Morgan 1
#check not_or       -- De Morgan 2
#check not_not      -- Double negation elimination
#check or_comm      -- Changes the order of an "or"
#check and_comm     -- Changes the order of and "and"


/-

Finally, some useful keyboard shortcuts: 

* `∩`: \inter, \cap 
* `∪`: \union, \cup 
* `ᶜ`: We use this for "complement". \^c 

-/


/-

Here's a proof using the set-element method:

-/

example (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by 
  ext x 
  split_goal 
  { intro hx
    set_simplify 
    rewrite [not_and_or] at hx 
    assumption }
  { intro hx 
    set_simplify
    rewrite [not_and_or] 
    assumption }



/- 

Here's another. This one uses `rw` much more heavily! 

The final goal has the form `p ↔ p`. The `reflexivity` tactic,
which we've seen once or twice already, closes goals like this.
`↔`, `=`, and some other relations are called *reflexive* because
for any `x`, `x ↔ x`, `x = x`, etc. are true.

-/

example (A B : Set U) : (A \ B)ᶜ = B ∪ Aᶜ := by 
  ext x 
  set_simplify
  rewrite [not_and_or]
  rewrite [not_not]
  rewrite [or_comm]
  reflexivity






/- 

## Bonus

We mentioned "De Morgan for quantifiers" in lecture.
Here's a proof of one direction of this. 
The other direction is trickier: we need a new proof technique for it.

-/


example (P : ℕ → Prop) : (¬ ∃ x, P x) ↔ (∀ x, ¬ P x)  := by 
  split_goal                    -- To prove an ↔, prove both directions.

  { intro hne                   -- Suppose `¬ ∃ x, P x`.
    intro x                     -- Take an arbitrary `x`,
    intro hx                    -- and suppose for the sake of contradiction that `P x` holds.
    have hex : ∃ x, P x         -- We then know that `∃ x, P x` holds,
    { existsi x                 -- since `x` is a witness.
      assumption }
    contradiction }             -- This contradicts our original hypothesis.

  { intro hall                  -- For the other direction, suppose `∀ x, ¬ P x`.
    intro hex                   -- Suppose for the sake of contradiction `∃ x, P x`.
    eliminate hex with w hw     -- Then there is a witness `w` such that `P w` holds.
    have hnw : ¬ P w := hall w  -- But, from our first hypothesis, `¬ P w` also holds.
    contradiction }             -- Contradiction.

/- 

There are even rewrite rules for "De Morgan for quantifiers":

-/

#check not_forall 
#check not_exists