import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs

-- don't change these lines
namespace HW3
open Set BrownCs22.Set
set_option linter.unusedVariables false
variable (U : Type)
variable (A B : Set U)

/-

# Welcome to the Lean section of HW3!

In these problems, we're going to get a little practice formally proving 
set equalities. We've seen two techniques for doing this on paper:

* With the set-element method, we argue that `A = B` by showing that 
  `A ⊆ B` and `B ⊆ A`.
* With the algebraic method, we can prove that sets are equal by rewriting
  one or both sides with algebraic identities like `(Aᶜ)ᶜ = A`, until we 
  have identical expressions.

We can do both of these in Lean. In this assignment you'll prove two 
set equalities, one with each method.

**Notes**: 

* Remember that in Lean, we write "the complement of A" as `Aᶜ` instead 
  of using a bar over the letter. (Diacritics are hard in a text editor!)

* You can type `⊆` using `\sub`.

* You can type `ᶜ` using `\compl` or `\^c`.

-/


/-

## Problem 1: the set-element method

We saw two important tactics in lecture for set-element proofs in Lean:

* `ext x`: given a goal `A = B` where `A` and `B` are sets, changes the goal
  to showing `x ∈ A ↔ x ∈ B` for an arbitrary element `x`. The name comes 
  from "extensionality," the property that two sets are equal if they have
  the same elements.

* `set_simplify`: unfolds the "logic" of a set membership proposition. 
  For instance, `x ∈ A ∩ B` simplifies to `x ∈ A ∧ x ∈ B`. 
  `x ∈ A \ C` simplifies to `x ∈ A ∧ ¬(x ∈ C)`.
  Calling `set_simplify` will simplify the goal and all hypotheses.

Use these techniques to prove the following.
Starting with `ext x` is probably a good move!
Then think about the last few homeworks; how do you prove an `↔` goal?

-/

/- 4 points -/
theorem problem_1 : (A ∩ B) ∪ A = A := by 
  ext x 
  split_goal 
  { intro hx 
    set_simplify
    eliminate hx with hxab hxa
    { eliminate hxab with hxa hxb 
      assumption }
    { assumption } }
  { intro hx 
    set_simplify 
    right
    assumption }


/-

## Problem 2: the algebraic method

What you just proved is sometimes called an "absorption law," since the 
intersection `A ∩ B` gets "absorbed" into the bigger set `A`.
This is an example of a useful rewrite rule: if we ever see the pattern 
`X ∪ (X ∩ Y)` in a proposition, we can replace it with `X`, since we know
that these sets are the same. 

As we saw in Lecture 8, the `rewrite` tactic lets us do this in Lean. 
Here's an example of using the above rule, and another useful rewrite rule:

-/


example : A ∩ ((Aᶜ ∩ B) ∪ Aᶜ) = ∅ := by 
  rewrite [inter_union_cancel_left]
  rewrite [inter_compl_self]
  reflexivity

/-

The name Lean gives to our identity from problem 1 is 
`inter_union_cancel_left`. We also used `inter_compl_self`, which says 
`A ∩ Aᶜ = ∅`. Hover over the name in the proof above to see this statement!

The final tactic, `reflexivity`, tells Lean that we are done: we can close
any goal of the form `P ↔ P`.

The `rewrite` tactic will use the identity "left to right":
it will look for the pattern on the left hand side of the identity,
and replace it with the right hand side. For example, `inter_compl_self`
says that `s ∩ sᶜ = ∅`, so it replaces `s ∩ sᶜ` with `∅`.
Sometimes you can use a rule in reverse direction, right to left,
using the symbol `←` (typed `\l` or `\<-`). For example:

-/ 

example : Aᶜ ∩ Aᶜ = Aᶜ := by 
  rewrite [← compl_union] -- we have used de morgan's law "backward",
                          -- changing `Aᶜ ∩ Aᶜ` to `(A ∪ A)ᶜ`.
  rewrite [union_self] 
  reflexivity

/-
But this won't work for every identity! Think about `inter_compl_self`.
Backward, this would say that if you see the pattern `∅`, you can replace 
it with `s ∩ sᶜ`. But how would Lean know what set `s` you wanted to use?
It could be anything! If you see some funny symbols like `?m1000`,
this is probably what's going on.

You may or may not need to use rules backwards in the following problem.


In recitation, you saw (or will see) a list of set identities:
<https://brown-cs22.github.io/resources/math-resources/sets.pdf>
All the identities on this list are available as rewrite rules in Lean,
listed in the file `BrownCs22/Demos/SetIdentities.lean`.

Use these rewrite rules to complete the following proof. Your proof should
have the same structure as the example above: 
a sequence of rewrites, followed by `reflexivity`.

It might help to plan out your steps on paper!

-/

/- 4 points -/
theorem problem_2 : (Aᶜ \ B)ᶜ = A ∪ B := by 
  rewrite [diff_eq]
  rewrite [compl_inter]
  rewrite [compl_compl]
  rewrite [compl_compl]
  reflexivity





end HW3