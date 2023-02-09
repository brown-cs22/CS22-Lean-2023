import BrownCs22.Library.Tactics
import BrownCs22.Library.TruthTables

/-

In this file, we'll keep a running lecture-by-lecture list
of the Lean syntax and tactics that we've learned.

-/



/-

## Lecture 2

`#check <expression>` tells us what kind of thing `<expression>` is.

-/

#check 0 
#check 1 + 1 = 3


/-

## Lecture 3

`variable (p q r : Prop)` introduces the atomic propositions `p`, `q`, `r`.
(If we enclose them in `section` ... `end`, their scope is limited.)

-/

section 

variable (p q r : Prop)

#check p ∧ q → r

end 

/- 

`#truth_table p ∧ q ∨ r` prints a truth table for the given proposition.

-/

#truth_table p ∧ q


/-

## Lecture 4

We begin proofs by writing 

`example : p → p := by` or 
`theorem my_theorem_name : p → p := by`.

Following lines should be indented two spaces.

-/

example : p → p := by
  intro hp 
  assumption 

/-

The new tactics (proof rules) we saw:

* `sorry`: proves anything! (Cheating!)

* `split_goal`: turn a goal of `p ∧ q` into two goals `p` and `q`,
  and a goal of `p ↔ q` into two goals `p → q` and `q → p`. 

* `left` and `right`: turn a goal of `p ∨ q` into a goal of `p` 
  or a goal of `q`, respectively.

* `intro h`: turn a goal of `p → q` into a goal of `q`,
  with an extra hypothesis `h : p`.

* `assumption`: if a hypothesis `h` matches the goal, will solve the goal.

* `eliminate h with h1 h2`: when a hypothesis `h : p ∧ q`, 
  replaces `h` with two hypotheses `h1 : p` and `h2 : q`. 
  When a hypothesis `h : p ∨ q`, creates two goals, one with 
  a hypothesis `h1 : p` and one with a hypothesis `h2 : q`. 

* `apply h`: if `h : p → q` and the goal is `q`, changes the goal to `p`.
  Read this as "to show `q`, it suffices to show `p`".
  We'll use this later in a slightly different context. 

* `have h : q := hpq hp`: if `hpq : p → q` and `hp : p` (the lhs of the → matches),
  creates a new hypothesis `h : q`. 
  Read this as "I know `p → q` and I know `p`, so I know `q`."

* `contradiction`: If you have both a proposition and its negation in your context,
  will prove any goal.

-/


/-

## Lecture 6

Some more new tactics, or new behavior for old tactics:

* `intro t`: turn a goal of `∀ x : T, P x` into a goal of `P t`,
  with a new term `t : T` in the context. 

* `have h : P t := hP t`: if `hP : ∀ x : T, P x` and `t : T`,
  creates a new hypothesis `h : P t`. 
  Read this as "I know every `T` has property `P`, and `t` is a `T`, 
  so `t` must have property `P`.

* `existsi t`: turns a goal of `∃ x : T, G x` into a goal of `G t`.
  This is the tactic we use to provide a witness.

* `eliminate h with t ht`: when a hypothesis `h :  ∃ x : T, H x`, 
  replaces `h` with a new witness `t` and the hypothesis `ht : H t`.
  You should always use a fresh name for `t`.

* `reflexivity`: proves equality goals where the LHS and RHS are the same,
  like `x = x` and `f y = f y`. 

-/


/-

## Homework 2

* `positivity`: if your goal is to show something is positive or nonnegative 
  (like `0 < x`, `x ≥ 0`, `0 ≤ a^2`, ...) and this "obviously" follows from
  your hypotheses, write `positivity` to finish that goal. This tactic knows
  basic facts like "natural numbers are nonnegative" and "the square of a 
  positive number is positive." It does not know complicated arithmetic.

* `numbers`: If your goal is to show an arithmetic statement about numerals,
  like `5 + 5 = 10` or `1000 < 50000000`, `numbers` will close the goal.
  It's basically a calculator!

* `linarith`: stands for "linear arithmetic." (If you don't know this term,
  don't worry.) `linarith` does similar things to `positivity` and `numbers`,
  but it can do some simple arithmetic, and use hypotheses.
  For instance, if you know `h1 : x < 10` and `h2 : x + y < 20`, `linarith`
  can prove the goal `3*x + 2*y < 50`.

-/