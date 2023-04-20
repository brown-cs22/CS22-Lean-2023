import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs


/-

# Strong Induction (Mindbender)

You've seen `basic_induction`, now get ready for `strong_induction`! This is an
alternative induction tactic that can be used on induction proofs where using
`basic_induction` would be awkward and confusing.

Informally: using basic induction, in our inductive step, we get to assume `P(n)` 
and need to prove `P(n+1)`. Using strong induction, We get to assume more in the 
inductive step: we assume `P(0)`, `P(1)`, ..., `P(n)`, and need to prove `P(n+1)`.
Generically, we can say that our induction hypothesis is `∀ k, k ≤ n → P(k)`: 
"`P` holds for all `k` between 0 and `n` inclusive."

A slight variant of this lets us get rid of the base case -- how useful! 
We assume `∀ k, k < n → P(k)` and prove `P(n)`.
We talked about this briefly in class way back when, on Feb 22.



Now in Lean!

Recall that `basic_induction` transforms a goal of `∀ (x : ℕ), P(x)` into two new
goals: `P(0)` and `∀ (x : ℕ), P(x) → P(x+1)`.

On the other hand, `strong_induction` only creates one new goal -- it uses the 
variant version of strong induction. However, the transformed goal can look quite 
confusing in Lean, so we're going to walk through it step by step.

-/

variable (P : Nat → Prop)

example : ∀ (x : ℕ), P x := by
  strong_induction
  sorry

/-

The example above shows that the `strong_induction` tactic replaces our goal with:

`∀ (n : ℕ), (∀ (m : ℕ), m < n → P m) → P n`

Seeing this, it's natural to ask two questions:
1. Why would proving this let us prove our goal?
2. What does this even mean?

To try to answer these questions, let's isolate the middle part of that expression:

`(∀ (m : ℕ), m < n → P m)`

In English, we can read that proposition as, "`P` is satisfied for all natural numbers
less than `n`." Let's extract this proposition into a named predicate `SatisfiedBelow`,
to hopefully make things clearer.

`SatisfiedBelow n ↔ (∀ (m : ℕ), m < n → P m)`

So `SatisfiedBelow n` is true iff `P` is satisfied for all natural numbers below `n`.

Using that named predicate, we can rewrite the goal given to us by `strong_induction`:

`∀ (n : ℕ), SatisfiedBelow n → P n`

In this form, it's a lot easier to recognize the goal as the definition of strong
induction we discussed in class. This is saying that for all `n`, if `P` is true
for all natural numbers below `n`, then `P` is true for `n` as well. And since
`SatisfiedBelow n` is *vacuously true* when `n = 0`, proving this goal will
automatically prove `P 0`, and therefore also `P 1`, and `P 2`, and so on.



# The Problem

We're going to use the `strong_induction` tactic to prove something we discussed
in class - that all natural numbers 8 or larger can be made using coins of value
3 and 5.

Here's the predicate `P` we'll be working with:

-/

def from_three_five (n : ℕ) : Prop :=
  ∃ (x y : ℕ), n = 3 * x + 5 * y

/-

You'll need these three lemmas - they shouldn't require more than 2 lines each to prove.

-/

/- 1 point -/
lemma ftf8 : from_three_five 8 := by
  sorry

/- 1 point -/
lemma ftf9 : from_three_five 9 := by
  sorry

/- 1 point -/
lemma ftf10 : from_three_five 10 := by
  sorry

/-

Now for the tricky parts. This next lemma is a proof that if `n` is between 8 and
10, inclusive, then it can be made from 3 and 5. This follows from the three lemmas
above, but it will be useful to get it into this form. Your main tool in this proof
will be the Mathlib lemma `lt_or_le`, which is a proof that for any natural numbers
`x` and `y`, either `x < y`, or `y ≤ x`. (It actually works for more than just natural
numbers, but we won't go into that.)

-/

#check lt_or_le

/- 1 points -/
lemma ftf_of_ge_8_le_10 (n : ℕ) : 8 ≤ n ∧ n ≤ 10 → from_three_five n := by
  intro h
  eliminate (lt_or_le n 9) with htri9 htri9
  {
    sorry
  }
  {
    eliminate (lt_or_le n 10) with htri10 htri10
    {
      sorry
    }
    {
      sorry
    }
  }

/-

Two more helper lemmas, and then we finish this once and for all. These two are
*almost* the same - the first says that if `n` can be made from 3 and 5, so can `n+3`.
The second says that if `n-3` can be made from 3 and 5, so can `n`. Consider:
why aren't these *exactly* equivalent? And why does the second lemma require the
extra hypothesis `3 ≤ n`?

-/

/- 1 point -/
lemma ftf_add_3_of_ftf_self (n : ℕ) :
  from_three_five n → from_three_five (n+3) := by
  sorry

-- You may find the Mathlib lemma below to be useful.
#check Nat.sub_add_comm

/- 1 point -/
lemma ftf_of_ftf_sub_3 (n : ℕ) :
  3 ≤ n → from_three_five (n-3) → from_three_five n := by
  intro h_3_le_n hftf
  have : (n-3) + 3 = n := by {
    sorry
  }
  sorry

/-

You may find the Mathlib lemmas below useful. Also, `linarith` is your friend :)

-/

#check Nat.sub_lt_self
#check Nat.le_sub_of_add_le

/- 2 points -/
lemma all_from_three_five : ∀ (n : ℕ), 8 ≤ n → from_three_five n := by
  strong_induction
  intro n hind h
  eliminate (lt_or_le n 11) with htri htri
  {
    sorry
  }
  {
    sorry
  }