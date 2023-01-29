import BrownCs22.Library.Tactics

/-

In this file, we'll prove some of the identities from
https://brown-cs22.github.io/resources/math-resources/logic.pdf 

Note that these identities are stated with the symbol `≡`,
meaning "the formula on the left is equivalent to the formula on the right."
In Lean, we can use iff (bi-implication, `↔`) to mean the same thing.

Remember the tactics we learned in Lecture 4. 
We'll see a bit of new Lean syntax along the way.

Also remember that it doesn't matter what we name our hypotheses.
In our examples, we use patterns like `hp` for the hypothesis `p`,
`hnpq` for the hypothesis `¬ p ∧ q` (hnpq for "hypothesis not p q"), etc.
But this is just a custom. You can choose any names you want.
As they say, the hardest problem in computer science is naming variables.

Your task: fill in all the `sorry`s with proofs!

-/

variable (p q r : Prop)

-- ## Commutative Laws

-- We'll do the first for you, as an example.
-- Notice two things.
-- One, must of these problems will start with `split_goal`,
-- to turn the `iff` goal into two `implies` goals.
-- Two, we structure our proof by putting each *subproof* in `{...}`.
-- This isn't necessary but it helps with organization!
example : p ∧ q ↔ q ∧ p := by 
  split_goal 
  { intro hpq 
    eliminate hpq with hp hq 
    split_goal 
    assumption 
    assumption }
  { intro hqp 
    eliminate hqp with hq hp 
    split_goal 
    assumption 
    assumption }

example : p ∨ q ↔ q ∨ p := by 
  sorry

-- ## Associative laws 

-- Notice that Lean doesn't print parentheses unless it needs to.
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by 
  sorry 


-- This is getting a little repetitive. 
-- To mix it up, we'll only do one direction of the iff this time.
-- You won't start with `split_goal`, but instead, ... what?
example : (p ∨ q) ∨ r → p ∨ (q ∨ r) := by 
  sorry 

-- ## Distributive laws 

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by 
  sorry 

-- Again, let's just do one direction. 
-- When we're proving an implication `→`, we'll always start with `intro`. 
-- This is such a common pattern that Lean gives us special syntax for it:
-- we can do the intro "in advance," before we start the proof,
-- by naming the hypothesis to the left of the `:`.
-- Notice that at the beginning of our proof, we already have the 
-- hypothesis `hpqr` in our context.
example (hpqr : p ∨ (q ∧ r)) : (p ∨ q) ∧ (p ∨ r) := by 
  sorry 


-- ## Identity laws 

/-

We'll do a few more together.

Let's sneak a new tactic in. 
To prove a goal `True`, you can use the tactic `trivial`. 
This is a sensible proof rule: trivially, you can always show `True` is true!
-/

example : p ∧ True ↔ p := by
  split_goal
  { intro hpT 
    eliminate hpT 
    assumption }
  { intro hpT 
    split_goal
    assumption 
    trivial }

-- Before, we saw `contradiction` would work if we had hypotheses 
-- `p` and `¬ p` at the same time. 
-- It also works if we have a hypothesis `False`!
example : p ∨ False ↔ p := by 
  split_goal 
  { intro hpF 
    eliminate hpF with hp hF 
    assumption 
    contradiction }
  { intro hp 
    left
    assumption }

/-

## Negation laws

If you're following along with the list of identities, you'll see that
we've come to some laws like `(p ∨ ¬ p) ↔ True`.

Unfortunately, we don't have the tools to prove these in Lean yet.

But, you can do the **Idempotent laws** and **Universal bound laws**.
Try stating and proving these yourself!

-/




/-

## De Morgan's Laws 

These can be a bit of a challenge! Like the negation laws,
a few of the implications here will require some new tools. 
But try out these directions.

Remember that to prove a negation `¬ X`, you can use a *proof by contradiction*:
add a hypothesis `h : X` using `intro h`, and then show a contradiction.

-/

example (hnpnq : ¬ p ∨ ¬ q) : ¬(p ∧ q) := by 
  sorry 

example (hnpnq : ¬ p ∧ ¬ q) : ¬ (p ∨ q) := by 
  sorry


/- 

That's it for the moment! 
Try the **Absorption laws** and **Negation of True and False**
on your own, if you want to. Skip the definition laws for now.

-/