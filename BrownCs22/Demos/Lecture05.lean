import BrownCs22.Library.Tactics 

/-

Wrapping up Lecture 4: here's how we can work with *implications* and *negations*.


if we know `hpq : p → q`, and our goal is to prove `q`,
then `apply hpq` will change the goal to `p`.

-/

example : p → (p → q) → q := by 
  intro hp 
  intro hpq 
  apply hpq 
  assumption 

/-

Alternatively, if we know `hpq : p → q` and `hp : p`, 
we can "reason forward" by writing `have hq : q := hpq hp`.
This adds a new hypothesis `hq : q` without changing the goal.
This syntax is a little clunky, but we'll use it in a more general setting later.

-/

example : p → (p → q) → q ∧ p := by 
  intro hp 
  intro hpq 
  have hq : q := hpq hp 
  split_goal
  { assumption }
  { assumption }





/-
If you *know* a negation: use it to find a contradiction.

-/

variable (p q r : Prop)

example : (¬ p ∧ (p ∨ q)) → q := by 
  intro hand 
  eliminate hand with hnp hpq 
  eliminate hpq with hp hq 
  { contradiction }
  { assumption }

/- 
If you want to *prove* a negation: assume the statement is true,
and find a contradiction.
-/

example : ¬ (p ∧ ¬ p) := by 
  intro hpnp 
  eliminate hpnp with hp hnp 
  contradiction 


(P ∧ Q ∧ R) ∨ (¬ P ∧ ¬ Q ∧ R)
(P ∧ Q) ∨ (¬ P ∧ Q) ∨ (P ∧ ¬ Q) ∨ (¬ P ∧ ¬ Q)
(P ∧ Q) ∨ (¬ P ∧ Q) ∨ (P ∧ ¬ Q)
(P ∨ Q) ∨ (¬ P ∧ Q)