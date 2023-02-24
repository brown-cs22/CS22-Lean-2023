import BrownCs22.Library.Tactics

/-

# Induction in Lean

There are tactics corresponding to the induction principles we saw in class. 
Think about it: how many goals should each induction principle produce?
What hypotheses do we have in each goal?



* `basic_induction` is the normal, one-step, starting-from-0 induction:

-/

example (P : ℕ → Prop) : ∀ n, P n := by 
  basic_induction 
  { sorry } -- show `P 0` 
  { intro n 
    intro hn 
    sorry } -- assuming `P n`, show `P (n + 1)` 








/-

* `induction_from_starting_point`: again, as the name implies, this lets 
  us start a normal induction proof from a value besides 0.

-/

example (P : ℕ → Prop) : ∀ n ≥ 4, P n := by 
  induction_from_starting_point
  { sorry } -- prove `P 4`
  { intro n 
    intro hn4 
    intro hpn
    sorry } -- assuming `4 ≤ n` and `P n`, show `P (n + 1)`




/- 

Here's an example we did in class, typed into Lean!

-/

example : ∀ n ≥ 5, 2^n > n^2 := by 
  induction_from_starting_point 
  { numbers }
  { intro n 
    intro hn 
    intro ih 
    have hle : 2*n + 1 ≤ n^2
    { nlinarith }
    calc (n+1)^2 = n^2 + 2*n + 1 := by linarith
               _ ≤ n^2 + n^2     := by linarith
               _ < 2^n + 2^n     := by linarith
               _ = 2^n * 2       := by linarith
               _ = 2 ^ (n + 1)   := by rw [pow_add, pow_one]
  }










/-

* `strong_induction` is, as the name implies, an induction principle 
  that lets us assume `P` holds of *all* smaller numbers.
  Why is there no base case here?

-/

example (P : ℕ → Prop) : ∀ n, P n := by 
  strong_induction
  intro n 
  intro hn 
  sorry -- assuming `∀ (m : ℕ), m < n → P m`, show `P n`


/-

There's no base case because if we can prove the strong induction step 
for every `n`, it must hold for `0`, which implies `P 0`:

-/

example (P : ℕ → Prop) (hn : ∀ (n : ℕ), (∀ (m : ℕ), m < n → P m) → P n) : 
    P 0 := by 
  have hn0 : (∀ (m : ℕ), (m < 0 → P m)) → P 0 := hn 0 
  apply hn0 
  intro m hm 
  contradiction

