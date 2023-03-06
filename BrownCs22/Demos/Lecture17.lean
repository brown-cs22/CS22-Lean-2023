import Mathlib.Data.Nat.Basic 
import BrownCs22.Library.Tactics
import BrownCs22.Library.ModSubst.ModRel
import BrownCs22.Library.Defs

set_option linter.unusedVariables false

open BrownCs22

/-

# Lecture 17 Lean notes

We've been using Lean (on and off) in homeworks. 
The plan for today is to get a bit more context about *why* 
people are interested in tools like this.


## GCD in Lean

First of all: we've mentioned before that Lean is in fact 
a programming language itself. Here's the `gcd` function 
we've been discussing, implementing Euclid's algorithm.

(We could implement the extended Euclidean algorithm, the "pulverizer",
but let's keep it simple for now.)

-/

def gcd (a b : ℕ) : ℕ := 
  if b < a then 
    gcd b a 
  else if h : a = 0 then 
    b 
  else 
    have hlt : b % a < a := Nat.mod_lt _ (by positivity)
    gcd (b%a) a
termination_by gcd a b => a


#eval gcd 55 60 
#eval gcd 22 3 

/-

This looks more or less like our slides version, with a couple funny things.
First of all: there are `have` statements and hypothesis names `h : ` in the 
body of our program!
Second of all, what's the `termination_by` at the end?


Lean is a very particular programming language. 
It does not support functions that fail to terminate, or that raise 
error messages. In other words: *we can only define total functions!*

The statements we write in the body of our program help Lean decide 
that the program does, in fact, terminate. 
(Actually: it *proves* that the program terminates, automatically.)


Proving about programs, cool. It's here that proof assistants like Lean 
really shine. Most proofs can't be done automatically, but...

Here's a proof that the output of `gcd` always divides both the inputs.
(We won't talk through the details in class.)
-/


theorem gcd_divides : ∀ a b : ℕ, gcd a b ∣ a ∧ gcd a b ∣ b := by 
  -- We proceed by strong induction on `a`,
  -- with predicate `∀ b : ℕ, gcd a b ∣ a ∧ gcd a b ∣ b`.
  strong_induction 

  -- Introduce the induction hypothesis into the context.
  intro a 
  intro ih 
  intro b

  -- Expand the definition of `gcd`.
  unfold gcd

  -- Let's reason by cases on whether `b < a`. 
  by_cases hba : b < a 

  -- If we know `b < a`, we can simplify our `gcd` program (we know which branch of the `if` statement we take)
  { simp [hba]

    -- We can instantiate the induction hypothesis to match the goal.
    have ih2 : gcd b a ∣ b ∧ gcd b a ∣ a := ih b hba a
    rw [and_comm]
    assumption }

  -- Otherwise, we know `¬ b < a`.
  { simp [hba]

    -- Reason by cases again, on whether `a = 0`.
    by_cases ha : a = 0

    -- If `a = 0`, our proof is easy: `0 ∣ 0 ∧ 0 ∣ b` is trivial.
    { simp [ha] }

    -- Otherwise, we can again simplify our program knowing we're in the "else" branch.
    { simp [ha]

      -- We can again instantiate our induction hypothesis.
      have ih3 : gcd (b % a) a ∣ b % a ∧ gcd (b % a) a ∣ a := 
        ih (b % a) (Nat.mod_lt _ (by positivity)) a 
      eliminate ih3 with hl hr 

      -- We need to prove two "divides" claims. 
      split_goal 

      -- The first comes directly from our induction hypothesis.
      { assumption }

      -- Otherwise, let's do some arithmetic, expanding the definition of `∣`. 
      { dsimp [Dvd.dvd] at hl hr ⊢
        eliminate hl with k hk 
        eliminate hr with m hm

        -- We apply the qhotient-remainder theorem on `b % a`,
        -- which in Lean is named `Nat.div_add_mod`.
        have qr := Nat.div_add_mod b a 

        -- We can then compute a witness for divisibility...
        existsi (b/a)*m + k 

        -- and do a (slightly ugly) calculation, with the help of polyrith.
        -- (Don't worry about the details here too much.)      
        zify at qr hm hk ⊢ 
        linear_combination hk + (b / a : ℤ) * hm - qr } } }



/-

A lot of real-world programs -- encryptors or decryptors, for instance -- 
depend on a subroutine that computes gcds. 
A lot of these programs are safety-critical, in that bugs in this programs 
could have severe social, political, or economic consequences.

Imagine if they were formally verified....

-/



open BrownCs22.Int Dvd

/-

## Modular arithmetic in Lean

On Friday we introduced the notion of "equivalence modulo `n`".
Two integers are equivalent if they are separated by a multiple of `n`.

-/

#check ModEq

#eval 4 ≡ 14 [ZMOD 5]
#eval 23 ≡ 11 [ZMOD 12]
#eval 22 ≡ 11 [ZMOD 12]


/-
We can *prove* modular equivalences, using tools we've used before.
-/

example : 4 ≡ 14 [ZMOD 5] := by 
  dsimp [ModEq]
  dsimp [dvd]
  existsi -2 
  numbers 

/-
But if Lean can evaluate facts like this, why can't it prove them automatically?
-/

example : 4 ≡ 14 [ZMOD 5] := by 
  decide 


/-
Ultimately, we're not interested so much in a bare calculator.
We want to prove things about equivalences.

Here's a theorem that says, if `a ≡ b`, we can add equivalent values
to each side. (We used this in Friday's lecture...)
-/

theorem Int.ModEq.add {n a b c d : ℤ} 
  (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [ModEq, dvd] at *
  eliminate h1 with x hx 
  eliminate h2 with y hy
  existsi x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by linarith
                  _ = n * x + n * y   := by rw [hx, hy]
                  _ = n * (x + y)     := by linarith



/-
We ended the day on Friday thinking about *division*.
If I know `a ≡ b`, do I know `a/c ≡ b/c`? 
Certainly not if `c` doesn't divide `a` or `b`. 
But what if it does? Could we prove this theorem?
-/

example {a b c n : ℤ} 
  (hca : c ∣ a) (hcb : c ∣ b) (hab : a ≡ b [ZMOD n]) : 
    a/c ≡ b/c [ZMOD n] := by
sorry








/-
After some thought and experimentation: *no!*
Let `a = 10`, `b = 22`, `c = 2`, `n = 4`.
-/

example : 2 ∣ 10               := by decide 
example : 2 ∣ 22               := by decide 
example : 10 ≡ 22 [ZMOD 4]     := by decide 
example : 10/2 ≡ 22/2 [ZMOD 4] := by sorry

#eval 10/2 ≡ 22/2 [ZMOD 4]




/-

So, we can't necessarily "cancel" across both sides of a modular equivalence.
But we can simplify addition, multiplication, exponents, ...

-/


example (a b : ℤ) (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 2 [ZMOD 5] :=
  calc
    a * b + b ^ 3 + 3 ≡ 4 * b + b ^ 3 + 3 [ZMOD 5] := by mod_subst [ha]
                    _ ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by mod_subst [hb]
                    _ = 2 + 5 * 8                  := by numbers
                    _ ≡ 2 [ZMOD 5]                 := by decide

