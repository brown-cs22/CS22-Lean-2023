import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs
import Mathlib.Tactic.LibrarySearch

set_option pp.notation true
set_option linter.unusedVariables false
namespace Hw7


/-

# Application and Induction

In this homework, we're going to introduce you to two of the most powerful and
commonly-used tactics in Lean, `simp` and `apply`.

(We're all simps for `simp`!)

We'll also be giving you a gentle introduction to induction proofs in Lean, using
the tactic `basic_induction`, which inducts over all natural numbers, starting from 0.

This homework is quite long, but don't panic! Most of it is reading and worked
examples. There's only a few actual problems for you to do.





## Simplification

The `simp` tactic, like `dsimp`, `simp`lifies expressions. However, `dsimp` only
knows about *definitions*. For instance, if we have a function defined like this...

-/

def f (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | x + 1 => (f x) + 1

/-

... then `dsimp` could simplify `f 0` to `0`, and simplify `f 1` to `1`, and so on.

(Note that `f` is defined *recursively*: `f 2 = (f 1) + 1 = ((f 0) + 1) + 1 = 0 + 1 + 1 = 2`.

But what about `f x`? Without knowing the actual value of `x`, `dsimp` doesn't know
how to expand the definition of `f`. It's not smart enough to know that `f x` is always
equivalent to `x`, it just knows how to mechanically unwrap definitions.

`simp`, on the other hand, knows a LOT of ways to simplify expressions, including
everything `dsimp` can do. However, unlike `dsimp`, it doesn't automatically figure
out simplification rules from definitions. Someone has to manually write the code
that tells `simp` how to simplify things. We haven't done that here, so it won't
help us with the `f` example.

The good news is that `simp` comes built-in with a lot of useful simplification 
rules that can make proof-writing much easier. Whenever you find yourself looking
at your proof goal and thinking, "ugh, OBVIously this is true, why can't Lean just
accept it already???", and `dsimp` isn't doing anything, you may want to try `simp`.
This is especially convenient for when you have annoying bits of arithmetic trapped
deep inside an expression where `numbers` and `linarith` can't do anything about them.

Here's a demo:

-/

example : Nat.gcd (0 + a) a = a := by
  -- numbers -- nope doesn't work
  -- linarith -- nope
  -- dsimp -- still nothing
  simp -- hooray, we're done!


/-

## The `apply` tactic

So far, we've given you two main ways of using existing theorems in a new proof:
`eliminate` and `have`. And they're not going away! They're very useful, and the
best tool for the job in many, many proofs. But, both techniques have their drawbacks.

`eliminate` will only let you use an existing theorem if it is either:
1. a conjunction (an AND statement, like `(2 + 2 = 4) ∧ (3 = 3)`),
2. a disjunction (an OR statement, like `(2 = 3) ∨ (3 = 3)`),
3. or an existential (a statement like `∃ x, x + 1 = 2`).

But many theorems do not fit into any of these boxes.

`have`, on the other hand, is quite general, but sometimes awkward to use. Let's
say we wanted to prove a proposition `P`, and we have an existing theorem, called
`helper`, that says `A → B → P`. So, if we have proofs of `A` and `B`, then by 
modus ponens, we can conclude `P` from `helper`.

How would we write this in Lean, using `have`? Well, it would look something like
this, where the stuff in brackets is a placeholder for some actual proof:

`have proof_of_A : A := [... proof of A ...]`
`have proof_of_B : B := [... proof of B ...]`
`have goal : P := helper proof_of_A proof_of_B`

This works! But it could be much simpler. We had to give explicit names to our
subproofs of `A` and `B`, even though we might not use them later. We also had
to manually invoke `helper` at the end, and make sure we passed in `proof_of_A`
and `proof_of_B` in the right order. Pretty easy here, but getting the order right
for helper theorems with a dozen premises gets tedious!

The core issue here is that, once we have `helper`, WE DON'T CARE ABOUT PROVING
`P` DIRECTLY ANYMORE. We just care about proving `A` and `B` - then getting `P`
from `helper` is easy. But, if we only use `have`, then Lean thinks our goal is
always just `P`, which means it won't help us out in proving `A` and `B`.

This is where `apply` comes in! Here's the same proof of `P`, written using `apply`:

`apply helper`
`[... proof of A ...]`
`[... proof of B ...]`

Much simpler, right? Here's what's happening. The `apply` tactic expects to be given
a proof of some implication. Here, we gave it `helper`, which is a double implication,
so that works. That first line, `apply helper`, tells Lean to look at the current
goal (`P`) and the conclusion of the given theorem (`helper` is a proof of `A → B → P`,
so the conclusion is `P`). They match, so Lean knows we'll be done as soon as we prove
`A` and prove `B`. So it removes the goal of `P`, and replaces it with two new,
simpler goals: `A` and then `B`. This nicely cleans up our context and breaks down
the problem, and means Lean will have a better idea of what we're trying to do,
so it will be better at filling in the details.

Enough explaining, let's look at some examples.

-/

-- This is a lot like the example we just looked at, except `A` and `B` are given to us
example (A B P : Prop) : A → B → (A → B → P) → P := by
  intros a b habp -- We want to just have `P` as our goal, so we can use `apply`
  apply habp  -- `habp` has conclusion `P` which matches. It creates two goals
  { assumption }  -- Our first new goal is `A`, and we already have proof in context
  { assumption }  -- Our second goal is to prove `B`, and done!

/-

Now let's try a more "real" example. Our `helper` theorem this time will be the
beautifully-named `Nat.mul_lt_mul_of_pos_left`, which comes from Lean's library. It says
that if `a` is less than `b`, then `ka` is less than `kb` as long as `k` isn't 0.
You can `#check Nat.mul_lt_mul_of_pos_left` or hover over it in the example below 
to see its formal statement.

We could just use `numbers` here, but I'm using `apply` for the sake of demonstration.
Unfortunately, it's hard to think of simple examples for which no one's made a powerful
tactic that can do everything for us :'(
  
-/

example : 1337 * 1003 < 1337 * 2005 := by
  -- Lean sees that the conclusion `k * n < k * m` matches our goal `1337 * 1003 < 1337 * 2005`,
  -- and very nicely infers the correct values for `k`, `n`, and `m`.
  apply Nat.mul_lt_mul_of_pos_left
  { numbers } -- proving 1003 < 2005
  { numbers } -- proving 1337 > 0

/-

You may be confused since `Nat.mul_lt_mul_of_pos_left` doesn't really look
like an implication - see the #check statement below. It LOOKS like a universal
quantification. What's going on there?

-/

#check Nat.mul_lt_mul_of_pos_left

/-

Well, we probably won't go into this much in class, but to Lean, implications and
universal quantifications are basically the same thing. But you don't need to worry
about this much. The one thing that might get confusing is that, if Lean can't automatically
figure out how to assign the quantified variable, it'll ask you to provide it. If
your Infoview shows a goal of `ℕ` or `ℚ`, or something else that doesn't look like
a proposition, that's what's happening. It's asking you to provide a value for the
quantified variable. You may also see symbols like `?a` elsewhere in the context -
those are placeholders waiting for that missing value.

If you need to provide a missing value to continue the proof, but it's not showing
up as your first goal, you can use the `case` tactic to focus that goal. The value
you provide will then fill in for the weird `?a` variables. To demonstrate this,
we're going to prove that `1 < 3` in a very silly and roundabout way. Try placing
your cursor at each step in the proof to see how the context and goals are changing.

-/

example : 1 < 3 := by
  -- This tells Lean we're going to prove 1 < 3 via transitivity. In other words,
  -- we're going to pick a value `x`, show 1 < `x`, and show `x` < 3. We're going
  -- to choose `x = 2` for this (really it's our only option). Lean will pick a
  -- weird-looking variable name instead of `x`, but I'll stuck with just `x`
  -- cuz it looks nicer.
  apply lt_trans

  -- Uh oh! Lean next wants us to prove 1 < `x`, but we haven't even chosen a value
  -- for `x` yet! How are we supposed to prove anything about it? Notice that the 
  -- third goal is just `ℕ` - that's where we actually tell Lean what we want `x`
  -- to be.

  -- To fix this, let's move that third goal to the front. See how it's labeled 
  -- `case b` in the Infoview? To move it up, we use the `case` tactic, like this:
  case b => 
    -- We can use the `exact` tactic to provide missing values.
    -- It doesn't have to be a literal value, though - if we had `x : ℕ` and
    -- `y : ℕ` in our context, we could have used `x + y` here. 
    exact 2
  

  -- Now our remaining goals are filled out, and we can finish the proof.
  { numbers }
  { numbers }

/-

So far, all our examples have applied theorems that are double-implications, but
that was just to match our initial explanation. You can `apply` single implications,
or quintuple implications, or whatever.

In this next example, notice that we use both `apply` and `have`! This was a case
where using both tactics made for a much easier proof. However, it's still much more
complicated than the previous examples, so we recommend stepping through it line-by-line,
and observing how the Infoview changes with each step.

-/

example (a : ℕ) : (a ∣ a+1) → a = 1 := by
  intro h

  -- I found this theorem in the library! If we can prove `a` divides 1, we'll be done.
  apply Nat.eq_one_of_dvd_one

  -- I use `have` here because I want to rewrite `1` as `(a + 1) - a`, so that the
  -- conclusion of `Nat.dvd_sub` will match properly. That will require calling
  -- `rewrite` with a named proof of `1 = (a + 1) - a`.
  have rewrite_helper : 1 = (a + 1) - a 
  { -- Since I didn't supply a proof of rewrite_helper, Lean makes it a goal for us
    -- to fill in.

    -- To change the goal from `1 = (a + 1) - a` to `(a + 1) - a = 1`. This lets me
    -- apply the next theorem, `Nat.add_sub_cancel_left`.
    apply Eq.symm

    -- This finishes the proof of rewrite_helper
    apply Nat.add_sub_cancel_left }

  -- Finally I can use `Nat.dvd_sub`. Now we just have to prove the premises, which
  -- are: `a ≤ a + 1`, `a ∣ a + 1`, and `a ∣ a`. We already have the tools to do all three!
  rewrite [rewrite_helper]
  apply Nat.dvd_sub

  { linarith }
  { assumption }

  -- The "divides" operator is reflexive, and Lean knows that.
  { reflexivity }


  
/-

## Problems 1 and 2

Now it's your turn! For each problem below, we've noted some theorems from
Mathlib that we recommend `apply`ing. You'll then have to prove the resulting
subgoals.

Try putting your cursor after the #check statements to see what each theorem does.

-/

-- Note: in Mathlib theorems, `lt` stands for Less Than, and `le` stands for
-- Less than or Equal to. Learning the abbreviations makes theorem names just
-- a *little* bit easier to read.
#check lt_of_lt_of_le
#check Nat.add_lt_add_left
#check Nat.add_le_add_right

-- Hint: show a + c < a + d, and a + d ≤ b + d
-- Hint: use lt_of_lt_of_le, Nat.add_lt_add_left, and Nat.add_le_add_right
-- Hint: you may need the `case` tactic - 

/- 2 points -/
lemma problem_1 (a b c d : ℕ) :
  a ≤ b →
  c < d → 
  a + c < b + d := by

  sorry

#check Nat.mul_le_mul
#check Nat.le_of_lt

-- Hint: use `problem_1`, `Nat.mul_le_mul`, and `Nat.le_of_lt`

/- 2 points -/
lemma problem_2 (a b c d e f : ℕ) :
  a < b → 
  c < d → 
  e < f → 
  a * c + e < b * d + f := by

  sorry



/-

## Induction

If you've gotten comfortable with the induction problems presented in class and in
homework, then the way Lean deals with induction should feel fairly natural. Well,
as natural as Lean ever feels.


With that out of the way, let's look at `basic_induction`. To demonstrate, we're
going to look at one of the first induction problems we saw in class - the formula
for triangular numbers.

Remember, the `n`th triangular number is `1 + 2 + 3 + ... + n`

And we proved in class that this is equal to `(n * (n + 1)) / 2`

First, we need to define them the first way, below.
Note that this is again a recursive definition!

-/

def tri_nums (n : ℕ) :=
  match n with
  | 0 => 0
  | n + 1 => (tri_nums n) + (n + 1)

/-

Now let's prove that the closed-form formula is equivalent! To simplify things,
we're actually going to prove that `2 * (tri_nums n) = n * (n + 1)`. This just
gets rid of the division by 2.

Finally we get to see `basic_induction` in action. This tactic can be applied
whenever our proof goal is a universal quantification over natural numbers, so
it has to look like `∀ (n : ℕ), P(n)` for some predicate `P`.

To prove the goal, `basic_induction` gives us two new goals. First, we'll need
to prove `P(0)`. Then, we'll need to prove that `∀ (n : ℕ), P(n) → P(n + 1)`.
This is just like the induction problems you've already seen!

-/

lemma tri_formula : ∀ (n : ℕ), 2 * (tri_nums n) = n * (n + 1) := by
  basic_induction
  {
    -- Prove that the zeroth triangular number is zero. Well, that's true just from
    -- how we defined tri_nums, so let's use dsimp
    dsimp [tri_nums]
  }
  {
    -- Now for the inductive case!
    intros n h
    dsimp [tri_nums]
    simp
    rewrite [Nat.left_distrib, h]
    linarith
  }



/-

## Problem 3

Now you try! This first problem is a lot like the last one, except we only use odd
numbers:

1 = 1
1 + 3 = 4
1 + 3 + 5 = 9
1 + 3 + 5 + 7 = 16

We're asking you to prove that this pattern always gives you the `n`th square number.

-/

def recursive_square (n : ℕ) :=
  match n with
  | 0 => 0
  | n + 1 => recursive_square n + (2 * n + 1)

/- 2 points -/
lemma square_formula : ∀ (n : ℕ), recursive_square n = n * n := by
  sorry


/-

## Parity and Problem 4

For more induction practice, we're going to build up some foundational theorems
about parity (whether a number is even or odd).

-/

-- A natural number is even iff it is a multiple of 2
def MyEven (n: ℕ) : Prop := ∃ (k : ℕ), 2*k = n 

-- A natural number is odd iff it is one more than a multiple of 2
def MyOdd (n: ℕ) : Prop := ∃ (k : ℕ), 2*k+1 = n

/-

Please note that the above definitions, by themselves, leave very much to be proved!

For instance, it will not be trivial to prove that all numbers are either even or
odd, and not both.

We're also giving you these theorems, which you are free to use however you want:

-/

lemma zero_is_even : MyEven 0 := by
  dsimp [MyEven]
  existsi 0
  numbers

lemma one_is_odd : MyOdd 1 := by
  dsimp [MyOdd]
  existsi 0
  numbers

lemma zero_isnt_odd : ¬(MyOdd 0) := by
  dsimp [MyOdd]
  intro h
  eliminate h with x h
  linarith

lemma one_isnt_even : ¬(MyEven 1) := by
  dsimp [MyEven]
  intro h
  eliminate h with x h
  rewrite [@Nat.mul_eq_one_iff] at h
  linarith
  
lemma even_after_odd (n : ℕ) : MyOdd n → MyEven (n+1) := by
  dsimp [MyEven, MyOdd]
  intro h
  eliminate h with x h
  existsi x + 1
  linarith

lemma odd_after_even (n : ℕ) : MyEven n → MyOdd (n+1) := by
  dsimp [MyEven, MyOdd]
  intro h
  eliminate h with x h
  existsi x
  linarith

lemma even_before_odd : ∀ (n : ℕ), MyOdd (n+1) → MyEven n := by
  intro n
  dsimp [MyEven, MyOdd]
  intro h
  eliminate h with x hx
  existsi x
  linarith

lemma odd_before_even : ∀ (n : ℕ), MyEven (n+1) → MyOdd n := by
  intro n
  dsimp [MyEven, MyOdd]
  intro h
  eliminate h with x hx
  cases x with
  | zero => {apply False.elim; simp at hx; linarith}
  | succ x => {existsi x; linarith}

#check not_and
#check not_or

/-

# Problem 4

You may find `apply` to be very useful here!

Hint: at some point in `not_both`, you might have a negation hypothesis
`hn : ¬ P` and a goal of `False`. 
Remember that we can prove `False` using the `contradiction` tactic 
if we have hypotheses `hn : ¬ P` and `h : P`. 
So a good move here would be `have h : P`! 
Then you'll need to go ahead and prove `P`.

-/

/- 2 points -/
theorem even_or_odd : ∀ (n : ℕ), MyEven n ∨ MyOdd n := by
  sorry

/- 2 points -/
theorem not_both : ∀ (n : ℕ), ¬(MyEven n ∧ MyOdd n) := by
  sorry





end Hw7