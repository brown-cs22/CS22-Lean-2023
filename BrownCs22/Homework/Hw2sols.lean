import BrownCs22.Library.Tactics

namespace HW2

set_option linter.unusedVariables false
open Dvd

/-

# Welcome to the Lean section of HW2!

In this assignment, we're going to move beyond random letters. 
Enough of those `p`, `q`, `r` problems.

Some things to keep in mind:

* The file `BrownCs22/Demos/QuickReference.lean` has some brief notes on 
  which tactics we've seen and what they do. Check it out!

* There's also an FAQ thread on Ed. Check there before making a new post 
  if you run into issues.

* You can hover over any fancy character in VSCode to see how to type it.

* Remember, the autograder will not be happy if your submission has any
  *red* error messages. If you can't finish a question, you can replace your work
  with `sorry`. You won't get points on that question but the autograder will run.


Our goal today: let's prove some interesting things about numbers!
We're looking a little bit ahead, preparing for the number theory 
section of this class. In the process, we'll get familiar with the proof rules
for the *quantifiers* `∀` and `∃`.

(If you don't remember those rules, check out the Lecture 6 notes and the
quick reference.)


## A few helpful tactics

In addition to the proof rules for quantifiers, these tactics may be useful 
to finish your proofs. Depending on how you do your proofs, you may not 
need all of these.

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

A good strategy: if you have a goal with no variables in it (only numbers),
try `numbers`. If it's a comparison between some variables and 0, try 
`positivity`. Otherwise, try `linarith`.

-/


/- 

## Problem 1 

Here's some practice with quantifiers. Read the statement of this question 
out loud to yourself -- what is it stating? 

Remember `ℕ = {0, 1, 2, ...}`, the natural numbers.

-/

/- 3 points -/
theorem problem_1 : ∃ n : ℕ, ∀ x : ℕ, n ≤ x := by 
  existsi 0 
  intro x 
  linarith -- or positivity


/-

## Problems 2-3

We say that a natural number `x : ℕ` *divides* a natural number `y : ℕ`,
written `x ∣ y`, if there exists `c : ℕ` such that `y = x * c`.

This is an existential claim in disguise! Written in logic, we can say 
`x ∣ y` is defined to mean `∃ c : ℕ, y = x * c`.

If you see a statement like `x ∣ y` in your goal or in a hypothesis, 
you can use the tactic `dsimp [dvd]` to change it to the equivalent existential.
This stands for "definition simplify".
(In the future, we'll use `dsimp` to unfold more than just division.)

For example:
-/ 

example (x : ℕ) : x ∣ 10 → x ∣ 10 := by 
  intro hx10 
  dsimp [dvd] -- change the goal to an existential 
  dsimp [dvd] at hx10 -- change the hypothesis hx10 to an existential 
  assumption

/-

We don't *need* to use `dsimp`.
If we want to prove a "divides" statement, we use `existsi` directly, 
just like for the existential statement. 
If we want to use a "divides" hypotheses, we can `eliminate` it directly, 
again just like for an existential.
But it should never hurt to use `dsimp` if you want to.


First, practice an introduction:

-/

/- 1 point -/
theorem problem_2 : 5 ∣ 15 := by 
  existsi 3
  numbers -- or linarith 


/-

## Notes for Problem 2

You may use `dsimp [dvd]` as your first step. This is optional, but totally fine!

The phrasing of this proof in natural language:
We want to show that 5 ∣ 15. This means, we want to show that there is 
`c` such that `15 = 5*c`.
Use 3 as a witness to this existential claim.
We compute `15 = 5*3`, so the proof is done.

-/

/-  

Let's use this definition of divides to prove that any divisor of 10
is also a divisor of 100.

-/

/- 3 points -/
theorem problem_3 : ∀ x : ℕ, x ∣ 10 → x ∣ 100 := by 
  intro x 
  intro hxdvd 
  dsimp [dvd] at hxdvd 
  dsimp [dvd] 
  eliminate hxdvd with k hkx 
  existsi k*10 
  linarith


/-

## Notes for problem 3

Again, the `dsimp`s are optional, but 
encouraged if you don't see how to "unpack" a division statement.

You may be confused about the repeated `intro` at the start.
The first one is a forall intro, the second is an implication intro.
But these moves are very similar: move something from the goal into the context. 
So they use the same tactic name. 

In natural language:
Let x be an arbitrary natural number and suppose x ∣ 10. 
We want to show that x ∣ 100. 
Rephrasing our hypothesis (expanding the definition of "divides"), 
there exists a `c` such that `10 = x*c`.
Call this witness `k`; we then know that `10 = x*k`.
To show that `x ∣ 100`, we need to provide a witness `w` such that `100 = x*w`. 
Use `k*10` as this witness.
We then show that `100 = x*(k*10)` follows from basic arithmetic and the fact
that `10 = x*k`.

-/



/-

## Problem 4

This time, you're going to practice a forall elimination!
Remember the syntax for this:
if you have a hypothesis `h : ∀ x : ℕ, MyProperty1 x ∧ MyProperty2 x`,
you could write `have h2 : MyProperty1 100 ∧ MyProperty2 100 := h 100`,
or even `have h4 : MyProperty1 my_var ∧ MyProperty2 my_var := h my_var`,
if you have a variable named `my_var`.
We say that we have *instantiated* the universal statement 
with `100` and `my_var`, respectively, "plugging in" these values for `x`.



Your creative step in this problem is to decide how to instantiate `h`.
`h` says a certain proposition is true for every `x`.
Which value of `x` is useful to you?

Try to reason through this problem on paper before solving it in Lean.
There's a hint at the bottom of this file.

Notice that we've already introduced the hypothesis `h` for you in this problem.
No need to start with `intro`.


-/

/- 3 points -/
theorem problem_4 (a b : ℤ) (h : ∀ x, 2*a ≤ x ∨ x ≤ 2*b) : a ≤ b := by
  have hab2 : 2*a ≤ a + b ∨ a + b ≤ 2*b := h (a + b)
  eliminate hab2 with h1 h2 
  linarith
  linarith
  


/-

## Bonus challenge

This one isn't for points, and doesn't have to do with numbers. 
But it's a fun logic puzzle. 
Try it if you're enjoying Lean and want a challenge.
But don't feel bad if you can't figure it out!
This problem relates to the infamous "barber paradox" (look it up!).

A hint: the `have` syntax we used for modus ponens is very general.
You can use this whenever you want, to create a new fact in your context.
But you can't create a fact without justifying it.
If you write, for instance, `have h_new_hyp : p ∧ q` 
(*without* a `:=` at the end, which we used for modus ponens),
you will see that a new goal appears. First Lean wants you to prove `p ∧ q`.
Then it wants you to return to your original goal, with a new hypothesis 
`h_new_hyp : p ∧ q` in your context.

An example:

-/


example (p q : Prop) (hp : p) (hq : q) : True := by 
  have hpq : p ∧ q -- after this line, the goal becomes to show `p ∧ q`
  { split_goal     -- use brackets to focus on the first goal
    assumption
    assumption }
  -- at this point in the proof, we have a new hypothesis `hpq : p ∧ q`.
  -- but this was just a silly example so we don't need to use it
  trivial 



/- Informally, this is like "reasoning forward". From things you already know,
you're deriving a new thing, and then using that new thing later on.

This technique is very helpful to finish this problem, when you look at 
the proof state and feel stuck. Try puzzling through it: what new thing(s)
can you state and use?

-/



theorem bonus_challenge (p : Prop) : ¬ (p ↔ ¬ p) := by 
  intro hiff 
  eliminate hiff with h_left h_right
  have hnp : ¬ p 
  { intro hp 
    have hnp : ¬ p := h_left hp
    contradiction }
  have hp : p := h_right hnp 
  contradiction



/-

## TA notes for the bonus challenge

This is a loopy argument! It's a classic puzzle that trips people up. 
Notice the nested proof-by-contradiction.

The informal argument:
Suppose for the sake of contradiction that `p ↔ ¬ p`.
We thus know `p → ¬p` and `¬p → p`. 
Subproof: I claim that we also know `¬p`.
  Suppose `p` for the sake of contradiction. 
  Because `p → ¬p`, we know `¬p` by modus ponens -- contradiction!
Since we know `¬p → p` and `¬p`, we conclude `p` again by modus ponens.
Contradiction! 

You may want to approach this by cases. "If `p` is true, contradiction. 
And also if `p` is false, contradiction."
There is a way to do this, again using `have`:
  `have hem : p ∨ ¬p := em p`
Here, `em` stands for "excluded middle."
This is allowed, and a valid way of proving this statement, but not necessary.
You get an extra brownie point for *not* using it :) 

-/



/-

## HW4 hint

Just thinking informally, not in Lean:
if `2*a ≤ a + b`, then `a ≤ b`, 
since we can subtract `a` from both sides.

-/


end HW2
