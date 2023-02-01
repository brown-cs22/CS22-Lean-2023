import BrownCs22.Library.Tactics 

/-

# Welcome to the Lean section of HW1!

Some general guidelines, before we get started.

* When you're doing Lean homework assignments, including this one,
  do *not* edit any of the `import` statements above the 
  opening comment. This will most likely break our autograder.

* Speaking of: when you submit this on Gradescope, you'll 
  upload it to a separate assignment than the PDF with your other
  solutions. That's because we can autograde Lean, but not normal 
  math! In the future, we hope to let you upload both files to the 
  same assignment. But autograders are tricky and we haven't 
  figured it out yet.

* Your goal in this assignment is to replace the `sorry`s in each 
  part with completed proofs. If you can't finish a problem and 
  want to submit the assignment half-complete, that's fine -- 
  but try to "finish" the proof by putting in more `sorry`s.

  For example, if the original problem looks like this:
-/

theorem example_1 (p : Prop) : p → p → p := by 
  sorry 

/- 
  and you work on it, but get stuck at this stage and can't finish:

theorem example_1 (p : Prop) : p → p → p := by 
  intro hp1
  intro hp2

  then you should "finish" it by writing `sorry` again:
-/

theorem example_1' (p : Prop) : p → p → p := by 
  intro hp1
  intro hp2
  sorry

/- 
  Notice that, with the `sorry`, `example_1` is highlighted in yellow.
  Without the sorry, there is a red error message.
  It's safest to submit a file with no red error messages,
  to avoid any unexpected autograder failures.
  The autograder will give you points if all of the warnings and errors are gone.

Let's get started!
-/

variable (p q r s : Prop)

/-

## Problem 1

Fill in the `sorry` in the proof below.
The elimination and introduction rules we talked about in Lecture 4
will be very helpful here!


-/

/- 3 points -/
theorem problem_1 : (p ∧ q ∧ r) → (p ∧ r) := by 
  sorry



/-

## Problem 2

Consider what the theorem below is saying! 
"If the truth of `p` implies the falsity of `q`,
 then `p` and `q` cannot both be true."

Does that seem like a reasonable statement? 
What do the truth tables of `p → ¬ q` and `¬ (p ∧ q)` look like?
(You do not need to write an answer, but think about it for a moment.
 Try the `#truth_table` command if you want.)


Again, your task is to fill in the `sorry` below to prove this statement.

-/

/- 3 points -/
theorem problem_2 : (p → ¬ q) → ¬ (p ∧ q) := by 
  sorry


/-
## Problem 3

This one's a little tricky! Let's reason through it in natural language.

We want to prove that, if we know `((p ∨ q) ∧ (p → r) ∧ (q → s))`,
then we know `r ∨ s`. 
So suppose that we know `((p ∨ q) ∧ (p → r) ∧ (q → s))`.
Our goal is to show that `r ∨ s` follows.

From that long statement, we know three facts: `p ∨ q`, `p → r`, and `q → s`. 
We'll reason by cases on `p ∨ q`.

First, if we know `p`, then we know `r`, because `p → r`. 
And if we know `r` then we know `r ∨ s`. 

Second, if we know `q`, then we know `s`, because `q → s`. 
And if we know `s` then we know `r ∨ s`.

That completes our proof!

Your task: translate this argument to Lean.

-/

/- 4 points -/
theorem problem_3 : ((p ∨ q) ∧ (p → r) ∧ (q → s)) → (r ∨ s) := by 
  sorry