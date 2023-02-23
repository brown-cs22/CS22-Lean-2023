import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Polyrith

-- don't change these lines
namespace HW4
open Dvd Function
set_option linter.unusedVariables false

/-

# Welcome to the Lean section of HW4!

Today we'll explore a little bit about functions and relations in Lean.

In particular, we'll think about the *logical form* 
of some of the function and relation properties we saw,
like injectivity and surjectivity. 


## Defining functions in Lean

Lean, believe it or not, is a programming language like Python, Pyret,
ReasonML, or whatever language you're familiar with. 
(Of the Brown intro course languages, it's probably closest to ReasonML.)

This means we can define functions and evaluate them.
The below defines a function named `my_quadratic` that takes as input 
an integer `x` and produces another integer.
-/

def my_quadratic (x : ℤ) : ℤ :=
  4*x^2 + 55*x - 10 

#check my_quadratic 

/-
We can evaluate it by using `#eval`.

Unlike many languages like Python, we don't need parentheses 
if the argument is a single integer -- 
we *can* write `my_quadratic(12)`, but we don't need to.
If we want to evaluate it on a more complicated expression, 
we do need parentheses around the argument.
-/

#eval my_quadratic 12 
#eval my_quadratic (10 + 2)

/-

What makes Lean more exciting than these other languages? 
Not only can we define functions, but we can state *properties* 
of these functions, and *prove* that these properties hold.

How convenient: we just learned about a lot of function 
and relation properties in class :) 


A side note: in class, we said that functions and relations were 
sets of ordered pairs, defined by their *graph*:
`f(x) = y` if and only if `(x, y) ∈ G(f)`.
But we also (in lecture 9) mentioned that it was a *choice* of ours 
to take sets as the "primary" concept and to define functions and relations 
in terms of sets. Lean, like most programming languages, 
takes the opposite approach: functions are a "primary" concept, and 
sets are defined in terms of functions.

Confusing? Don't worry about it too much: if we're interested in properties 
of functions and relations, and in using these ideas, it doesn't really 
matter how they're defined. It matters what they can do. And Lean functions 
can do exactly the same things as our "sets of pairs" functions from class.




## Problems 1 and 2

We'll work with some pretty simple functions today. 
Here's one, a *linear* function on the rational numbers, called `f`.

(We call `f` linear because its graph is a straight line, or equivalently,
because it doesn't multiply variables together. 
`g x = x^2` would not be linear.)

-/

def f (x : ℚ) : ℚ := 2*x + 6

#eval f 5
#eval f (1/3)

/- 

Let's prove that `f` is injective and surjective. 

Some tactics to remember:

* `dsimp` unfolds definitions. You can `dsimp [Injective]` 
  to expand what it means for `f` to be injective. 
  (This is probably a good place to start!)
  You can `dsimp [f]` to change `f x` into `2*x + 6`.

* `linarith` will do basic arithmetic for you, using facts 
  that appear in your hypotheses.
  In particular, `linarith` will reason about linear functions. 
  It will often get confused, or fail to prove things, 
  if it sees variables multiplied together.
  
-/

/- 2 points -/
theorem problem_1 : Injective f := by 
  sorry

/- 2 points -/
theorem problem_2 : Surjective f := by 
  sorry


/-

## Problem 3

We can talk about relations in Lean as well.
Again, the relations we see will be mostly mathematical,
but there are lots of interesting relations on programming data types:
for instance, the relation `is_prefix_of` on strings or lists.

Here's a mathematical relation on `ℤ`: `R a b` holds when `a` divides `b`.
-/

def R (a b : ℤ) : Prop := 
  a ∣ b

/- 

When we talked about relation properties in class, we described them 
in terms of "arrows" going out of and into the domain and codomain. 
But we also saw the logical form of these properties. Lean, unsurprisingly,
knows about these logical forms. To show that `R` is reflexive, 
we'll need to prove `∀ x : ℤ, R x x`: 
"every integer is related to itself by `R`."

Let's show that this relation is reflexive. Like before, 
`dsimp [Reflexive]` and `dsimp [R]` might be useful!


-/

/- 2 points -/
theorem problem_3 : Reflexive R := by
  sorry

/- 

## Problem 4 

Finally, let's also show that `R` is transitive. 
(Why did we skip "symmetric"? Think about that one for a sec!)

At some point in your proof, you might end up with a statement that 
looks like it could be solved by `linarith`, but can't. 
First, check that the statement should really be provable. 
If you're convinced it is -- are there variables multiplied together? 

There's another tactic (actually, two tactics) that can help out. 

`polyrith` is a very expensive version of `linarith` that only works 
on equalities, but handles nonlinear expressions. 
Because it can sometimes be slow, when it succeeds, 
it prints a message in the tactic state to the right. 
The message suggests to try using a tactic called `linear_combination`. 
Copy and paste this message, replacing your call to `polyrith`, 
and it should magically work.

(We'll talk more in class about linear combinations very soon -- 
this is the same concept showing up in a different context.)

-/

/- 3 points -/
theorem problem_4 : Transitive R := by 
  sorry
  
  

end HW4