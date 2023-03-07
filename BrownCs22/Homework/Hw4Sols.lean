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
  -- A good first step is always to unfold definitions! After these lines, the tactic state shows
  -- the internal definition of `Injective` and `f`, which will help with the proof.
  dsimp [Injective] 
  dsimp [f] -- Make sure you can read, understand, and explain the rewritten goal before continuing
  -- We now have a goal with 2 universal quantifiers and an implication. This will require 3 intro statements:
  -- make sure to check that everything is named what you want it to be!
  intro a1
  intro a2
  intro heq
  -- Now, our goal is a mathematical statement that can be algebraically proved from our hypotheses.
  linarith

/- 2 points -/
theorem problem_2 : Surjective f := by 
  -- As before, let's start by unfolding `Surjective` and `f`.
  dsimp [Surjective] 
  dsimp [f] -- Make sure you can read, understand, and explain the rewritten goal before continuing
  -- We have a universal quantifier and an existential quantifier. Let's start by introducing the universal:
  intro b
  -- We now have an ∃ statement. Because we are working in the rational numbers, we can directly calculate 
  -- a value for a that makes the statement true, and "plug" that value into `existsi`: 
  existsi (b - 6) / 2        -- b / 2 - 3 also works, if you come up with that instead
  -- From here, just algebra!
  linarith

/-

## Notes for 1 and 2

Think about the *logical forms* of injectivity and surjectivity. 

Injectivity says: if two things `a, b` in the domain map to the same value in the codomain,
then `a` and `b` must be the same. 
This is a ∀, ∀, → structure.

Surjectivity says: everything in the codomain gets mapped to by something in the domain. 
This is a ∀, ∃ structure.


If you `dsimp [f]` before `dsimp [Surjective]`, you might see some funny 
syntax. This syntax is for an "anonymous function" (if you're familiar with that concept).
Try starting by unfolding surjectivity.

-/


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
  -- As mentioned above, dsimp is almost always useful, and is a good first step!
  dsimp [Reflexive]
  dsimp [R]
  dsimp [dvd] -- You should probably also dsimp `dvd` as they did on previous homework
  -- Now, we have a ∀ statement and an ∃ statement, so we know `intro` and `existsi` will have to show up somewhere.
  -- But what witness should we introduce? Note that after simplifying, the math part of our goal is `x = x * c`. 
  -- c = 1 satisfies this statement.  
  intro x
  exists 1
  linarith

/-

## Notes for problem 3 

Again, unfolding `R` before `Reflexive` might expose some confusing syntax.



-/

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
  -- No surprises here - time to `dsimp`:
  dsimp [Transitive]
  dsimp [R] 
  -- This is a good time to look at the Infoview to get the feel for what you are being asked to do: unfolding
  -- `dvd` can make things a bit cluttered.

  -- There's quite a bit going on here. Looking at the goal, we can see that there are 3 universal quantifiers, 
  -- and 2 implications. Hovering over the arrows in the Infoview shows that the left arrow (the one with only x | y on the side)
  -- is the outermost of the implications, so that will be the first one introduced after the quantifiers.
  dsimp [dvd] -- Be careful - the term `c` shows up in 3 separate lines in the Infoview, but they are not all the same `c`!
  intro x
  intro y
  intro z
  intro hxy
  intro hyz 
  -- Here, you should check to make sure that everything is named how you expect it to be. If they accidentally
  -- named a hypothesis with the wrong letters, it will cause extra confusion later.
  
  -- Looking at the Infoview, it looks like `x * something₁ = y` and `y * something₂ = z`. Therefore, the main goal of
  -- our proof is to conclude that `x * (something₁ * something₂) = z`. In order to do that, we will need to use
  -- `eliminate` on `hxy` and `hyz` to extract the `something`s, and then use `existsi` to introduce 
  -- `(something₁ * something₂)` as our witness:
  eliminate hxy with c₁ hc₁
  eliminate hyz with c₂ hc₂
  existsi c₁ * c₂
  -- Now, looking at the statements in the Infoview, this looks like a purely algebraic proof! However, `linarith` will not
  -- work here, since we are multiplying variables together. Therefore, we can use `polyrith` to make sure that the goal
  -- is provable:

  -- polyrith

  -- `polyrith` will complete the proof, but will also generate the following message in the Infoview:
  -- `Try this: linear_combination c₂ * hc₁ + hc₂`
  -- Using this in place of polyrith will also complete the proof, and it is preferred that you do such
  -- (for a variety of reasons: if you are interested, you can hover over an uncommented call to polyrith to 
  --  see its documentation - do you notice anything going on that might not be good to keep in a final product?)
  linear_combination c₂ * hc₁ + hc₂
  
/-

## Notes for problem 4

The `polyrith` step is kind of funny: a tactic is suggesting another tactic!
If you see an error about python when trying to use `polyrith`,
you did not follow the directions to create a new Gitpod instance.

Fun fact: `linear_combination` and `polyrith` were both written by Brown undergrads,
Abby Goldberg and Dhruv Bhatia, who took cs1951x "Formal Proof and Verification"!

-/

end HW4
