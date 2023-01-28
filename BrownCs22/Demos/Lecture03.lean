import BrownCs22.Library.Defs
import BrownCs22.Library.TruthTables

/-

Lean is a language that we will be using in CS22 this year.

If you're in this class, you've most likely used a programming language before.
Lean is a programming language too. But we'll be using it for a different reason:
Lean lets us state *propositions*, write *proofs* of these propositions, and *check*
automatically that these proofs are correct.

Some basic Lean syntax:

* Block comments, like this one, are written as /- ... -/.
* Line comments begin with -- 
* If a file imports other files, this appears at the very top of the file.
  You shouldn't change these imports!


Remember from Lecture 2, 
the `#check` command asks Lean to tell us "what kind of thing" something is.
(This will be very useful for us!)

For example, `1` is a natural number (`ℕ`),
and `1 + 1 = 2` is a proposition (`Prop`).

-/

#check 1

#check 1 + 1 = 2


/-

We've just introduced *propositional formulas*,
which are built out of *atoms* and *connectives*.

In normal math, it's common for us to introduce some atoms by writing
"let p, q, and r be propositions".

In Lean, we write:

-/

variable (p q r : Prop)

#check p 
#check p ∧ q 
#check p ∧ q → r 
#check p ∨ q ∨ p ∧ r ∧ ¬ (p ∧ q ∧ r) 

/-

A few things to note here.

* In the third `#check` above, if you hover over the output in the infoview,
  you can see how this formula is parenthesized!

* Those unicode symbols are input using \ . To write the third line I typed
  `p \and q \to r`. But there are lots of variants. 
  They usually match the LaTeX command.
  You can hover over a symbol to see how it was typed. Here's a useful list:

  * `∧`: and, wedge
  * `∨`: or, vee 
  * `¬`: not, neg
  * `→`: to, imp, rightarrow 
  * `↔`: iff
  * `ℕ`: N, nat 
  * `ℤ`: Z, int
  * `∀`: all, forall
  * `∃`: ex, exist

Try it out: write down some propositional formulas.
If you want more atoms than `p`, `q`, and `r`, you can write a new line
`variable (s t u : Prop)` (using whatever letters you would like).

-/



#truth_table p ∧ q ∨ r
