/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
-- import Math2001.Library.Division
import Mathlib.Data.Int.Basic

/-- Two integers are congruent modulo `n`, if their difference is a multiple of `n`. -/
def BrownCs22.Int.ModEq (n a b : ℤ) : Prop := n ∣ a - b

notation:50 a " ≡ " b " [ZMOD " n "]" => BrownCs22.Int.ModEq n a b
