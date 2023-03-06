/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import BrownCs22.Library.ModEq.Lemmas
import BrownCs22.Library.ModSubst.Basic

open Lean Elab Tactic

-- syntax (name := ModRelSyntax) "mod_subst" " [" term,* "] " : tactic

elab_rules : tactic | `(tactic| mod_subst [$t,*]) => do
  liftMetaTactic <|
    Lean.MVarId.Rel `mod_rules t.getElems.toList
      "cannot prove this by 'substituting' the listed relationships"

-- macro_rules | `(tactic| mod_subst [$t,*]) => `(tactic| mod_rel [$t,*])

syntax (name := ModExtraSyntax) "mod_extra" : tactic

elab_rules : tactic | `(tactic| mod_extra) => do
  liftMetaTactic <|
    Lean.MVarId.Rel `mod_extra []
      "the two sides don't differ by a neutral quantity for the relation"

macro_rules | `(tactic| extra) => `(tactic| mod_extra)

attribute [mod_rules]
  BrownCs22.Int.ModEq.refl
  -- hopefully, the order here prioritizes `add_right` and `add_left` over `add`
  BrownCs22.Int.ModEq.add_right BrownCs22.Int.ModEq.add_left BrownCs22.Int.ModEq.add
  BrownCs22.Int.ModEq.sub_right BrownCs22.Int.ModEq.sub_left BrownCs22.Int.ModEq.sub
  BrownCs22.Int.ModEq.mul_right BrownCs22.Int.ModEq.mul_left BrownCs22.Int.ModEq.mul
  BrownCs22.Int.ModEq.neg BrownCs22.Int.ModEq.pow

-- attribute [mod_extra]
--   Int.modEq_fac_zero Int.modEq_fac_zero' Int.modEq_zero_fac Int.modEq_zero_fac'
--   Int.modEq_add_fac_self Int.modEq_add_fac_self' Int.modEq_add_fac_self'' Int.modEq_add_fac_self'''
--   Int.modEq_sub_fac_self Int.modEq_sub_fac_self' Int.modEq_sub_fac_self'' Int.modEq_sub_fac_self'''
--   Int.modEq_add_fac_self_symm Int.modEq_add_fac_self_symm' Int.modEq_add_fac_self_symm'' Int.modEq_add_fac_self_symm'''
--   Int.modEq_sub_fac_self_symm Int.modEq_sub_fac_self_symm' Int.modEq_sub_fac_self_symm'' Int.modEq_sub_fac_self_symm'''
--   Int.ModEq.add_right Int.ModEq.add_left
--   Int.ModEq.sub_right Int.ModEq.sub_left
--   Int.ModEq.refl
