import Lean.Elab
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Existsi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Lean hiding Rat mkRat
open Meta Elab Tactic Lean.Parser.Tactic

elab (name := split_goal) "split_goal " : tactic => withMainContext do 
  let tgt := (← instantiateMVars (← whnfR (← getMainTarget)))
  match tgt.and?, tgt.iff? with 
  | .none, .none => throwError "split_goal only applies to ∧ and ↔ goals"
  | _, _ => evalConstructor default


open private getElimNameInfo in evalCases in
elab (name := eliminate) "eliminate " tgts:(casesTarget,+) usingArg:((" using " ident)?)
  withArg:((" with " (colGt binderIdent)+)?) : tactic => focus do
  let targets ← elabCasesTargets tgts.1.getSepArgs
  let g ← getMainGoal
  g.withContext do
    let elimInfo ← getElimNameInfo usingArg targets (induction := false)
    let targets ← addImplicitTargets elimInfo targets
    let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM (instantiateMVars elimArgs[·]!)
    let motive := elimArgs[elimInfo.motivePos]!
    let g ← generalizeTargetsEq g (← inferType motive) targets
    let (targetsNew, g) ← g.introN targets.size
    g.withContext do
      ElimApp.setMotiveArg g motive.mvarId! targetsNew
      g.assign result.elimApp
      let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
         (numEqs := targets.size) (toClear := targetsNew)
      setGoals subgoals.toList

macro "reflexivity" : tactic => `(tactic |rfl)

section 

open Lean.Meta Qq Lean.Elab Term
open Lean.Parser.Tactic Mathlib.Meta.NormNum

/--
Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹` and `^`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions.
-/
elab (name := numbers) "numbers" loc:(location ?) : tactic =>
  elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)
end 

macro "set_simplify" : tactic => `(tactic | simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_diff] at *)