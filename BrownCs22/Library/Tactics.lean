import Lean.Elab
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ApplyFun

open Lean Meta Elab Tactic Lean.Parser.Tactic

elab (name := split_goal) "split_goal " : tactic => withMainContext do 
  let tgt := (← instantiateMVars (← whnfR (← getMainTarget)))
  match tgt.and?, tgt.iff? with 
  | .none, .none => throwError "split_goal only applies to ∧ and ↔ goals"
  | _, _ => evalConstructor default


open private getElimNameInfo in evalCases in
elab (name := eliminate) "eliminate " tgts:(casesTarget,+) usingArg:((" using " ident)?)
  withArg:((" with " (colGt binderIdent)+)?) : tactic => do
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
