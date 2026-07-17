/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Lean.Meta.Hint
public import Mathlib.Init

/-!
# The `haveI`/`letI` linter

This is a local copy of the linter introduced in
https://github.com/leanprover-community/mathlib4/pull/41657. It can be removed once that PR is
available in this project's mathlib dependency.

The linter flags uses of the `haveI` or `letI` tactic while the main goal is a proposition. In Lean
4, ordinary `have` and `let` declarations are already available to instance synthesis; `haveI` and
`letI` only inline their values, which is immaterial in proofs by proof irrelevance.
-/

meta section

open Lean Elab Meta Parser.Term Tactic Linter

namespace QuillenSuslin.Linter.HaveLetI

/-- Enable warnings for `haveI` and `letI` tactics used in proofs of propositions. -/
public register_option linter.style.haveILetI : Bool := {
  defValue := true
  descr := "enable the `haveILetI` linter"
}

/-- Run `haveI`, suggesting `have` when the main goal is a proposition. -/
def runHaveI (tk : Syntax) (c : TSyntax ``letConfig) (d : TSyntax ``letDecl) : TacticM Unit := do
  evalTactic (← `(tactic| haveI $c:letConfig $d:letDecl))
  if getLinterValue linter.style.haveILetI (← getLinterOptions) then
    withMainContext do
    if ← isProp (← getMainTarget) then
      let suggs ← Hint.mkSuggestionsMessage #[{toTryThisSuggestion := "have"}] tk none false
      logWarning m!"Try this: {suggs}\n\n\
        The goal is a proposition, so `have` is preferred over `haveI`.\n\
        The difference between `have` and `haveI` is that `haveI` inlines the value.\n\
        But this is not relevant for proofs because of proof irrelevance."

/-- `haveI` with a warning when its inlining behavior is immaterial. -/
elab tk:"haveI" c:letConfig d:letDecl : tactic => runHaveI tk c d

/-- Run `letI`, suggesting `let` when the main goal is a proposition. -/
def runLetI (tk : Syntax) (c : TSyntax ``letConfig) (d : TSyntax ``letDecl) : TacticM Unit := do
  evalTactic (← `(tactic| letI $c:letConfig $d:letDecl))
  if getLinterValue linter.style.haveILetI (← getLinterOptions) then
    withMainContext do
    if ← isProp (← getMainTarget) then
      let suggs ← Hint.mkSuggestionsMessage #[{toTryThisSuggestion := "let"}] tk none false
      logWarning m!"Try this: {suggs}\n\n\
        The goal is a proposition, so `let` is preferred over `letI`.\n\
        The difference between `let` and `letI` is that `letI` inlines the value.\n\
        But this is not relevant for proofs because of proof irrelevance."

/-- `letI` with a warning when its inlining behavior is immaterial. -/
elab tk:"letI" c:letConfig d:letDecl : tactic => runLetI tk c d

end QuillenSuslin.Linter.HaveLetI
