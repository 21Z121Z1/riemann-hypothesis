import Lean.Elab.Declaration

/-!
`example` that warns instead of failing.

Import minimization cannot see what an `example` uses: examples are elaborated and then discarded,
so nothing they reference reaches the olean. If a file's imports were narrowed below what one of its
examples needs, the example fails although every declaration in the file is fine.

This elaborator takes precedence over the builtin one for `example` declarations (other
declarations go to the builtin elaborator unchanged). It runs the builtin `elabDeclaration`
synchronously and without incrementality, so that every message ends up in the command's message
log rather than in an asynchronous snapshot task. If that produces errors, they are reported as
warnings, together with a warning that a necessary import may have been removed.
-/

namespace BuildAid.LenientExample

open Lean Elab Command

/-- `example`, as `Lean.Elab.Command.elabDeclaration`, with its errors downgraded to warnings. -/
@[command_elab Lean.Parser.Command.declaration]
def elabExample : CommandElab := fun stx => do
  unless stx[1].getKind == ``Lean.Parser.Command.example do throwUnsupportedSyntax
  let saved := (← get).messages
  modify fun s => { s with messages := {} }
  try
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
      withoutCommandIncrementality true do
        elabDeclaration stx
  catch ex =>
    logException ex
  let new := (← get).messages
  if new.hasErrors then
    modify fun s => { s with messages := saved ++ new.errorsToWarnings }
    logWarningAt stx[1][0] m!"this `example` failed to elaborate (its errors are shown as \
      warnings); a necessary import may have been removed"
  else
    modify fun s => { s with messages := saved ++ new }

end BuildAid.LenientExample
