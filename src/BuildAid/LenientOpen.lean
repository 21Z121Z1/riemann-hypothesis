import Lean.Elab.Command
import Lean.Elab.Tactic.BuiltinTactic

/-!
`open` that ignores namespaces which do not exist.

Import minimization can drop the module that made an opened namespace exist even though nothing in
the namespace is used, and then `open` fails with "unknown namespace". These elaborators take
precedence over the builtin ones for `open` (command, term and tactic forms). Each drops the
namespaces that do not resolve and re-elaborates the rest; once every namespace resolves it throws
`unsupportedSyntax`, so the builtin elaborator does the actual work. Only the plain and `scoped`
forms are filtered; `open X (a b)`, `hiding` and `renaming` go to the builtin elaborator unchanged.
-/

namespace BuildAid.LenientOpen

open Lean Elab

/-- The `openDecl` with unresolvable namespaces removed, `none` if nothing needs removing, or
`some none` if nothing is left. -/
def filterOpenDecl {m : Type → Type} [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m]
    [MonadExcept Exception m] (decl : Syntax) : m (Option (Option Syntax)) := do
  let k := decl.getKind
  -- `openSimple`: `$nss*`; `openScoped`: `scoped $nss*`
  let idx? := if k == ``Parser.Command.openSimple then some 0
    else if k == ``Parser.Command.openScoped then some 1 else none
  let some idx := idx? | return none
  let ids := decl[idx].getArgs
  let keep ← ids.filterM fun id => do
    try
      discard <| resolveNamespace ⟨id⟩
      return true
    catch _ =>
      return false
  if keep.size == ids.size then return none
  if keep.isEmpty then return some none
  return some (some (decl.setArg idx (mkNullNode keep)))

open Command in
@[command_elab Lean.Parser.Command.open]
def elabOpen : CommandElab := fun stx => do
  match ← filterOpenDecl stx[1] with
  | none => throwUnsupportedSyntax
  | some none => pure ()
  | some (some decl) => elabCommand (stx.setArg 1 decl)

open Term in
@[term_elab Lean.Parser.Term.open]
def elabOpenTerm : TermElab := fun stx expectedType? => do
  -- `open $decl in $e`
  match ← filterOpenDecl stx[1] with
  | none => throwUnsupportedSyntax
  | some none => elabTerm stx[3] expectedType?
  | some (some decl) => elabTerm (stx.setArg 1 decl) expectedType?

open Tactic in
@[tactic Lean.Parser.Tactic.open]
def evalOpenTactic : Tactic := fun stx => do
  -- `open $decl in $tac`
  match ← filterOpenDecl stx[1] with
  | none => throwUnsupportedSyntax
  | some none => evalTactic stx[3]
  | some (some decl) => evalTactic (stx.setArg 1 decl)

end BuildAid.LenientOpen
