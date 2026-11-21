import Lean.Elab.Command
import Lean.Elab.Tactic.BuiltinTactic
import Batteries.Tactic.OpenPrivate

/-!
`open` that skips what does not resolve.

Import minimization can drop the module that made an opened namespace (or an explicitly opened
name) exist when nothing from it is used, and then `open` fails. These elaborators take precedence
over the builtin ones for every form of `open` (command, `open ... in` for terms and tactics) and
over Batteries' `open private`.

They follow the builtin elaborators exactly, except that the declaration is elaborated piece by piece
with the builtin `elabOpenDecl`, threading the open declarations through as Lean's own loop does, and
a piece that throws is skipped:

* `open A B`, `open scoped A B`: one piece per namespace, in order, so `B` may resolve through `A`.
* `open A (x y)`: one piece per name.
* `open A renaming x → y, ...`: one piece per renaming.
* `open A hiding x y`: one piece, since splitting it would change what is hidden. Hidden names that
  do not resolve are dropped first (each is tried with the environment restored afterwards).
* `open private x y ... from M`: one `open private` per name.

Anything a file actually uses from something skipped still fails, as an unknown identifier.
-/

namespace BuildAid.LenientOpen

open Lean Elab

-- The instances `elabOpenDecl` needs (`Lean/Elab/Open.lean`), plus `MonadFinally` and
-- `MonadQuotation` for the splitting.
variable {m : Type → Type} [Monad m] [STWorld IO.RealWorld m] [MonadEnv m]
  [MonadExceptOf Exception m] [MonadRef m] [AddErrorMessageContext m]
  [AddMessageContext m] [MonadLiftT (ST IO.RealWorld) m] [MonadLog m]
  [MonadOptions m] [MonadResolveName m] [MonadInfoTree m] [MonadFinally m] [MonadQuotation m]

/--
Elaborates `decl` like `elabOpenDecl`, but piece by piece, skipping pieces that fail.
`withOpenDecls ds x` runs `x` with `ds` as the current open declarations.
-/
def elabOpenDeclLenient (withOpenDecls : List OpenDecl → m (List OpenDecl) → m (List OpenDecl))
    (decl : TSyntax ``Parser.Command.openDecl) : m (List OpenDecl) := do
  let attempt (acc : List OpenDecl) (piece : TSyntax ``Parser.Command.openDecl) :
      m (Option (List OpenDecl)) := do
    try
      return some (← withOpenDecls acc (elabOpenDecl piece))
    catch _ =>
      return none
  let mut acc ← getOpenDecls
  match decl with
  | `(Parser.Command.openDecl| $nss*) =>
    for ns in nss do
      if let some ds ← attempt acc (← `(Parser.Command.openDecl| $ns:ident)) then acc := ds
  | `(Parser.Command.openDecl| scoped $nss*) =>
    for ns in nss do
      if let some ds ← attempt acc (← `(Parser.Command.openDecl| scoped $ns:ident)) then acc := ds
  | `(Parser.Command.openDecl| $ns ($ids*)) =>
    for id in ids do
      if let some ds ← attempt acc (← `(Parser.Command.openDecl| $ns ($id))) then acc := ds
  | `(Parser.Command.openDecl| $ns hiding $ids*) =>
    let ok ← ids.filterM fun id => do
      let piece ← `(Parser.Command.openDecl| $ns hiding $id)
      return (← withoutModifyingEnv (attempt acc piece)).isSome
    let piece ← if ok.isEmpty then `(Parser.Command.openDecl| $ns:ident)
      else `(Parser.Command.openDecl| $ns hiding $ok*)
    if let some ds ← attempt acc piece then acc := ds
  | `(Parser.Command.openDecl| $ns renaming $[$froms -> $tos],*) =>
    for («from», to) in froms.zip tos do
      let piece ← `(Parser.Command.openDecl| $ns renaming $«from» → $to)
      if let some ds ← attempt acc piece then acc := ds
  | _ => acc ← elabOpenDecl decl
  return acc

open Command in
/-- `open`, as `Lean.Elab.Command.elabOpen` but with `elabOpenDeclLenient`. -/
@[command_elab Lean.Parser.Command.open]
def elabOpen : CommandElab
  | `(open $decl:openDecl) => do
    let openDecls ← elabOpenDeclLenient
      (fun ds x => withScope (fun scope => { scope with openDecls := ds }) x) decl
    modifyScope fun scope => { scope with openDecls := openDecls }
  | _ => throwUnsupportedSyntax

open Term in
/-- `open ... in` for terms, as `Lean.Elab.Term.elabOpen` but with `elabOpenDeclLenient`. -/
@[term_elab Lean.Parser.Term.open]
def elabOpenTerm : TermElab := fun stx expectedType? => do
  let `(open $decl in $e) := stx | throwUnsupportedSyntax
  try
    pushScope
    let openDecls ← elabOpenDeclLenient
      (fun ds x => withTheReader Core.Context (fun ctx => { ctx with openDecls := ds }) x) decl
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      withSaveInfoContext <| elabTerm e expectedType?
  finally
    popScope

open Tactic in
/-- `open ... in` for tactics, as `Lean.Elab.Tactic.evalOpen` but with `elabOpenDeclLenient`. -/
@[tactic Lean.Parser.Tactic.open]
def evalOpenTactic : Tactic := fun stx => do
  let `(tactic| open $decl in $tac) := stx | throwUnsupportedSyntax
  try
    pushScope
    let openDecls ← elabOpenDeclLenient
      (fun ds x => withTheReader Core.Context (fun ctx => { ctx with openDecls := ds }) x) decl
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      evalTactic tac
  finally
    popScope

open Command in
/-- Batteries' `open private`, one name at a time, skipping names that fail. -/
@[command_elab Lean.Elab.Command.openPrivate]
def elabOpenPrivate : CommandElab
  | `(open private $ids* $[in $tgts*]? $[from $mods*]?) => do
    for id in ids do
      let piece ← `(open private $id $[in $tgts*]? $[from $mods*]?)
      try
        Lean.Elab.Command.elabOpenPrivate piece
      catch _ =>
        pure ()
  | _ => throwUnsupportedSyntax

end BuildAid.LenientOpen
