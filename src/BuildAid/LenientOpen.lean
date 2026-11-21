import Lean.Elab.Command
import Lean.Elab.Open
import Lean.Elab.Tactic.BuiltinTactic
import Batteries.Tactic.OpenPrivate

/-!
Allows `open` commands to silently succeed if they cannot find the relevant namespace.

Hypothetically, they could warn instead.
-/

namespace BuildAid.LenientOpen

open Lean Elab OpenDecl

variable {m} [Monad m] [STWorld IO.RealWorld m] [MonadEnv m]
variable [MonadExceptOf Exception m] [MonadRef m] [AddErrorMessageContext m]
variable [AddMessageContext m] [MonadLiftT (ST IO.RealWorld) m] [MonadLog m]

private def addOpenDecl (decl : OpenDecl) : M (m:=m) Unit :=
  modify fun s => { s with openDecls := decl :: s.openDecls }

def elabOpenDecl [MonadOptions m] [MonadResolveName m] [MonadInfoTree m] (stx : TSyntax ``Parser.Command.openDecl) : m (List OpenDecl) := do
  StateRefT'.run' (s := { openDecls := (← getOpenDecls), currNamespace := (← getCurrNamespace) }) do
    match stx with
    | `(Parser.Command.openDecl| $nss*) =>
      for ns in nss do
        let resolved ← try resolveNamespace ns catch _ => continue
        Linter.checkAmbiguousOpen ns resolved
        for ns in resolved do
          addOpenDecl (OpenDecl.simple ns [])
          activateScoped ns
    | `(Parser.Command.openDecl| scoped $nss*) =>
      for ns in nss do
        let resolved ← try resolveNamespace ns catch _ => continue
        Linter.checkAmbiguousOpen ns resolved
        for ns in resolved do
          activateScoped ns
    | `(Parser.Command.openDecl| $ns ($ids*)) =>
      let nss ← try resolveNamespace ns catch _ => return (← get).openDecls
      Linter.checkAmbiguousOpen ns nss
      for idStx in ids do
        let declName ← try resolveNameUsingNamespacesCore nss idStx catch _ => continue
        if (← getInfoState).enabled then
          addConstInfo idStx declName
        addOpenDecl (OpenDecl.explicit idStx.getId declName)
    | `(Parser.Command.openDecl| $nsStx hiding $ids*) =>
      let ns ← try resolveUniqueNamespace nsStx catch _ => return (← get).openDecls
      Linter.checkAmbiguousOpen nsStx [ns]
      activateScoped ns
      for id in ids do
        let declName ← try resolveId ns id catch _ => continue
        if (← getInfoState).enabled then
          addConstInfo id declName
      let ids := ids.map (·.getId) |>.toList
      addOpenDecl (OpenDecl.simple ns ids)
    | `(Parser.Command.openDecl| $nsStx renaming $[$froms -> $tos],*) =>
      let ns ← try resolveUniqueNamespace nsStx catch _ => return (← get).openDecls
      Linter.checkAmbiguousOpen nsStx [ns]
      for («from», to) in froms.zip tos do
        let declName ← try resolveId ns «from» catch _ => continue
        if (← getInfoState).enabled then
          addConstInfo «from» declName
          addConstInfo to declName
        addOpenDecl (OpenDecl.explicit to.getId declName)
    | _ => throwUnsupportedSyntax
    return (← get).openDecls

open Command in
@[command_elab Lean.Parser.Command.open]
def elabOpen : CommandElab
  | `(open $decl:openDecl) => do
    let openDecls ← elabOpenDecl decl
    modifyScope fun scope => { scope with openDecls := openDecls }
  | _ => throwUnsupportedSyntax

open Term in
@[term_elab Lean.Parser.Term.open]
def elabOpenTerm : TermElab := fun stx expectedType? => do
  let `(open $decl in $e) := stx | throwUnsupportedSyntax
  try
    pushScope
    let openDecls ← elabOpenDecl decl
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      withSaveInfoContext <| elabTerm e expectedType?
  finally
    popScope

open Tactic in
@[tactic Lean.Parser.Tactic.open]
def evalOpenTactic : Tactic := fun stx => do
  let `(tactic| open $decl in $tac) := stx | throwUnsupportedSyntax
  try
    pushScope
    let openDecls ← elabOpenDecl decl
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
