import Mathlib
import Formalism.PeriodIntegrals.Bundle0032
import Formalism.LocalToGlobal.Columns.Bundle0008

-- bundled from Formalism.PeriodIntegrals.NormRepChange
section
noncomputable section

open scoped Classical

namespace PI.NormRepChange

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word)

def NormRepMove : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ t : TermsOf D u' F0 Λ, IsRel Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F t →
      ∀ F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E),
        Formalism.L2.SG.TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₁ → AdmWit Λ (gS D) (lf D F0) F₁ 1 →
        Formalism.L2.SG.TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₂ → AdmWit Λ (gS D) (lf D F0) F₂ 1 →
        ∀ w : Point D.host.E (D.R.rS + 1), IsInCell (ZhatOM (ZhatL (lf D F0) F₁)) w →
          ∃ A B : MatR D, IsLoUni A ∧ IsUpUni B ∧
            ZhatOM (ZhatL (lf D F0) F₂) = A * ZhatOM (ZhatL (lf D F0) F₁) * B ∧ psiInf (gS D) (sgLo A + sgUp B) = 1

end PI.NormRepChange
end
end

-- bundled from Formalism.PeriodIntegrals.XgCTieBr
section
namespace PI

def XgCTieBr : Prop :=
  PI.XgNamed.BrauerSplit →
  ∀ {X : Formalism.L2.Col.Fields} (Pr : Formalism.L2.Col.Primes X) {m : ℕ} (Ch : Formalism.L2.Col.Chars X Pr m) (r : ℕ)
    [∀ i, Fact (Pr.g i).Prime] (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ)
    (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i)),
    Formalism.L2.Col.XgCTie Pr Ch r σ teich ζ

end PI
end

