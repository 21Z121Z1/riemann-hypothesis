import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousLvMat
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsLv
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

namespace GlobalTheory.SphEis.Inhabitant

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n j m : ℕ} {J : Matrix (Fin n) (Fin n) E} {C D : Matrix (Fin n) (Fin j) E}
  {Z : Matrix (Fin n) (Fin m) E} {J₀ : Matrix (Fin m) (Fin m) E}

theorem existsUnique_isLv (f : Fr σ J C D Z J₀) :
    ∃ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv ∧ Function.Injective lv ∧
      ∀ lv', IsLv σ J C D Z lv' → lv' = lv :=
  ⟨SphEisModel.lv f, SphEisModel.isLv_lv f, SphEisModel.isLv_injective f (SphEisModel.isLv_lv f),
    fun _ h => SphEisModel.isLv_unique f h (SphEisModel.isLv_lv f)⟩

theorem all_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 3) (Fin 3) E) (C D Z : Matrix (Fin 3) (Fin 1) E) (J₀ : Matrix (Fin 1) (Fin 1) E)
    (l : GL (Fin 1) (AF F ⊗[F] E) →* GAd σ J) (u : GAd σ J) (c : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)),
    Fr σ J C D Z J₀ ∧ IsLv σ J C D Z l ∧ Function.Injective l ∧ Crd σ J C D Z J₀ u 1 c ∧ u ∈ fixG σ J C :=
  SphEisModel.inhabited

end GlobalTheory.SphEis.Inhabitant

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Imports
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

def RealMatch.Tied (ρ : RealMatch W) : Prop :=
  ∀ (i j : Fin D.R.m) (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1))))
    (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∀ (t : T) ωA ωB Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
      ωA ωB Pi rf rl p p' →
    ∀ (B : Frames G) n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
      HasFlip B t ρ i j n Φ τ τ' → ∃ c : ℂ, ∀ a b, ρ.Matched (t := t) (i := i) (j := j) a b →
        p (datumA W (tensT W a τ)) = c • p' (datumB W (tensT W b τ'))

end GlobalTheory.FunObj

end
end

