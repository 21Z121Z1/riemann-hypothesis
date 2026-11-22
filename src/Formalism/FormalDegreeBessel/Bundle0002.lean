import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg
import Formalism.FormalDegreeBessel.StatementDS

-- bundled from Formalism.FormalDegreeBessel.FinalBF
section
namespace Formalism.QuantumDeterminants

theorem bigCellMem : BigCellMem := big_cell_mem_holds
theorem bigCellZhat : BigCellZhat := big_cell_coordinate_holds
theorem bigCellMinors : BigCellMinors := big_cell_minors_holds

end Formalism.QuantumDeterminants
end

-- bundled from Formalism.FormalDegreeBessel.FinalG
section
namespace Formalism.QuantumDeterminants

theorem uHGroup : UHGroup := unitary_group_holds
theorem uHConj : UHConj := unitary_conjugation_holds
theorem hpkFacts : HpkFacts := hermitian_pos_facts_hold
theorem nSubgroup : NSubgroup := unipotent_subgroup_holds
theorem ellAdd : EllAdd := length_additive_holds
theorem psiChar : PsiChar := additive_character_holds
theorem uWNormal : UWNormal := unitary_weyl_normal_holds
theorem sGroup : SGroup := symmetric_group_holds
theorem dInv : DInv := diagonal_inverse_holds
theorem gInv : GInv := group_inverse_holds
theorem gFactor : GFactor := group_factorization_holds
theorem revCS : RevCS := reverse_cauchy_schwarz_holds
theorem gGram : GGram := group_gram_holds
theorem gNonneg : GNonneg := gNonneg_of group_gram_holds

end Formalism.QuantumDeterminants
end

-- bundled from Formalism.FormalDegreeBessel.HolDimLowK
section
open Finset

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

def dimLowK {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b),
    (((lowK ε lam + rhoC ε) a - (lowK ε lam + rhoC ε) b) / (rhoC ε a - rhoC ε b))

def cBetween {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ℕ :=
  (univ.filter fun c : Fin n => a < c ∧ c < b ∧ ε c = ε a).card

def FdegFactorial : Prop :=
  ∀ n : ℕ, (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) =
    ∏ i ∈ range n, (i.factorial : ℝ)

def FdegDimV : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), StrictAnti lam →
    fdegHC lam = (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)) /
      ∏ i ∈ range n, (i.factorial : ℝ)

def FdegVV : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), StrictAnti lam →
    fdegHC lam * (∏ i ∈ range n, (i.factorial : ℝ)) =
      ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)

def RhoCGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin n), a < b → ε a = ε b →
    rhoC ε a - rhoC ε b = 1 + (cBetween ε a b : ℝ)

def DimLowKPos : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → 0 < dimLowK ε lam

def DimLowKNat : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → ∃ d : ℕ, dimLowK ε lam = (d : ℝ)

def HolDimLowK : Prop :=
  ∀ (n : ℕ) (a b : ℝ), dimLowK (epsHol n) (lamHol n a b) = 1

end Formalism.QuantumDeterminants
end
end

