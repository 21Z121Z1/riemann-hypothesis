import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIde
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.exists_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B),
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  intro B _ J δ Q
  obtain ⟨η, hη⟩ := _root_.GlobalTheory.PDA.exists_dividedPowers_aug B Q
  obtain ⟨ε, hε⟩ := (_root_.GlobalTheory.PDA.PDPoly.exists_lift_and_aug B Q).2
  obtain ⟨θ, hθ, hθη⟩ := _root_.GlobalTheory.SplitDP.exists_dp_ext B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n ↦ ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0), hη]

end GlobalTheory.PDA
