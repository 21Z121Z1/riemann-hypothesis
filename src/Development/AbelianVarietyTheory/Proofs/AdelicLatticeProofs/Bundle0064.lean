import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassFinitenessCompletelyReducibleStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFiniteness_completelyReducible : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → SS Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_ss | exact GlobalTheory.ClassFin.cf_of_ss | (intros; apply GlobalTheory.ClassFin.cf_of_ss <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmCharacterConjugationSymmetry
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in

theorem _root_.GlobalTheory.cA_incA_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (x : E) :
    _root_.HeckeCharacterZeroLocus.ThmBIn.cA σ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E (σ x) := by
  unfold _root_.HeckeCharacterZeroLocus.ThmBIn.cA _root_.HeckeCharacterZeroLocus.ThmBIn.incA _root_.HeckeCharacterZeroLocus.ThmBIn.AE
  exact rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfOddPrimeDegreeStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.np_of_odd_prime_degree' : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  first | exact @GlobalTheory.CNorm.np_of_odd_prime_degree | exact GlobalTheory.CNorm.np_of_odd_prime_degree | (intros; apply GlobalTheory.CNorm.np_of_odd_prime_degree <;> assumption)
end

