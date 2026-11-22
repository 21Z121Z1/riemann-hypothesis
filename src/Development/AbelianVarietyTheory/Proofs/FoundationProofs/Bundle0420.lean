import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0419
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0396

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnnihilatorKaehlerDerivationPrimitiveRootStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∀ a : A, a • dA A z = 0 → ∃ w ∈ A, (l : Ω) ^ 4 * (a : Ω) = (l : Ω) ^ N * w := by
  first | exact @GlobalTheory.RecOne.pow_four_mul_mem_of_smul_dA_eq_zero | exact GlobalTheory.RecOne.pow_four_mul_mem_of_smul_dA_eq_zero | (intros; apply GlobalTheory.RecOne.pow_four_mul_mem_of_smul_dA_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqPrimeSmulKaehlerDerivationEqSmulRootOfUnityStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_prime_smul_kaehlerDerivation_eq_smul_rootOfUnity : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : A, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ y : A, ((l : A) ^ 2) • dA A v = y • dA A z := by
  first | exact @GlobalTheory.RecOne.l_sq_smul_dA_eq_smul | exact GlobalTheory.RecOne.l_sq_smul_dA_eq_smul | (intros; apply GlobalTheory.RecOne.l_sq_smul_dA_eq_smul <;> assumption)
end

