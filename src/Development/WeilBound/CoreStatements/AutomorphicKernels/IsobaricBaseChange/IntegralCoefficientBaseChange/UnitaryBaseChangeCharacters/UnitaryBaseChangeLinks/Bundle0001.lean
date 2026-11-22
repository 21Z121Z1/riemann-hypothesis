import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Mathlib
import Formalism.SatakeDualWeyl.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import GroundTheory.LocalFields.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormApproximationFirstLevel

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.CharpolyDvdOfAevalEqZero
section
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt : ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]), M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by
  first | exact @GlobalTheory.SepCharpoly.charpoly_dvd_of_aeval_eq_zero | (intros; apply GlobalTheory.SepCharpoly.charpoly_dvd_of_aeval_eq_zero <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ConjugateSelfReciprocalCharpoly
section
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.conjugate_self_reciprocal_charpoly : ∀ (R : Type) [CommRing R] (s : R →+* R) (n : ℕ) (M : Matrix (Fin n) (Fin n) R), cT s M * M = 1 → GlobalTheory.UTr.IsCsr s M.charpoly := by
  first | exact @GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one | (intros; apply GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EqZeroOfMemAllPowers
section
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.eq_zero_of_mem_all_powers : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P), (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 := by
  first | exact @GlobalTheory.NormEq.sep | (intros; apply GlobalTheory.NormEq.sep <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NormApproximationFiltration
section
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.norm_approximation_filtration : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (m : ℕ), 1 ≤ m → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → x ∈ GlobalTheory.NormEq.filt h P m → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, u ∈ GlobalTheory.NormEq.filt h P m ∧ (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P (m + 1) := by
  first | exact @GlobalTheory.NormEq.exists_norm_lift_step | (intros; apply GlobalTheory.NormEq.exists_norm_lift_step <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NormApproximationFirstLevel
section
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.norm_approximation_first_level : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)), P.1.Separable → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P 1 := by
  first | exact @GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one | exact GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one | (intros; apply GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NormFiltrationComplete
section
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.norm_filtration_complete : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)), GroundTheory.LocalField.FiltrationComplete (GlobalTheory.NormEq.filt h P) := by
  first | exact @GlobalTheory.NormEq.filtrationComplete_filt | exact GlobalTheory.NormEq.filtrationComplete_filt | (intros; apply GlobalTheory.NormEq.filtrationComplete_filt <;> assumption)
end

