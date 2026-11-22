import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertNormalFormOfLinearExponent
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamilyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family : ∀ (F : Type) [Field F] (I : Type) (k : I → Type) [∀ i, Field (k i)] (f : ∀ i, F →+* k i), ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (g : ∀ i, k i →+* L) (h : F →+* L), ∀ i, (g i).comp (f i) = h := by
  first | (exact @GlobalTheory.exists_isAlgClosed_embeddings_of_family) | (exact GlobalTheory.exists_isAlgClosed_embeddings_of_family) | (intros; apply GlobalTheory.exists_isAlgClosed_embeddings_of_family  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekindStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind : ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∃ _ : Algebra (RatFunc k) (FractionRing B), Algebra.IsAlgebraic (RatFunc k) (FractionRing B) := by
  first | (exact @GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc) | (exact GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc) | (intros; apply GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHomogeneousDehomogenizeStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHomogeneous_aeval_eq_of_first_eq_one : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ), T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧ ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 → aeval a T = aeval (fun j => a j.succ) T₀ := by
  first | exact @GlobalTheory.exists_isHomogeneous_dehomogenize | exact GlobalTheory.exists_isHomogeneous_dehomogenize | (intros; apply GlobalTheory.exists_isHomogeneous_dehomogenize <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalRingQuotientPairwiseIsCoprimeIInfEq
section
open scoped TensorProduct
open Function

namespace GlobalTheory

theorem exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A],
      ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A),
        (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  intro ℓ _ A _ _ _
  classical
  have : HenselianLocalRing ℤ_[ℓ] := henselianLocalRing_of_henselianRing ℤ_[ℓ]
  have := finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[ℓ] A
  letI := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨e, he, H⟩ := exists_completeOrthogonalIdempotents_of_henselian ℤ_[ℓ] A
  refine ⟨MaximalSpectrum A, inferInstance, fun q ↦ Ideal.span {1 - e q}, fun q ↦ ?_, ?_, ?_⟩
  · have := q.isMaximal
    exact isLocalRing_quotient_one_sub (he.idem q) q.asIdeal (H q)
  · intro i j hij
    change IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j})
    rw [Ideal.isCoprime_span_singleton_iff]
    have h0 : e i * e j = 0 := he.ortho hij
    exact ⟨1, e i, by linear_combination (-1 : A) * h0⟩
  · refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [Submodule.mem_iInf] at hx
    rw [Ideal.mem_bot, ← one_mul x, ← he.complete, Finset.sum_mul]
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hx q)
    rw [← hw]
    linear_combination (-w) * (he.idem q).eq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLargePrimeDvdIntPolynomialEval
section
open scoped TensorProduct Polynomial

namespace GlobalTheory

open Polynomial in

theorem exists_prime_gt_dvd_eval :
    ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | (apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementIsotropicOrthogonalComplexStatement
section
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by
  first | exact @GlobalTheory.levi_element_cpx | exact GlobalTheory.levi_element_cpx | (intros; apply GlobalTheory.levi_element_cpx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAlgebraicallyClosedPointStatement
section
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_algebraically_closed_point : ∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] (k : Type) [Field k] [IsAlgClosed k]
    (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
    ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by
  first | exact @GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed | exact GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed | (intros; apply GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricPointOfFaithfullyFlatFiniteTyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_geometricPoint_of_faithfullyFlat_finiteType : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
    Algebra.FiniteType A B → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k),
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := by
  first | exact @GlobalTheory.GeomPointLift.exists_lift | exact GlobalTheory.GeomPointLift.exists_lift | (intros; apply GlobalTheory.GeomPointLift.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentAdaptedToDecreasingChainAStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIndependent_adapted_to_decreasing_chain' : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ), (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) → (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ), LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧ ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  first | exact @GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | exact GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | (intros; apply GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSubPiHermitianOfLatticeAddHom
section
open Complex Matrix

namespace GlobalTheory

theorem exists_linear_sub_pi_mul_form_of_addMonoidHom :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) → ∀ p : Λ →+ ℂ, ∃ (f : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ), ∀ l : Λ, p l = f l - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  intro g Λ H _ hΛ hH p
  obtain ⟨F, hF⟩ := AppellHumbert.exists_real_extension Λ hΛ p
  have hinj : Function.Injective H.vecMulLinear := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra h0
    have := hH v h0
    rw [dotProduct_mulVec] at this
    rw [vecMulLinear_apply] at hv
    simp [hv] at this
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let s : Fin g → ℂ := fun b => (F (Pi.single b 1) - I * F (Pi.single b I)) / 2
  let c : Fin g → ℂ := fun b => (F (Pi.single b 1) + I * F (Pi.single b I)) / 2
  have hsplit : ∀ u, F u = s ⬝ᵥ u + c ⬝ᵥ star u := by
    intro u
    conv_lhs => rw [AppellHumbert.eq_sum_re_im u]
    simp only [map_sum, map_add, map_smul, dotProduct, ← Finset.sum_add_distrib,
      Pi.star_apply, real_smul, s, c]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 : u b = (u b).re + (u b).im * I := (re_add_im _).symm
    have h2 : star (u b) = (u b).re - (u b).im * I := by
      apply Complex.ext <;> simp
    rw [h2]
    generalize (u b).re = x at *
    generalize (u b).im = y at *
    rw [h1]
    linear_combination (y * F (Pi.single b I)) * I_mul_I
  obtain ⟨v, hv⟩ := hsurj (-(Real.pi : ℂ)⁻¹ • c)
  rw [vecMulLinear_apply] at hv
  refine ⟨LinearMap.toContinuousLinearMap (dotProductBilin ℂ ℂ s), v, fun l => ?_⟩
  rw [← hF, hsplit, dotProduct_mulVec, hv, smul_dotProduct]
  simp only [LinearMap.coe_toContinuousLinearMap', dotProductBilin_apply_apply, smul_eq_mul]
  field_simp
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtendStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ → ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R, IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  first | exact @GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | exact GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | (intros; apply GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitOfDvrUnit
section
namespace GlobalTheory

theorem unitMultiple_descends_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (𝔭 : PrimeSpectrum A),
    𝔭.asIdeal.height = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (iT : Localization.AtPrime 𝔭.asIdeal →+* V), Function.Injective iT → IsLocalHom iT →
    ∀ a b : A,
    (∃ w : Vˣ, iT (algebraMap A _ a) = iT (algebraMap A _ b) * w) →
    ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      (u : Localization.AtPrime 𝔭.asIdeal) * algebraMap A _ b = algebraMap A _ a := by
  intro A _ _ _ _ 𝔭 h1 V _ _ _ iT hinj hloc a b ⟨w, hw⟩
  haveI : IsDomain (Localization.AtPrime 𝔭.asIdeal) :=
    IsLocalization.isDomain_localization 𝔭.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔭.asIdeal) :=
    isDiscreteValuationRing_of_height_eq_one 𝔭.asIdeal h1 _
  set x := algebraMap A (Localization.AtPrime 𝔭.asIdeal) a with hxdef
  set y := algebraMap A (Localization.AtPrime 𝔭.asIdeal) b with hydef
  have hw0 : (w : V) ≠ 0 := w.ne_zero
  by_cases hx : x = 0
  · refine ⟨1, ?_⟩
    have h0 : iT y * (w : V) = 0 := by rw [← hw, hx, map_zero]
    have hy : iT y = 0 := (mul_eq_zero.mp h0).resolve_right hw0
    have : y = 0 := hinj (by rw [hy, map_zero])
    rw [this, hx, mul_zero]
  · have hxT : iT x ≠ 0 := fun h => hx (hinj (by rw [h, map_zero]))
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond x y
    · have e : iT x * (iT c * (w : V)) = iT x * 1 := by
        rw [mul_one, ← mul_assoc, ← map_mul, hc]
        exact hw.symm
      have hcw : iT c * (w : V) = 1 := mul_left_cancel₀ hxT e
      have hc' : IsUnit c := (isUnit_map_iff iT c).mp (IsUnit.of_mul_eq_one _ hcw)
      refine ⟨hc'.unit⁻¹, ?_⟩
      rw [← hc, mul_left_comm, IsUnit.val_inv_mul, mul_one]
    · have hy : y ≠ 0 := by
        rintro h
        apply hx
        rw [← hc, h, zero_mul]
      have hyT : iT y ≠ 0 := fun h => hy (hinj (by rw [h, map_zero]))
      have e : iT y * iT c = iT y * (w : V) := by
        rw [← map_mul, hc]
        exact hw
      have hcw : iT c = (w : V) := mul_left_cancel₀ hyT e
      have hc' : IsUnit c := (isUnit_map_iff iT c).mp (by rw [hcw]; exact w.isUnit)
      refine ⟨hc'.unit, ?_⟩
      rw [IsUnit.unit_spec, mul_comm, hc]

end GlobalTheory
end

