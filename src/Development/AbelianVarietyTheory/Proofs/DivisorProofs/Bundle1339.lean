import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalEigenvaluesIndependentOfStandardFrame
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SegDualExistsTerms
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.SegDualProof

theorem segDual_exists_terms : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ D : IrrGL k → IrrGL k, (∀ x y, DualCl x y ↔ y = D x) → (∀ x, D (D x) = x) → (∀ (x : IrrGL k) (s : ℂ), D (x.nu s) = (D x).nu (-s)) → (∀ x, x.IsCusp → (D x).IsCusp) → (∀ x, (D x).1 = x.1) → ∀ Δ : Segment k, (∃ Δ', SegDual Δ Δ') ∧ ∀ Δ', SegDual Δ Δ' → Δ'.len = Δ.len ∧ ∀ a : ℕ, a < Δ.len → Δ'.first.nu (a : ℂ) = D (Δ.first.nu ((Δ.len : ℂ) - 1 - a)) := by
  intro k _ _ _ _ D hD _ hnu hcusp _ Δ
  have hρ : (D (Δ.first.nu ((Δ.len : ℂ) - 1))).IsCusp := hcusp _ (Δ.isCusp_first.nu _)
  refine ⟨⟨Segment.ofFirst _ hρ Δ.len Δ.len_pos, rfl, (hD _ _).2 rfl⟩, ?_⟩
  rintro Δ' ⟨hl, hd⟩
  refine ⟨hl, fun a _ => ?_⟩
  rw [(hD _ _).1 hd]
  have h1 := hnu (Δ.first.nu ((Δ.len : ℂ) - 1)) (-(a : ℂ))
  rw [neg_neg, IrrGL.nu_nu, ← sub_eq_add_neg] at h1
  exact h1.symm

end GlobalTheory.SegDualProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCentralizerCommutativeStatement
section
open Matrix GlobalTheory.LKRes
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_centralizer_commutative : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∀ a ∈ Subgroup.centralizer {N}, ∀ b ∈ Subgroup.centralizer {N}, a * b = b * a := by
  first | (exact @GlobalTheory.LKRes.CentComm.centralizer_comm) | (exact GlobalTheory.LKRes.CentComm.centralizer_comm) | (intros; apply GlobalTheory.LKRes.CentComm.centralizer_comm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace
section
open Matrix GlobalTheory.TorFin

namespace GlobalTheory.CapelliNext

open Finset

variable {A : Type} [Ring A] [Algebra ℂ A]

def shiftCoeff (d : ℕ) (p q : A) (c : ℕ → A) : ℕ → A :=
  fun i => (Nat.casesOn i 0 (fun j => p * c j) : A) + (if i < d + 1 then q * c i else 0)

theorem affine_mul_eq (d : ℕ) (p q : A) (c : ℕ → A) (u : ℂ) :
    (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • shiftCoeff d p q c i := by
  unfold shiftCoeff
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]

theorem prod_affine_two_top (t : ℕ) (p : Fin (t + 1) → ℂ) (q : Fin (t + 1) → A) :
    ∃ c : ℕ → A, c (t + 1) = (∏ k, p k) • (1 : A) ∧
      c t = ∑ k, (∏ j, (if j = k then (1 : ℂ) else p j)) • q k ∧
      ∀ u : ℂ, (List.ofFn fun k => (u * p k) • (1 : A) + q k).prod
        = ∑ i ∈ range (t + 1 + 1), u ^ i • c i := by
  induction t with
  | zero =>
    let c : ℕ → A := fun i => if i = 0 then q 0 else if i = 1 then (p 0) • (1 : A) else 0
    refine ⟨c, ?_, ?_, fun u => ?_⟩
    · simp [c]
    · simp [c]
    · simp [c, sum_range_succ, add_comm]
      rw [mul_smul]
  | succ t ih =>
    obtain ⟨c, hc1, hc0, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    refine ⟨shiftCoeff (t + 1) (p 0 • (1 : A)) (q 0) c, ?_, ?_, fun u => ?_⟩
    · simp only [shiftCoeff, lt_irrefl, if_false, add_zero]
      rw [hc1, smul_one_mul, smul_smul, ← Fin.prod_univ_succ]
    · simp only [shiftCoeff, lt_add_iff_pos_right, Nat.lt_add_one, if_true]
      rw [hc0, hc1, smul_one_mul, mul_smul_comm, mul_one, smul_sum, add_comm]
      conv_rhs => rw [Fin.sum_univ_succ]
      congr 1
      · simp [Fin.prod_univ_succ, smul_mul_assoc]
      · refine sum_congr rfl fun k _ => ?_
        simp [Fin.prod_univ_succ, Fin.succ_ne_zero, smul_smul, (Fin.succ_ne_zero _).symm]
    · rw [List.ofFn_succ, List.prod_cons, hc u]
      have : (u * p 0) • (1 : A) + q 0 = u • (p 0 • (1 : A)) + q 0 := by rw [smul_smul]
      rw [this, affine_mul_eq]

end GlobalTheory.CapelliNext

namespace GlobalTheory.CapelliNext
open Finset

theorem qdet_shift_next_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ), ∃ (c : ℕ → A) (t : ℂ),
    c (m + 1) = 1 ∧ c m = ∑ i, E i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  intro A _ _ m E s
  have h : ∀ σ : Equiv.Perm (Fin (m + 1)), ∃ c : ℕ → A,
      c (m + 1) = (∏ k, (if σ k = k then (1 : ℂ) else 0)) • (1 : A) ∧
      c m = ∑ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) •
        ((if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k) ∧
      ∀ u : ℂ, (List.ofFn fun k : Fin (m + 1) => Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (m + 1 + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hc1, hc0, hc⟩ := prod_affine_two_top m (fun k => if σ k = k then (1 : ℂ) else 0)
      (fun k => (if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k)
    refine ⟨c, hc1, hc0, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Formalism.REAL.Tm
    simp only [id]
    split_ifs with hk
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← add_assoc, ← add_smul]
      congr 2
      ring
    · simp
  choose c hc1 hc0 hc using h
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i,
    ∑ k : Fin (m + 1), (-s - ((k : ℕ) : ℂ)), ?_, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc1 1]
      simp
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc1 σ, Finset.prod_eq_zero (mem_univ k) (if_neg hk), zero_smul, mul_zero]
    · intro h1
      exact absurd (mem_univ _) h1
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc0 1]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one,
        id_eq, if_true, ite_self, prod_const_one, one_smul]
      rw [sum_add_distrib, add_comm]
      congr 1
      simp only [Algebra.algebraMap_eq_smul_one, ← sum_smul]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc0 σ]
      have hz : ∀ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) = 0 := by
        intro k
        by_cases hk : σ k = k
        · refine Finset.prod_eq_zero (mem_univ k₀) ?_
          have : k₀ ≠ k := fun e => hk₀ (e ▸ hk)
          simp [this, hk₀]
        · refine Finset.prod_eq_zero (mem_univ (σ k)) ?_
          have h2 : σ (σ k) ≠ σ k := fun e => hk (σ.injective e)
          simp [hk, h2]
      simp [hz]
    · intro h1
      exact absurd (mem_univ _) h1
  · unfold Formalism.REAL.qdet Formalism.REAL.qminor
    rw [Finset.sum_congr rfl fun σ _ => by rw [hc σ u]]
    simp_rw [mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    simp_rw [← smul_sum]

end GlobalTheory.CapelliNext
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAdelicGLComplexConjCommutesOperators
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section
namespace GlobalTheory.SmoothConj
open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem chart_conj (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (φ x)) g = Complex.conjCLE ∘ chart φ g := by
  funext x
  simp only [chart, Function.comp_apply]
  split_ifs <;> simp

theorem conj_mem (φ : Sm E a) : (fun x => starRingEnd ℂ (φ.1 x)) ∈ Sm E a := by
  have hφ : ∀ g, ContDiffOn ℝ (↑(⊤ : ℕ∞)) (chart φ.1 g) (invSet E a) := φ.2
  show ∀ g, ContDiffOn ℝ _ (chart (fun x => starRingEnd ℂ (φ.1 x)) g) (invSet E a)
  intro g
  rw [chart_conj]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (hφ g)

def conjMap (φ : Sm E a) : Sm E a := ⟨fun x => starRingEnd ℂ (φ.1 x), conj_mem φ⟩

def conjEquiv : Sm E a ≃ₗ⋆[ℂ] Sm E a where
  toFun := conjMap
  invFun := conjMap
  map_add' x y := by apply Subtype.ext; funext g; simp [conjMap]
  map_smul' c x := by apply Subtype.ext; funext g; simp [conjMap]
  left_inv x := by apply Subtype.ext; funext g; simp [conjMap]
  right_inv x := by apply Subtype.ext; funext g; simp [conjMap]

theorem conjEquiv_act (o : Op E a) (φ : Sm E a) :
    act o (conjEquiv φ) = conjEquiv (act o φ) := by
  cases o with
  | fin k => rfl
  | cpt k => rfl
  | lie X =>
    apply Subtype.ext; funext g
    show lieD X (fun x => starRingEnd ℂ (φ.1 x)) g = starRingEnd ℂ (lieD X φ.1 g)
    simp only [lieD, chart_conj, ContinuousLinearEquiv.comp_fderiv]
    rfl

end GlobalTheory.SmoothConj

namespace GlobalTheory
open GlobalTheory.CuspRep

theorem smooth_conj_commutes_act : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∃ C : Sm E a ≃ₗ⋆[ℂ] Sm E a, (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) ∧
      ∀ o φ, act o (C φ) = C (act o φ) :=
  fun _ _ _ _ _ => ⟨SmoothConj.conjEquiv, fun _ _ => rfl, SmoothConj.conjEquiv_act⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLocalLieRepresentation
section
noncomputable section

open Matrix GlobalTheory.TorFin GlobalTheory.SmoothForms
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.TorFin.RightRep

variable {n : ℕ} {G : Type} [Group G]

def sig (J : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := J⁻¹ * Xᴴ * J
  map_add' X Y := by rw [conjTranspose_add, mul_add, add_mul]
  map_smul' c X := by
    change J⁻¹ * (c • X)ᴴ * J = c • (J⁻¹ * Xᴴ * J)
    rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]

abbrev skewSub (J : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J).toSubmodule

theorem sig_mul_eq_one_iff {J : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit J.det) (u : Matrix (Fin n) (Fin n) ℂ) :
    sig J u * u = 1 ↔ IsUni J u := by
  change J⁻¹ * uᴴ * J * u = 1 ↔ uᴴ * J * u = J
  constructor
  · intro h1
    have := congrArg (J * ·) h1
    simpa only [← mul_assoc, mul_nonsing_inv _ hu, one_mul, mul_one] using this
  · intro h1
    rw [mul_assoc, mul_assoc, ← mul_assoc uᴴ, h1, nonsing_inv_mul _ hu]

theorem isLieData {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hu : IsUnit J.det) {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) : IsLieData (sig J) (skewSub J).subtype s := by
  have anti : ∀ a b, sig J (a * b) = sig J b * sig J a := fun a b => by
    change _ * (a * b)ᴴ * _ = (_ * bᴴ * _) * (_ * aᴴ * _)
    rw [conjTranspose_mul]
    simp only [mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hu]
  refine ⟨anti, ?_, fun a => ?_, Subtype.val_injective, fun X => ⟨fun h => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change J⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J = 1
    rw [conjTranspose_one, mul_one, nonsing_inv_mul _ hu]
  · change _ * (_ * aᴴ * _)ᴴ * _ = a
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hu, nonsing_inv_mul _ hu, mul_one]
  · refine ⟨⟨X, ?_⟩, rfl⟩
    have h1 : J⁻¹ * Xᴴ * J = -X := h
    change Xᴴ * J + J * X = 0
    rw [← mul_nonsing_inv_cancel_left _ (Xᴴ * J) hu, ← mul_assoc J⁻¹, h1, mul_neg, neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    have h1 : Y.1ᴴ * J + J * Y.1 = 0 := Y.2
    change _ * Y.1ᴴ * _ = -Y.1
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ hu]
  · exact hs a b ((sig_mul_eq_one_iff hu a).1 ha) ((sig_mul_eq_one_iff hu b).1 hb)

theorem mem_smLoc_iff {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hu : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s) (φ : G → ℂ) :
    φ ∈ smLoc J s ↔ Sm (expMap (skewSub J).subtype s) φ := by
  have H := isLieData hJ hu hs
  rw [SecondKind.sm_iff H (hasLog_of_isLieData _ _ _ _ _ _ H) Set.univ (by simp), mem_smLoc]
  constructor
  · intro h k Y _ g
    exact h k (fun i => (Y i).1) (fun i => (Y i).2) g
  · intro h k Z hZ g
    exact h k (fun i => ⟨Z i, hZ i⟩) (fun _ => trivial) g

variable {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hu : IsUnit J.det) {s : Matrix (Fin n) (Fin n) ℂ → G}
  (hs : IsMulOn J s)

def derL (X : skewSub J) : Module.End ℂ (smLoc J s) where
  toFun φ := ⟨Der (expMap (skewSub J).subtype s) X φ.1, (mem_smLoc_iff hJ hu hs _).2
    ((der_smooth_and_linear _ _ _ _ _ _ (isLieData hJ hu hs)
      (hasLog_of_isLieData _ _ _ _ _ _ (isLieData hJ hu hs)) φ.1 ((mem_smLoc_iff hJ hu hs _).1 φ.2)).1 X)⟩
  map_add' φ ψ := Subtype.ext (funext fun g => deriv_add
    (Sm.differentiableAt ((mem_smLoc_iff hJ hu hs _).1 φ.2) g X)
    (Sm.differentiableAt ((mem_smLoc_iff hJ hu hs _).1 ψ.2) g X))
  map_smul' c φ := Subtype.ext (funext fun g =>
    deriv_const_smul c (Sm.differentiableAt ((mem_smLoc_iff hJ hu hs _).1 φ.2) g X))

theorem derL_apply (X : skewSub J) (φ : smLoc J s) :
    (derL hJ hu hs X φ).1 = Der (expMap (skewSub J).subtype s) X φ.1 := rfl

include hu hs in

theorem lineOf_add (Z : skewSub J) (t u : ℝ) : lineOf s Z.1 t * lineOf s Z.1 u = lineOf s Z.1 (t + u) := by
  have h1 : IsUni J (NormedSpace.exp (t • Z.1)) := exp_mem_UH hu (t • Z).2
  have h2 : IsUni J (NormedSpace.exp (u • Z.1)) := exp_mem_UH hu (u • Z).2
  unfold lineOf
  rw [← hs _ _ h1 h2, add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl Z.1).smul_left t).smul_right u)]

theorem hasDerivAt_derL (X : skewSub J) (φ : smLoc J s) (g : G) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => φ.1 (g * lineOf s X.1 τ)) ((derL hJ hu hs X φ).1 (g * lineOf s X.1 t)) t := by
  have hsm := (mem_smLoc_iff hJ hu hs _).1 φ.2
  set F : ℝ → ℂ := fun τ => φ.1 (g * lineOf s X.1 τ) with hFdef
  have hF : Differentiable ℝ F :=
    ((hsm g).comp (contDiff_id.smul contDiff_const : ContDiff ℝ ∞ fun τ : ℝ => τ • X)).differentiable (by simp)
  have key : (fun u : ℝ => φ.1 (g * lineOf s X.1 t * expMap (skewSub J).subtype s (u • X))) =
      fun u => F (t + u) := funext fun u => by
    show φ.1 (g * lineOf s X.1 t * lineOf s X.1 u) = φ.1 (g * lineOf s X.1 (t + u))
    rw [mul_assoc, lineOf_add hu hs]
  have e : (derL hJ hu hs X φ).1 (g * lineOf s X.1 t) = deriv F t := by
    rw [derL_apply]
    show deriv (fun u : ℝ => φ.1 (g * lineOf s X.1 t * expMap (skewSub J).subtype s (u • X))) 0 = _
    rw [key, deriv_comp_const_add, add_zero]
  rw [e]
  exact (hF t).hasDerivAt

end GlobalTheory.TorFin.RightRep

namespace GlobalTheory.TorFin

open RightRep in

theorem exists_rightDer_rep : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ)
    (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s →
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsLieRep ρ ∧ IsRightDer J s ρ := by
  intro n G _ J s hJ hu hs
  have H := isLieData hJ hu hs
  have hl := hasLog_of_isLieData _ _ _ _ _ _ H
  let ρ₀ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → Module.End ℂ (smLoc J s) := fun X => derL hJ hu hs ⟨X.1, X.2⟩
  have hsm : ∀ φ : smLoc J s, Sm (expMap (skewSub J).subtype s) φ.1 := fun φ => (mem_smLoc_iff hJ hu hs _).1 φ.2
  obtain ⟨R, -, hR, hc⟩ := GlobalTheory.UnitaryLieComplexification.exists_extension hJ hu ρ₀
    (fun X Y => LinearMap.ext fun φ => Subtype.ext
      ((der_smooth_and_linear _ _ _ _ _ _ H hl φ.1 (hsm φ)).2.1 ⟨X.1, X.2⟩ ⟨Y.1, Y.2⟩))
    (fun c X => LinearMap.ext fun φ => Subtype.ext
      ((der_smooth_and_linear _ _ _ _ _ _ H hl φ.1 (hsm φ)).2.2 c ⟨X.1, X.2⟩))
    (fun X Y Z hZ => LinearMap.ext fun φ => Subtype.ext
      (Bracket.der_bracket _ _ _ _ _ _ H hl φ.1 (hsm φ) ⟨X.1, X.2⟩ ⟨Y.1, Y.2⟩ ⟨Z.1, Z.2⟩ hZ).symm)
  refine ⟨R, hc, fun Z hZ φ g t => ?_⟩
  have hRZ : R Z = derL hJ hu hs ⟨Z, hZ⟩ := hR ⟨Z, hZ⟩
  rw [hRZ]
  exact hasDerivAt_derL hJ hu hs ⟨Z, hZ⟩ φ g t

end GlobalTheory.TorFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosureStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialUnitary_fixing_plane_complement_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  first | exact @GlobalTheory.PlaneSU.plane_closure | exact GlobalTheory.PlaneSU.plane_closure | (intros; apply GlobalTheory.PlaneSU.plane_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehInfMapSubEqSumTwists
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.DefiniteBC.spehInf_map_sub_eq_sum_twists : ∀ (d : ℕ) (m : Multiset ℂ) (F : ℂ),
  ∑ k : Fin d, m.map (fun z => F + (((d : ℂ) - 1) / 2 - (k : ℕ)) - z) = (spehInf d m).map (fun z => F - z) := by
  intro d m F
  have hL : ∀ (f : ℕ → Multiset ℂ) (n : ℕ), ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
    intro f n
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => m.map (fun z => F + (((d : ℂ) - 1) / 2 - (k : ℕ)) - z)) d]
  unfold spehInf
  rw [hL]
  have hM := map_sum (Multiset.mapAddMonoidHom (fun z : ℂ => F - z))
    (fun k : ℕ => m.map (fun x => x + (((d : ℂ) - 1) / 2 - k))) (Finset.range d)
  simp only [Multiset.mapAddMonoidHom_apply] at hM
  rw [hM]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalEigenvaluesIndependentOfStandardFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalEigenvalues_independent_of_standardFrame : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ Pr d, (∀ κ, Q.ψ κ ∈ hyp V Pr ↔ Q'.ψ κ ∈ hyp V' Pr) ∧ ∀ B B', SphOp V Pr d B → SphOp V' Pr d B' → ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ κ, Q.ψ κ ∈ hyp V Pr → Formalism.L2.NG.rt D.host.E n κ x = x) → principalLevelFrame.Hecke₃ Q B x = principalLevelFrame.Hecke₃ Q' B' x := by
  first | exact @GlobalTheory.FrameTransport.sph_eigen_frame_indep | exact GlobalTheory.FrameTransport.sph_eigen_frame_indep | (intros; apply GlobalTheory.FrameTransport.sph_eigen_frame_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMemIsotropicFlagLeviStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorusElement_mem_isotropicFlagLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  first | exact @GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag | exact GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag | (intros; apply GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEqStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqZeroPoint_eq_of_cotangentForm_eq : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A], (GlobalTheory.LieVB.omega A).IsQuasicoherent → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') := by
  first | exact @GlobalTheory.SqZeroPt.eq_of_Phi_eq | exact GlobalTheory.SqZeroPt.eq_of_Phi_eq | (intros; apply GlobalTheory.SqZeroPt.eq_of_Phi_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionTopCoeffComplexPartitionOfUnityEStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_transgressionTopCoeffComplex_partitionOfUnity_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι] (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) → (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  first | exact @GlobalTheory.GoodTop.corrC_sum_eq_zero | exact GlobalTheory.GoodTop.corrC_sum_eq_zero | (intros; apply GlobalTheory.GoodTop.corrC_sum_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermEqOfSimilitudeRelStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_eq_of_similitude_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.Rel Q → Q.term Kf f r K φ = P.term Kf f r K φ := by
  first | (exact @GlobalTheory.LKMid.Pair.term_eq_of_rel) | (exact GlobalTheory.LKMid.Pair.term_eq_of_rel) | (intros; apply GlobalTheory.LKMid.Pair.term_eq_of_rel <;> assumption)
end

