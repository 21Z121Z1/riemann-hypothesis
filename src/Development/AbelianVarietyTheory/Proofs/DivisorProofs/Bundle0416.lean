import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowCountAllBounds
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LowCount

theorem v_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (z : ℤ) :
    0 ≤ v (z : C) := by
  have hn : ∀ n : ℕ, 0 ≤ v (n : C) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact le_trans (le_min ih (by simp)) (v.map_add _ _)
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · exact_mod_cast hn n
  · push_cast; rw [v.map_neg]; exact hn n

theorem low_count_first_bound : FactorialWeightedSumBound := by
  intro C _ _ v M ρ g hg P B hB
  apply AddValuation.map_le_sum
  intro α hα
  rw [v.map_mul, v.map_mul]
  have h1 := hB α hα
  have h2 := hg α
  have h3 := v_intCast_nonneg v (P.coeff α)
  have h4 : (((B + ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) + (((0 - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ)
      ≤ v ((∏ m, (α m).factorial : ℕ) : C) + v (coeff α g) := add_le_add h1 h2
  rw [← WithTop.coe_add] at h4
  have h5 : (B + ∑ m, ρ m * α m) + (0 - ∑ m, ρ m * α m) = B := by ring
  rw [h5] at h4
  calc ((B : ℝ) : WithTop ℝ) = 0 + ((B : ℝ) : WithTop ℝ) := by simp
    _ ≤ _ := by rw [add_assoc]; exact add_le_add h3 h4

end GlobalTheory.LowCount

namespace GlobalTheory.LowCount

theorem logb_two_le (p : ℕ) (hp : 3 ≤ p) : Real.logb p 2 ≤ 7 / 8 := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have h3 : Real.log 3 ≤ Real.log p := Real.log_le_log (by norm_num) hp'
  have h : 8 * Real.log 2 ≤ 7 * Real.log 3 := by
    have := Real.log_le_log (by norm_num) (show (2:ℝ) ^ 8 ≤ 3 ^ 7 by norm_num)
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  rw [Real.logb, div_le_iff₀ hlp]
  linarith

theorem low_count_third_bound : RadiusExponentInequality := by
  intro p i cr K ex hp hex hcr hK hK2
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < p := by linarith
  have hex' : (1 : ℝ) ≤ ex := by exact_mod_cast hex
  set D : ℝ := (p : ℝ) ^ 2 - 1 with hD
  have hD8 : 8 ≤ D := by nlinarith
  set q : ℝ := (p : ℝ) ^ (-(2 * (K : ℤ) + 1)) with hq
  have hq0 : 0 ≤ q := zpow_nonneg (by linarith) _
  have hqe : (ex : ℝ) * q ≤ 1 := by
    have hpos : (0 : ℝ) < (p : ℝ) ^ (2 * K + 1) := by positivity
    have : q = 1 / (p : ℝ) ^ (2 * K + 1) := by
      rw [hq, zpow_neg, one_div, show (2 * (K : ℤ) + 1) = ((2 * K + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast]
    rw [this, mul_one_div, div_le_one hpos]
    exact_mod_cast hK
  have hrK : radius p K = (1 + q) / D := rfl
  have hrm : radius p (-1) = (1 + p) / D := by
    rw [hD]; simp only [radius]; norm_num
  have hpm : 1 / ((p : ℝ) - 1) = (1 + p) / D := by
    rw [hD, div_eq_div_iff (by linarith) (by nlinarith)]; ring
  have hL : Real.logb p (ex + 1) ≤ Real.logb p ex + 7 / 8 := by
    have h2 : ((ex : ℝ) + 1) ≤ ex * 2 := by linarith
    have := Real.logb_le_logb_of_le hp1 (by linarith) h2
    rw [Real.logb_mul (by linarith) (by norm_num)] at this
    linarith [logb_two_le p hp]
  have hi : (cr : ℝ) ≤ i := by exact_mod_cast hcr
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hii : (i : ℝ) ≤ (i : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ i := by exact_mod_cast h
      nlinarith
  refine ⟨?_, ?_⟩
  · rw [hrK, hrm]
    have hdiv : (i : ℝ) * ex / ((p : ℝ) - 1) = i * ex * (1 / ((p : ℝ) - 1)) := by ring
    rw [hdiv, hpm]
    have key : ((i : ℝ) - cr) * ex * (ex * q) ≤ ((i : ℝ) - cr) * ex := by
      have := mul_le_mul_of_nonneg_left hqe (mul_nonneg (sub_nonneg.2 hi) (by positivity : (0:ℝ) ≤ ex))
      linarith
    have e : (i : ℝ) * ex * ((1 + p) / D) - (i : ℝ) ^ 2 * Real.logb p (ex + 1) - i * ex * ((1 + q) / D)
        - ex * cr * ((1 + p) / D - (1 + q) / D)
        - ((((i : ℝ) - cr) * ex * p / D) - (i : ℝ) ^ 2 * (Real.logb p ex + 1))
        = (i : ℝ) ^ 2 * (Real.logb p ex + 1 - Real.logb p (ex + 1)) - ((i : ℝ) - cr) * (ex * q) / D := by
      field_simp; ring
    have h1 : ((i : ℝ) - cr) * (ex * q) / D ≤ i / 8 := by
      rw [div_le_iff₀ (by linarith)]
      have : ((i : ℝ) - cr) * (ex * q) ≤ (i : ℝ) - cr :=
        by nlinarith [mul_le_mul_of_nonneg_left hqe (sub_nonneg.2 hi)]
      nlinarith
    have h2 : (i : ℝ) ^ 2 / 8 ≤ (i : ℝ) ^ 2 * (Real.logb p ex + 1 - Real.logb p (ex + 1)) := by
      nlinarith [sq_nonneg (i : ℝ)]
    linarith
  · rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0
      have : 0 ≤ Real.logb p ex := Real.logb_nonneg hp1 hex'
      push_cast; linarith
    · rcases hK2 with h | h
      · omega
      · have h' : ((p : ℝ) ^ (2 * K - 1) : ℝ) ≤ ex := by exact_mod_cast h.le
        have := Real.logb_le_logb_of_le hp1 (by positivity) h'
        rw [Real.logb_pow, Real.logb_self_eq_one hp1] at this
        have hc : ((2 * K - 1 : ℕ) : ℝ) = 2 * (K : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [hc] at this
        linarith

end GlobalTheory.LowCount

namespace GlobalTheory.LowCount

theorem rows_eq {i ex : ℕ} (α : Fin i × Fin i →₀ ℕ) (hdeg : Finsupp.degree α = i * ex)
    (hrow : ∀ e : Fin i, ∑ c : Fin i, α (e, c) ≤ ex) : ∀ e : Fin i, ∑ c : Fin i, α (e, c) = ex := by
  have hs : ∑ e : Fin i, ∑ c : Fin i, α (e, c) = ∑ e : Fin i, ex := by
    rw [← Fintype.sum_prod_type' (fun e c => α (e, c))]
    rw [Finsupp.degree_eq_sum] at hdeg
    simp [hdeg, mul_comm]
  intro e
  exact (Finset.sum_eq_sum_iff_of_le (fun e _ => hrow e)).1 hs e (Finset.mem_univ e)

theorem count_lt (i cr : ℕ) (hcr : cr ≤ i) (a b : ℝ) :
    ∑ e : Fin i, (if e.val < cr then a else b) = cr * a + (i - cr) * b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < cr then a else b) i, Finset.sum_ite]
  have h1 : (Finset.range i).filter (· < cr) = Finset.range cr := by
    ext k; simp; omega
  have h2 : ((Finset.range i).filter (fun k => ¬ k < cr)).card = i - cr := by
    have : (Finset.range i).filter (fun k => ¬ k < cr) = Finset.Ico cr i := by
      ext k; simp; omega
    rw [this, Nat.card_Ico]
  rw [Finset.sum_const, Finset.sum_const, h1, h2, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
  push_cast [hcr]; ring

theorem low_count_second_bound : FactorialMultiindexBound := by
  intro C _ _ v p hp hp3 hv i cr K ex hcr α hdeg hrow
  have hR := rows_eq α hdeg hrow
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨?_, ?_⟩
  · apply le_of_eq
    rw [Fintype.sum_prod_type]
    have : ∀ e : Fin i, ∑ c : Fin i, (if (e, c).1.val < cr then radius p (-1) else radius p K) * (α (e, c) : ℝ)
        = (if e.val < cr then radius p (-1) else radius p K) * ex := by
      intro e
      rw [← hR e, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun e _ => this e), ← Finset.sum_mul, count_lt i cr hcr]
    ring
  · have hN : (∏ x, (α x).factorial : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
    rw [GlobalTheory.T.addValuation_natCast_eq_padicValNat' C v p hp hv _ hN]
    rw [WithTop.coe_le_coe]
    rw [GlobalTheory.LegendreBounds.padicValNat_prod_factorial p hp]
    have hle : ∀ x : Fin i × Fin i, α x ≤ ex := by
      intro x
      rw [← hR x.1]
      exact Finset.single_le_sum (f := fun c => α (x.1, c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ x.2)
    have hterm : ∀ x : Fin i × Fin i, (α x : ℝ) / ((p : ℝ) - 1) - Real.logb p ((ex : ℝ) + 1)
        ≤ (padicValNat p (α x).factorial : ℝ) := by
      intro x
      rw [GlobalTheory.LegendreBounds.legendre_real p hp]
      have hd := GlobalTheory.T.digits_sum_le_mul_logb p (α x) hp
      have hlog : Real.logb p ((α x : ℝ) + 1) ≤ Real.logb p ((ex : ℝ) + 1) :=
        Real.logb_le_logb_of_le hp1 (by positivity) (by have := hle x; push_cast; exact_mod_cast (by omega : α x + 1 ≤ ex + 1))
      have h0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [sub_div]
      have : (((Nat.digits p (α x)).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((ex : ℝ) + 1) := by
        rw [div_le_iff₀ h0]; nlinarith
      linarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hterm x)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul] at hsum
    have htot : (∑ x : Fin i × Fin i, (α x : ℝ)) = i * ex := by
      rw [Finsupp.degree_eq_sum] at hdeg; exact_mod_cast hdeg
    rw [htot] at hsum
    push_cast at hsum ⊢
    nlinarith [hsum]

theorem lowC_all : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality :=
  ⟨low_count_first_bound, low_count_second_bound, low_count_third_bound⟩

end GlobalTheory.LowCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShape
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetPowShape

noncomputable def detZ (i : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) ℤ :=
  Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) ℤ))

theorem detPow_eq_map (C : Type) [Field C] (i c : ℕ) :
    detPow C i c = MvPolynomial.map (Int.castRingHom C) (detZ i ^ c) := by
  rw [map_pow, detZ, RingHom.map_det]
  unfold detPow
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem weight_eq_sum {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    Finsupp.weight w α = ∑ x, α x * w x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [smul_eq_mul]

theorem det_wh {R : Type} [CommRing R] {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) :
    MvPolynomial.IsWeightedHomogeneous w (Matrix.det (Matrix.of fun a b : Fin i =>
      (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))) 1 := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := MvPolynomial.IsWeightedHomogeneous.prod (R := R) (w := w) Finset.univ
    (fun j => (MvPolynomial.X ⟨j, σ j⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))
    (fun j => w ⟨j, σ j⟩) (fun j _ => MvPolynomial.isWeightedHomogeneous_X R w _)
  rw [hw σ] at hp
  have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Σ _ : Fin i, Fin i) R) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  simp only [Matrix.of_apply]
  rw [hc]
  simpa using hp.C_mul ((Equiv.Perm.sign σ : ℤ) : R)

theorem sum_of_mem_support {C : Type} [Field C] {i c : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) (α) (hα : α ∈ (detPow C i c).support) :
    ∑ x, α x * w x = c := by
  have h := (det_wh (R := C) w hw).pow c
  rw [← weight_eq_sum]
  have := h (MvPolynomial.mem_support_iff.1 hα)
  simpa using this

theorem detPow_shape : ∀ (C : Type) [Field C] [CharZero C] (i c : ℕ),
    (detPow C i c).IsHomogeneous (i * c) ∧ (∀ α, ∃ n : ℤ, (detPow C i c).coeff α = n) ∧
    (detPow C i c).coeff (∑ a : Fin i, Finsupp.single ⟨a, a⟩ c) = 1 ∧
    ∀ α ∈ (detPow C i c).support, (∀ a : Fin i, ∑ b : Fin i, α ⟨b, a⟩ = c) ∧
      (∀ b : Fin i, ∑ a : Fin i, α ⟨b, a⟩ = c) := by
  intro C _ _ i c
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (GlobalTheory.LeadingMinors.isHomogeneous_det_X (k := C)
      (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i))).pow c
    simpa [Fintype.card_fin, detPow] using this
  · intro α
    exact ⟨(detZ i ^ c).coeff α, by rw [detPow_eq_map, MvPolynomial.coeff_map]; simp⟩
  · let f : Fin i → (Σ _ : Fin i, Fin i) := fun a => ⟨a, a⟩
    have hf : Function.Injective f := fun x y h => congrArg Sigma.fst h
    have h1 : (∑ a : Fin i, Finsupp.single (⟨a, a⟩ : Σ _ : Fin i, Fin i) c) =
        Finsupp.mapDomain f (∑ a : Fin i, Finsupp.single a c) := by
      change _ = Finsupp.mapDomain.addMonoidHom f _
      simp [map_sum, f]
    have h2 : MvPolynomial.killCompl hf (detPow C i c) =
        MvPolynomial.monomial (∑ a : Fin i, Finsupp.single a c) 1 := by
      unfold detPow
      rw [map_pow, GlobalTheory.LeadingMinors.killCompl_det_X (k := C) hf
        (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i)) id (fun a => rfl),
        MvPolynomial.monomial_pow, one_pow]
      · congr 1
        rw [Finset.smul_sum]
        simp
      · rintro a b hab ⟨x, hx⟩
        obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 hx
        exact hab ((eq_of_heq h2).symm.trans h1)
    rw [h1, ← MvPolynomial.coeff_killCompl hf, h2, MvPolynomial.coeff_monomial, if_pos rfl]
  · intro α hα
    constructor
    · intro a
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.2 = a then 1 else 0) (fun σ => by
          rw [← Equiv.sum_comp σ.symm]
          simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h
    · intro b
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.1 = b then 1 else 0) (fun σ => by simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h

end GlobalTheory.DetPowShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOnePrimeIntegralClosureIffDvdIrreduciblStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_heightOne_prime_integralClosure_iff_dvd_irreducible : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A), Irreducible t → (∀ b : B, (b : K) = algebraMap F K t → b ∈ Q) → ∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a) := by
  first | (exact @GlobalTheory.JacVal.mem_iff_dvd_of_height_one) | (exact GlobalTheory.JacVal.mem_iff_dvd_of_height_one) | (intros; apply GlobalTheory.JacVal.mem_iff_dvd_of_height_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallHeightOneLocalizationIntegrallyClosedStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (z : K), (∀ Q : Ideal A, Q.IsPrime → Q.height = 1 → ∃ r c : A, r ∉ Q ∧ algebraMap A K r * z = algebraMap A K c) → ∃ c : A, z = algebraMap A K c := by
  first | (exact @GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one) | (exact GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one) | (intros; apply GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationCharStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ y : F, y ∈ rA k x I ↔ ∃ N : ℕ, y * (∏ j ∈ I, x j / x i) ^ N ∈ rA k x {i} := by
  first | (exact @GlobalTheory.PD.rA_eq_loc) | (exact GlobalTheory.PD.rA_eq_loc) | (intros; apply GlobalTheory.PD.rA_eq_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSymmetricCocyclesOfPullbackMulP
section
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

theorem mem_symCocycles_of_pullTwo_mulP {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (c : G.A n ⊗[R] G.A n) (h : pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1))) :
    c ∈ symCocycles R (G.A n) := by
  rw [mem_symCocycles] at h ⊢
  have h3 : Function.Injective
      (TensorProduct.map (G.mulP n : G.A n →ₗ[R] G.A (n + 1)) (pullbackTwo (G.mulP n))) :=
    TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n)
      (G.pullbackTwo_mulP_injective n)
  refine ⟨h3 ?_, G.pullbackTwo_mulP_injective n ?_⟩
  · rw [← cobTwo_pullTwo, h.1, map_zero]
  · rw [← h.2]
    exact TensorProduct.map_comm _ _ c

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosuStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure : ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  first | (exact @GlobalTheory.aic_integralClosure_algebraicClosure) | (exact GlobalTheory.aic_integralClosure_algebraicClosure) | (intros; apply GlobalTheory.aic_integralClosure_algebraicClosure  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastSmulMemAugIdealSqSupMapMulP
section
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory

open PDiv

theorem PDivGroup.natCast_smul_mem_augSq_sup_map : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ),
    ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))),
      (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔
        (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
          ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n a ha
  have ha0 : counit (R := R) a = 0 := ha
  have hb : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n)) := by
    change counit (R := R) (G.res n a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha0]
  have h1 : mulBy R _ p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
      ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
    rw [← G.mulP_res n a]
    exact Ideal.mem_map_of_mem _ hb
  have h2 : dUnit R (mulBy R _ p a - (p : R) • a) = 0 := by
    have e1 : dUnit R (mulBy R _ p a - (p : R) • a) = dUnit R (mulBy R _ p a) - dUnit R ((p : R) • a) :=
      map_sub (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _
    have e2 : dUnit R ((p : R) • a) = (p : R) • dUnit R a :=
      map_smul (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _
    rw [e1, e2, ← cotMap_d, cotMap_mulBy, sub_self]
  have h3 : mulBy R _ p a - (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 := by
    have h := (AugCot.d_eq_zero_iff _ _).1 h2
    have he : Bialgebra.counitAlgHom R (G.A (n + 1)) (mulBy R _ p a - (p : R) • a) = 0 := by
      change counit (R := R) (mulBy R _ p a - (p : R) • a) = 0
      rw [map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha0, smul_zero, sub_zero]
    rwa [he, map_zero, sub_zero] at h
  have : (p : R) • a = mulBy R _ p a - (mulBy R _ p a - (p : R) • a) := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right h1) (Submodule.mem_sup_left h3)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqUniformizerCharacterMulResidueCardPowEqOneStatement
section
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d → φ0 ≠ 0 →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n),
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ T T' : Fin d → GlobalTheory.SplitFlip.Res k 1, T ≠ T' →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0) →
    ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 := by
  first | exact @GlobalTheory.HeisUnit.normSq_unif_mul_resCard_pow_eq_one | exact GlobalTheory.HeisUnit.normSq_unif_mul_resCard_pow_eq_one | (intros; apply GlobalTheory.HeisUnit.normSq_unif_mul_resCard_pow_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRealGramDeterminantBoundLeProdCutoff
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Cutoff

noncomputable section

theorem norm_entry_le_opNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (Z : Matrix m n ℂ) (a : m) (b : n) :
    ‖Z a b‖ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)‖ := by
  set v : EuclideanSpace ℂ n := EuclideanSpace.single b (1 : ℂ)
  have h1 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)).le_opNorm v
  have hv : ‖v‖ = 1 := by simp [v]
  rw [hv, mul_one] at h1
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanLin Z v) a
  have h3 : (Matrix.toEuclideanLin Z v) a = Z a b := by
    simp [v, Matrix.toEuclideanLin_apply, Matrix.mulVec_single]
  rw [h3] at h2
  exact h2.trans h1

theorem gB_nonneg {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : 0 ≤ gB p0 w :=
  Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem zOf_mem_cut (X : Data E r) {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) :
    zOf X z τ ∈ {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < X.p0 → X.p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
  intro p hb ha
  have he : zOf X z τ p = zBlock X z τ ⟨p.1.1, ha⟩ ⟨p.1.2, hb⟩ := by
    simp [zBlock, nmat, zOf, p.2]
  rw [he]
  exact ((norm_entry_le_opNorm _ _ _).trans (hz τ).le)

theorem ofReal_bnd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by
  intro E _ _ _ r X z hz
  rw [bnd, ENNReal.ofReal_prod_of_nonneg (fun τ _ => gB_nonneg _ _)]
  refine le_of_eq (Finset.prod_congr rfl fun τ _ => ?_)
  rw [hB, Set.indicator_of_mem (zOf_mem_cut X hz τ)]

end

end GlobalTheory.IntBall.Cutoff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParFunSiegMulStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parFun_sieg_mul' : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), (∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (1 : UG c (stdJ ν E))) φ = φ) ∧ ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, ∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (p * q)) φ = parFun c ψ χ Q (mat c p) (parFun c ψ χ Q (mat c q) φ) := by
  first | exact @GlobalTheory.KSp.parFun_sieg_mul | exact GlobalTheory.KSp.parFun_sieg_mul | (intros; apply GlobalTheory.KSp.parFun_sieg_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionMemComponentGenericOfClosedValuationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_mem_component_generic_of_closed_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (e σ : Spec (CommRingCat.of V) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → σ ≫ f = 𝟙 _ → σ (IsLocalRing.closedPoint V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → σ (⊥ : PrimeSpectrum V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.section_mem_component_generic_of_closed | exact GlobalTheory.section_mem_component_generic_of_closed | (intros; apply GlobalTheory.section_mem_component_generic_of_closed <;> assumption)
end

