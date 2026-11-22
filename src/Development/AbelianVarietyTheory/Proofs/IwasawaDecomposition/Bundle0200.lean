import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffXMulOfNotMem
section
noncomputable section

open Matrix MvPowerSeries GlobalTheory.FockSeq

namespace GlobalTheory.GaussInner

variable {σ : Type} [DecidableEq σ]

theorem coeff_X_mul_add (l : σ) (E : MvPowerSeries σ ℂ) (β : σ →₀ ℕ) :
    coeff (β + Finsupp.single l 1) (X l * E) = coeff β E := by
  rw [X_def, add_comm, coeff_add_monomial_mul, one_mul]

theorem coeff_X_mul_of_notMem (l : σ) (E : MvPowerSeries σ ℂ) {α : σ →₀ ℕ}
    (h : α ∉ Set.range fun β : σ →₀ ℕ => β + Finsupp.single l 1) : α l = 0 ∧ coeff α (X l * E) = 0 := by
  have h' : ¬ Finsupp.single l 1 ≤ α := fun hle => h ⟨_, tsub_add_cancel_of_le hle⟩
  refine ⟨by rw [Finsupp.single_le_iff] at h'; omega, ?_⟩
  rw [X_def, coeff_monomial_mul, if_neg h']

def dil (σ : Type) : Submodule ℂ (MvPowerSeries σ ℂ) where
  carrier := {E | ∀ r : ℝ, 0 ≤ r → r < 1 →
    Summable fun α : σ →₀ ℕ => r ^ α.degree * ((mfact α : ℝ) * ‖coeff α E‖ ^ 2)}
  zero_mem' r _ _ := by simp
  add_mem' {E E'} h h' r h0 h1 := by
    refine .of_nonneg_of_le (fun α => by positivity) (fun α => ?_) (((h r h0 h1).add (h' r h0 h1)).mul_left 2)
    rw [map_add, ← mul_add, ← mul_add, mul_left_comm 2, mul_left_comm 2]
    gcongr
    nlinarith [norm_add_le (coeff α E) (coeff α E'), norm_nonneg (coeff α E + coeff α E'),
      sq_nonneg (‖coeff α E‖ - ‖coeff α E'‖)]
  smul_mem' c E h r h0 h1 := by
    refine ((h r h0 h1).mul_left (‖c‖ ^ 2)).congr fun α => ?_
    rw [coeff_smul, norm_mul]; ring

theorem X_mul_mem {E : MvPowerSeries σ ℂ} (h : E ∈ dil σ) (l : σ) : X l * E ∈ dil σ := by
  intro r h0 h1
  have hρ0 := Real.sqrt_nonneg r
  have hρ1 : √r < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using h1)
  obtain ⟨C, hC⟩ := (tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1).bddAbove_range
  rw [← (add_left_injective (Finsupp.single l 1)).summable_iff
    fun α hα => by simp [(coeff_X_mul_of_notMem l E hα).2]]
  refine .of_nonneg_of_le (fun α => by dsimp; positivity) (fun β => ?_) ((h _ hρ0 hρ1).mul_left C)
  have h2 : ((β.degree + 1 : ℕ) : ℝ) * √r ^ (β.degree + 1) ≤ C := hC ⟨_, rfl⟩
  have h3 : (β l : ℝ) ≤ β.degree := Nat.cast_le.2 (Finsupp.le_degree l β)
  have h4 : r ^ (β.degree + 1) = √r ^ (β.degree + 1) * √r ^ (β.degree + 1) := by
    rw [← mul_pow, Real.mul_self_sqrt h0]
  have h5 : √r ^ (β.degree + 1) ≤ √r ^ β.degree := pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ _)
  simp only [Function.comp, coeff_X_mul_add, map_add, Finsupp.degree_single, Oscillator.mfact_add_single, h4]
  push_cast at h2 ⊢
  calc _ = (((β l : ℝ) + 1) * √r ^ (β.degree + 1)) *
        (√r ^ (β.degree + 1) * ((mfact β : ℝ) * ‖coeff β E‖ ^ 2)) := by ring
    _ ≤ (((β.degree : ℝ) + 1) * √r ^ (β.degree + 1)) *
        (√r ^ β.degree * ((mfact β : ℝ) * ‖coeff β E‖ ^ 2)) := by gcongr
    _ ≤ _ := by gcongr

def mulX (l : σ) : dil σ →ₗ[ℂ] dil σ := (LinearMap.mulLeft ℂ (X l)).restrict fun _ h => X_mul_mem h l

@[simp] theorem coe_mulX (l : σ) (E : dil σ) : (mulX l E : MvPowerSeries σ ℂ) = X l * (E : MvPowerSeries σ ℂ) := rfl

def term (t : ℝ) (E E' : MvPowerSeries σ ℂ) (α : σ →₀ ℕ) : ℂ :=
  (t : ℂ) ^ α.degree * ((mfact α : ℂ) * coeff α E * coeff α E')

omit [DecidableEq σ] in

theorem norm_term_le {t : ℝ} (ht : 0 ≤ t) (E E' : MvPowerSeries σ ℂ) (α : σ →₀ ℕ) :
    ‖term t E E' α‖ ≤ t ^ α.degree * ((mfact α : ℝ) * ‖coeff α E‖ ^ 2) +
      t ^ α.degree * ((mfact α : ℝ) * ‖coeff α E'‖ ^ 2) := by
  rw [term, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht,
    Complex.norm_natCast, ← mul_add, ← mul_add, mul_assoc]
  gcongr
  nlinarith [sq_nonneg (‖coeff α E‖ - ‖coeff α E'‖), norm_nonneg (coeff α E), norm_nonneg (coeff α E')]

omit [DecidableEq σ] in

theorem summable_norm_term {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (E E' : dil σ) :
    Summable fun α => ‖term t E.1 E'.1 α‖ :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le ht.1.le _ _)
    ((E.2 t ht.1.le ht.2).add (E'.2 t ht.1.le ht.2))

def pr {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : dil σ →ₗ[ℂ] dil σ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun E E' => ∑' α, term t E.1 E'.1 α)
    (fun E₁ E₂ E' => by
      rw [← (summable_norm_term ht E₁ E').of_norm.tsum_add (summable_norm_term ht E₂ E').of_norm]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_add, map_add]; ring)
    (fun c E E' => by
      rw [smul_eq_mul, ← tsum_mul_left]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_smul, coeff_smul]; ring)
    (fun E E₁ E₂ => by
      rw [← (summable_norm_term ht E E₁).of_norm.tsum_add (summable_norm_term ht E E₂).of_norm]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_add, map_add]; ring)
    (fun c E E' => by
      rw [smul_eq_mul, ← tsum_mul_left]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_smul, coeff_smul]; ring)

variable {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)

omit [DecidableEq σ] in

theorem pr_apply (E E' : dil σ) : pr ht E E' = ∑' α, term t E.1 E'.1 α := rfl

omit [DecidableEq σ] in

theorem pr_comm (E E' : dil σ) : pr ht E E' = pr ht E' E :=
  tsum_congr fun α => by simp only [term]; ring

def IsPDer (l : σ) (E D : MvPowerSeries σ ℂ) : Prop :=
  ∀ α : σ →₀ ℕ, ((α l : ℂ) + 1) * coeff (α + Finsupp.single l 1) E = coeff α D

theorem pr_mulX {l : σ} (E : dil σ) {E' D : dil σ} (h : IsPDer l E'.1 D.1) :
    pr ht (mulX l E) E' = t * pr ht E D := by
  rw [pr_apply, pr_apply, ← (add_left_injective (Finsupp.single l 1)).tsum_eq
    (fun α hα => by
      by_contra h'
      exact hα (by simp [term, (coeff_X_mul_of_notMem l _ h').2])), ← tsum_mul_left]
  refine tsum_congr fun β => ?_
  simp only [term, coe_mulX, coeff_X_mul_add, map_add, Finsupp.degree_single, Oscillator.mfact_add_single, ← h β]
  push_cast
  ring

theorem IsPDer.coeff_X_mul {l : σ} {E D : MvPowerSeries σ ℂ} (h : IsPDer l E D) (α : σ →₀ ℕ) :
    coeff α (X l * D) = (α l : ℂ) * coeff α E := by
  by_cases hα : α ∈ Set.range fun β : σ →₀ ℕ => β + Finsupp.single l 1
  · obtain ⟨β, rfl⟩ := hα
    simp [coeff_X_mul_add, ← h β]
  · simp [coeff_X_mul_of_notMem l D hα]

theorem IsPDer.X_mul {k : σ} {E D : MvPowerSeries σ ℂ} (h : IsPDer k E D) (m : σ) :
    IsPDer k (X m * E) (X m * D + (if k = m then (1 : ℂ) else 0) • E) := by
  intro α
  by_cases hk : k = m
  · subst hk
    rw [coeff_X_mul_add, map_add, h.coeff_X_mul]; simp; ring
  rw [if_neg hk, zero_smul, add_zero]
  by_cases hα : α ∈ Set.range fun β : σ →₀ ℕ => β + Finsupp.single m 1
  · obtain ⟨β, rfl⟩ := hα
    simp only
    rw [coeff_X_mul_add, add_right_comm, coeff_X_mul_add, ← h β]
    simp [Finsupp.single_apply, Ne.symm hk]
  · obtain ⟨h1, h2⟩ := coeff_X_mul_of_notMem m D hα
    rw [h2, (coeff_X_mul_of_notMem m E _).2, mul_zero]
    rintro ⟨β, hβ⟩
    have := congrArg (fun γ : σ →₀ ℕ => γ m) hβ
    simp [h1, hk] at this

variable [Fintype σ]

theorem hasDerivAt_pairing (E E' : dil σ) (D D' : σ → dil σ)
    (h : ∀ l, IsPDer l E.1 (D l).1) (h' : ∀ l, IsPDer l E'.1 (D' l).1) :
    HasDerivAt (fun s : ℝ => ∑' α, term s E.1 E'.1 α) (∑ l, pr ht (D l) (D' l)) t := by
  have hterm : ∀ s α, ∑ l, term s (mulX l (D l)).1 E'.1 α = (α.degree : ℂ) * term s E.1 E'.1 α := fun s α => by
    simp only [term, coe_mulX, (h _).coeff_X_mul, Finsupp.degree_eq_sum]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨r, htr, hr1⟩ := exists_between ht.2
  have hr : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1.trans htr, hr1⟩
  have hsum : Summable fun α : σ →₀ ℕ => r⁻¹ * ‖(α.degree : ℂ) * term r E.1 E'.1 α‖ := by
    refine Summable.mul_left _ ?_
    simp only [← hterm]
    exact (summable_sum fun l _ => (summable_norm_term hr (mulX l (D l)) E').of_norm).norm
  set c : (σ →₀ ℕ) → ℂ := fun α => (mfact α : ℂ) * coeff α (E : MvPowerSeries σ ℂ) *
    coeff α (E' : MvPowerSeries σ ℂ) with hc
  have hpow : ∀ s : ℝ, s ≠ 0 → ∀ n : ℕ, (n : ℂ) * (s : ℂ) ^ (n - 1) = (s : ℂ)⁻¹ * (n * (s : ℂ) ^ n) := by
    intro s hs n
    have : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; field_simp
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun α (s : ℝ) => term s E.1 E'.1 α)
    (g' := fun α (s : ℝ) => (α.degree : ℂ) * (s : ℂ) ^ (α.degree - 1) * c α) hsum isOpen_Ioo
    (isPreconnected_Ioo (a := 0) (b := r))
    (fun α s _ => ((hasDerivAt_pow α.degree (s : ℂ)).comp_ofReal).mul_const (c α))
    (fun α s hs => by
      have e : r⁻¹ * ‖(α.degree : ℂ) * term r E.1 E'.1 α‖ = ‖(α.degree : ℂ) * (r : ℂ) ^ (α.degree - 1) * c α‖ := by
        rw [hpow r hr.1.ne', mul_assoc, mul_assoc, norm_mul (r : ℂ)⁻¹, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg hr.1.le]
        rfl
      rw [e]
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.1.le, Real.norm_of_nonneg hs.1.le]
      gcongr
      exacts [hs.1.le, hs.2.le])
    ⟨ht.1, htr⟩ (summable_norm_term ht E E').of_norm ⟨ht.1, htr⟩
  refine key.congr_deriv ?_
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.1.ne'
  apply mul_left_cancel₀ ht0
  rw [Finset.mul_sum, ← tsum_mul_left]
  simp only [← fun l => pr_mulX ht (D l) (h' l)]
  simp only [pr_apply]
  rw [← Summable.tsum_finsetSum fun l _ => (summable_norm_term ht (mulX l (D l)) E').of_norm]
  refine tsum_congr fun α => ?_
  rw [hterm, hpow t ht.1.ne', term]
  simp only [hc]
  field_simp

theorem moments : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ) (E E' : MvPowerSeries σ ℂ), Summable (fun α : σ →₀ ℕ => (mfact α : ℝ) * ‖coeff α E‖ ^ 2) → Summable (fun α : σ →₀ ℕ => (mfact α : ℝ) * ‖coeff α E'‖ ^ 2) → (∀ l α, ((α l : ℂ) + 1) * coeff (α + Finsupp.single l 1) E = coeff α (x l • E + ∑ k, S l k • (X k * E))) → (∀ l α, ((α l : ℂ) + 1) * coeff (α + Finsupp.single l 1) E' = coeff α (y l • E' + ∑ k, T l k • (X k * E'))) → let f : ℝ → ℂ := fun s => ∑' α : σ →₀ ℕ, (s : ℂ) ^ α.degree * ((mfact α : ℂ) * coeff α E * coeff α E'); ContinuousOn f (Set.Icc 0 1) ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ (p q : σ → ℂ) (m n : Matrix σ σ ℂ), p = (t : ℂ) • (f t • y + T *ᵥ q) ∧ q = (t : ℂ) • (f t • x + S *ᵥ p) ∧ m = ((t : ℂ) * f t) • (1 : Matrix σ σ ℂ) + (t : ℂ) • vecMulVec y q + (t : ℂ) • (T * n) ∧ n = (t : ℂ) • vecMulVec x q + (t : ℂ) • (S * m) ∧ HasDerivAt f (f t * (x ⬝ᵥ y) + x ⬝ᵥ T *ᵥ q + y ⬝ᵥ S *ᵥ p + (S * m * Tᵀ).trace) t := by
  intro σ _ _ S T x y E E' hE hE' hd hd' f
  have hm : ∀ {G : MvPowerSeries σ ℂ}, Summable (fun α : σ →₀ ℕ => (mfact α : ℝ) * ‖coeff α G‖ ^ 2) →
      G ∈ dil σ := fun hG r h0 h1 =>
    .of_nonneg_of_le (fun α => by positivity)
      (fun α => mul_le_of_le_one_left (by positivity) (pow_le_one₀ h0 h1.le)) hG
  refine ⟨continuousOn_tsum (fun α => by fun_prop) (hE.add hE') fun α s hs => ?_, fun t ht => ?_⟩
  · refine (norm_term_le hs.1 E E' α).trans (add_le_add ?_ ?_) <;>
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hs.1 hs.2)
  let e : dil σ := ⟨E, hm hE⟩
  let e' : dil σ := ⟨E', hm hE'⟩
  have hD : ∀ l, IsPDer l (e : MvPowerSeries σ ℂ) (x l • e + ∑ k, S l k • mulX k e : dil σ).1 := fun l α => by
    simpa [e] using hd l α
  have hD' : ∀ l, IsPDer l (e' : MvPowerSeries σ ℂ) (y l • e' + ∑ k, T l k • mulX k e' : dil σ).1 :=
    fun l α => by simpa [e'] using hd' l α
  have hf : f t = pr ht e e' := rfl
  refine ⟨fun l => pr ht (mulX l e) e', fun l => pr ht e (mulX l e'),
    .of fun k m => pr ht (mulX k e) (mulX m e'), .of fun k m => pr ht e (mulX k (mulX m e')), ?_, ?_, ?_, ?_, ?_⟩
  · ext l
    simp [pr_mulX ht _ (hD' l), hf, mulVec, dotProduct, mul_comm]
  · ext l
    rw [pr_comm, pr_mulX ht _ (hD l), pr_comm]
    simp [hf, mulVec, dotProduct, mul_comm]
  · ext k m
    have h1 : IsPDer k (mulX m e' : MvPowerSeries σ ℂ) (mulX m (y k • e' + ∑ j, T k j • mulX j e') +
      (if k = m then (1 : ℂ) else 0) • e' : dil σ).1 := (hD' k).X_mul m
    have h2 : ∀ j, mulX m (mulX j e') = mulX j (mulX m e') := fun j => Subtype.ext (by simp [mul_left_comm])
    rw [of_apply, pr_mulX ht _ h1]
    by_cases hk : k = m <;> simp [hf, h2, hk, Matrix.mul_apply, vecMulVec_apply] <;> ring
  · ext k m
    rw [of_apply, pr_comm, pr_mulX ht _ (hD k), pr_comm]
    simp [Matrix.mul_apply, vecMulVec_apply, mul_add]
  · refine (hasDerivAt_pairing ht e e' _ _ hD hD').congr_deriv ?_
    simp only [hf, mulVec, dotProduct, trace, Matrix.diag_apply, Matrix.mul_apply, transpose_apply, of_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    have h1 : ∀ (g : σ → ℂ) (G : σ → σ → ℂ) (c : ℂ), ∑ m, T l m * (c * g m + ∑ k, S l k * G k m) =
        c * ∑ m, T l m * g m + ∑ m, (∑ k, S l k * G k m) * T l m := fun g G c => by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [h1 (fun m => pr ht e (mulX m e')) (fun k m => pr ht (mulX k e) (mulX m e'))]
    ring

end GlobalTheory.GaussInner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeOfImNeZero
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem denseRange_of_im_ne_zero {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (h : ∃ a, (σ a).im ≠ 0) :
    DenseRange σ := by
  obtain ⟨a, ha⟩ := h
  have hg : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * σ a := by fun_prop
  have hs : Function.Surjective fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * σ a := by
    intro z
    refine ⟨(z.re - z.im / (σ a).im * (σ a).re, z.im / (σ a).im), ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]
      field_simp
      ring
  have hq : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hc := hs.denseRange.comp hq hg
  refine hc.mono ?_
  rintro _ ⟨⟨p, q⟩, rfl⟩
  exact ⟨(p : K) + (q : K) * a, by simp⟩

theorem normAt_sq_eq_majAt_re {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : Formalism.HermitianLatticesTheory.normAt b X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem fnorm_cjv_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (s : Bool), (∀ a, (InfinitePlace.mk σ).embedding a = cj s (σ a)) → (∃ a, (σ a).im ≠ 0) → ∀ (A : HLat K) (d : ℕ) (L : Submodule (RingOfIntegers K) (Fin d → K)) (Xf : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (e : (Fin d → K) ≃ₗ[K] A.V), HLatTie A L Xf e → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : A.V →ₛₗ[σ] W) (c : W ≃ₗ[ℂ] (Fin d → ℂ)), (∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖j x‖) → (∀ x, c.symm (cpt σ x) = j (e x)) → ∀ w : W, Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s (c w)) = ‖w‖ := by
  intro K _ _ _ σ s htw hnr A d L Xf e hT W _ _ j c hn hc w
  have hd : DenseRange (cpt σ : (Fin d → K) → Fin d → ℂ) :=
    DenseRange.piMap (fun _ : Fin d => denseRange_of_im_ne_zero σ hnr)
  have hcj : Continuous (cj s) := by
    cases s
    · exact continuous_id
    · exact Complex.continuous_conj
  have h1 : Continuous fun z : Fin d → ℂ => Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s z) := by
    unfold Formalism.DivisionValues.fnorm Formalism.HermitianLatticesTheory.cnorm cjv Matrix.mulVec dotProduct
    fun_prop
  have h2 : Continuous fun z : Fin d → ℂ => ‖c.symm z‖ :=
    (LinearMap.continuous_of_finiteDimensional c.symm.toLinearMap).norm
  have key : ∀ z : Fin d → ℂ, Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s z) = ‖c.symm z‖ := by
    intro z
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    rw [hc, ← hn, normAt_sq_eq_majAt_re, hT.metric, ← normAt_sq_eq_majAt_re]
    have hv : cjv s (cpt σ x) = Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) (InfinitePlace.mk σ) x := by
      funext i
      simp [cjv, cpt, Formalism.HermitianLatticesTheory.vecAt, htw]
    rw [hv]
    rfl
  rw [key, c.symm_apply_apply]

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetConsColNeZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.Subst

theorem consCol_mulVec_map {E S : Type} [Field E] [CommRing S] (φ : E →+* S) {M : ℕ}
    (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (t : S) (w : Fin M → S) :
    ((Matrix.of fun i => Fin.cons (α := fun _ => E) (x 0 i) (B i) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) E).map φ).mulVec (Fin.cons t w) =
      t • (fun i => φ (x 0 i)) + (B.map φ).mulVec w := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

theorem det_consCol_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (h : StepData σ J x a B J') : (consCol x B).det ≠ 0 := by
  obtain ⟨-, ha, hx, hB, hJ', -, hd⟩ := h
  intro h0
  obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have e := consCol_mulVec_map (RingHom.id E) x B (v 0) (Fin.tail v)
  rw [Fin.cons_self_tail] at e
  have e' : v 0 • x 0 + B.mulVec (Fin.tail v) = 0 := by
    rw [← hPv]
    exact e.symm
  let r : Fin (M + 1) → E := Matrix.vecMul (fun i => σ (x 0 i)) J
  have hr : ∀ y, hE σ J (x 0) y = r ⬝ᵥ y := by
    intro y
    simp only [hE, Formalism.UG.hform, r, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have h1 : r ⬝ᵥ B.mulVec (Fin.tail v) = 0 := by
    rw [Matrix.dotProduct_mulVec]
    have : Matrix.vecMul r B = 0 := by
      funext j
      exact (hr _).symm.trans (hB j)
    rw [this, zero_dotProduct]
  have h2 : v 0 = 0 := by
    have := congrArg (fun y => r ⬝ᵥ y) e'
    simp only [dotProduct_add, h1, dotProduct_smul, ← hr (x 0), hx, add_zero, dotProduct_zero,
      smul_eq_mul, mul_eq_zero] at this
    rcases this with h | h
    · exact h
    · exact absurd ((map_eq_zero _).1 h) ha
  rw [h2, zero_smul, zero_add] at e'
  have h3 : J'.mulVec (Fin.tail v) = 0 := by
    rw [hJ', ← Matrix.mulVec_mulVec, e', Matrix.mulVec_zero]
  have h4 : Fin.tail v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hd h3
  apply hv
  rw [← Fin.cons_self_tail v, h2, h4]
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

theorem lintegral_subst (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (h1 : IsArtinianRing S) (h2 : IsReduced S) (lam : Measure S) (hl : lam.IsAddHaarMeasure) (M : ℕ)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) S) (hG : IsUnit G.det)
    (f : (Fin (M + 1) → S) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(Measure.pi fun _ => lam) =
      (modu S G.det : ℝ≥0∞) * ∫⁻ t, ∫⁻ y', f (G.mulVec (Fin.cons t (y' 0))) ∂(tupMeas lam 1 M) ∂lam := by
  have key := GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct S h1 h2 lam hl 1 (M + 1) G 1 hG (by simp)
  have hm1 : modu S 1 = 1 := (GlobalTheory.GaugeEx.modu_basic S).2.2.1
  rw [Matrix.det_one, hm1, pow_one, one_pow, mul_one] at key
  have hU : ∀ K : ℕ, MeasurePreserving (fun X : Fin 1 → Fin K → S => X 0) (tupMeas lam 1 K)
      (Measure.pi fun _ => lam) := fun K =>
    measurePreserving_funUnique (Measure.pi fun _ : Fin K => lam) (Fin 1)
  have hGc : Continuous fun z : Fin (M + 1) → S => G.mulVec z :=
    continuous_const.matrix_mulVec continuous_id
  have hlr : lrAct G (1 : Matrix (Fin 1) (Fin 1) S) = fun X _ => G.mulVec (X 0) := by
    funext X a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp [lrAct]
  have hlrm : Measurable (lrAct G (1 : Matrix (Fin 1) (Fin 1) S)) := by
    rw [hlr]
    exact measurable_pi_lambda _ fun _ => hGc.measurable.comp (measurable_pi_apply 0)
  have hfG : Measurable fun z : Fin (M + 1) → S => f (G.mulVec z) := hf.comp hGc.measurable
  have hP := (measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => lam) 0).symm
  have hc : ∀ p : S × (Fin M → S),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => S) 0).symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  calc ∫⁻ z, f z ∂(Measure.pi fun _ => lam)
      = ∫⁻ X, f (X 0) ∂(tupMeas lam 1 (M + 1)) := ((hU _).lintegral_comp hf).symm
    _ = (modu S G.det : ℝ≥0∞) * ∫⁻ X, f (G.mulVec (X 0)) ∂(tupMeas lam 1 (M + 1)) := by
        conv_lhs => rw [key]
        rw [lintegral_smul_measure, lintegral_map (f := fun X : Fin 1 → Fin (M + 1) → S => f (X 0))
          (hf.comp (measurable_pi_apply 0)) hlrm, hlr]
        rfl
    _ = (modu S G.det : ℝ≥0∞) * ∫⁻ z, f (G.mulVec z) ∂(Measure.pi fun _ => lam) := by
        rw [(hU _).lintegral_comp hfG]
    _ = _ := by
        congr 1
        rw [← hP.lintegral_comp hfG]
        refine (lintegral_prod _ (hfG.comp hP.measurable).aemeasurable).trans ?_
        refine lintegral_congr fun t => ?_
        have hm : Measurable fun w : Fin M → S => f (G.mulVec (Fin.cons t w)) := by
          have := (hfG.comp hP.measurable).comp (measurable_prodMk_left (x := t))
          convert this using 2 with w
          simp only [Function.comp, hc]
        rw [(hU M).lintegral_comp hm]
        simp only [Function.comp, hc]

theorem subst : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → ∀ (lam : Measure (R ⊗[F] E)), lam.IsAddHaarMeasure → ∀ (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E), g • ratTup (F := F) R x = y → ∀ f : (Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ z, f z ∂(Measure.pi fun _ => lam) = (modu (R ⊗[F] E) (inclR R (consCol x B).det) : ℝ≥0∞) * ∫⁻ t, ∫⁻ y', f (t • y 0 + pairOf R σ J B y g y' 1) ∂(tupMeas lam 1 M) ∂lam := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hR M J x a B J' hS lam hl g y hy f hf
  obtain ⟨n1, n2, -⟩ := GlobalTheory.GaugeEx.nice_tensor F E R hR
  have hP : IsUnit (inclR (F := F) R (consCol x B).det) :=
    (IsUnit.mk0 _ (det_consCol_ne_zero σ J x a B J' hS)).map _
  have hJ : IsUnit (JR (F := F) R J).det := by
    have : IsUnit (inclR (F := F) R J.det) := (IsUnit.mk0 _ hS.1.2).map _
    rwa [RingHom.map_det] at this
  set A : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) :=
    (HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)).val with hA
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have hU : Formalism.UG.cT (sigR R σ) A * JR R J * A = JR R J := (show HR R σ J from g).2
  have hN : A.det * sigR R σ A.det = 1 := by
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    apply hJ.mul_left_cancel
    rw [mul_one]
    conv_rhs => rw [← this]
    ring
  have hmA : modu (R ⊗[F] E) A.det = 1 := by
    rw [(GlobalTheory.GaugeEx.modu_eq_modu_norm F E σ hCM R A.det 1 hAu (by rw [map_one, hN])).2]
    exact (GlobalTheory.GaugeEx.modu_basic R).2.2.1
  have hdet : (A * (consCol x B).map (inclR (F := F) R)).det =
      A.det * inclR (F := F) R (consCol x B).det := by
    rw [Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [lintegral_subst (R ⊗[F] E) n1 n2 lam hl M (A * (consCol x B).map (inclR (F := F) R))
    (by rw [hdet]; exact hAu.mul hP) f hf, hdet,
    (GlobalTheory.GaugeEx.modu_basic (R ⊗[F] E)).2.1 _ _ hAu hP, hmA, one_mul]
  congr 1
  refine lintegral_congr fun t => lintegral_congr fun y' => congrArg f ?_
  rw [← Matrix.mulVec_mulVec, consCol, consCol_mulVec_map, Matrix.mulVec_add, Matrix.mulVec_smul]
  subst hy
  rfl

end GlobalTheory.GaugeEx.Subst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineCoverSquarePolarisationSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SquarePolCover.exists_cover : AmpleSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 2 ≤ n → ∃ (κ : Type)
    (s : κ → H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n),
    (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  intro hA R _ _ P n hn
  obtain ⟨κ, t, ht, hta⟩ := GlobalTheory.Algebraise.exists_cover hA P (2 * n) (by omega)
  have hm : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  choose s hs using fun i => GlobalTheory.T.linComb_pow_section_unflatten P.L 2 n ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) (t i)
  have key : ∀ i, nonzeroLocus (s i) = nonzeroLocus (t i) := by
    intro i
    ext x
    obtain ⟨j, hj⟩ := exists_chart P.isLB x
    have h₁ := GlobalTheory.SectionRingIso.mem_iff_isUnit (t i) (𝟙 _) x (j := fun _ => j) hj
    have h₂ := GlobalTheory.SectionRingIso.mem_iff_isUnit (s i) (𝟙 _) x (j := fun _ => fun _ => j)
      (GlobalTheory.SectionRingIso.mem_ch.2 hj)
    have h₃ := hs i P.A.left (𝟙 _) x j hj
    exact h₂.trans ((congrArg IsUnit h₃).to_iff.symm.trans h₁.symm)
  refine ⟨κ, s, ?_, fun i => ?_⟩
  · simp_rw [key]; exact ht
  · rw [key]; exact hta i
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyRealStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ ψ' : AddChar (AF F) ℂ), IsCharAF F ψ → IsCharAF F ψ' → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  first | exact @GlobalTheory.AdeleCharTwist.exists_mul_eq | exact GlobalTheory.AdeleCharTwist.exists_mul_eq | (intros; apply GlobalTheory.AdeleCharTwist.exists_mul_eq <;> assumption)
end

