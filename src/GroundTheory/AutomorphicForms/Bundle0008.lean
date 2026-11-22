import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinLineStage
import GroundTheory.AutomorphicForms.Bundle0006
import GroundTheory.AutomorphicForms.QuotientMeasure

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavinLineBounds
section
namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform

set_option linter.unusedSectionVars false

noncomputable section

namespace LineKernel

theorem tsupport_iteratedDeriv_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (m : ℕ) : tsupport (iteratedDeriv m f) ⊆ tsupport f := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem iteratedDeriv_eq_of_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℕ → ℝ → E} (h : ∀ m, deriv (Φ m) = Φ (m + 1)) (m : ℕ) : iteratedDeriv m (Φ 0) = Φ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ, ih, h]

theorem convolution_mul_eq_real (f g : ℝ → ℂ) : (f ⋆[mul ℂ ℂ] g) = (f ⋆[mul ℝ ℂ] g) := by
  funext x; simp only [convolution_def, mul_apply']

theorem iteratedDeriv_convolution {K g : ℝ → ℂ} (hK : LocallyIntegrable K) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (m : ℕ) :
    iteratedDeriv m (K ⋆[mul ℂ ℂ] g) = K ⋆[mul ℂ ℂ] iteratedDeriv m g := by
  have := iteratedDeriv_eq_of_deriv (Φ := fun m => K ⋆[mul ℂ ℂ] iteratedDeriv m g) (fun m => by
    funext x
    rw [convolution_mul_eq_real, convolution_mul_eq_real]
    rw [((hasCompactSupport_iteratedDeriv hgc m).hasDerivAt_convolution_right (mul ℝ ℂ) hK
      ((contDiff_iteratedDeriv_of_contDiff hg m).of_le (by simp)) x).deriv, ← iteratedDeriv_succ]) m
  simpa using this

theorem norm_convolution_le {K g : ℝ → ℂ} {B : ℝ} (hK : Integrable K) (hg : ∀ t, ‖g t‖ ≤ B)
    (x : ℝ) : ‖(K ⋆[mul ℂ ℂ] g) x‖ ≤ B * ∫ t, ‖K t‖ := by
  rw [convolution_mul, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun t => norm_nonneg _) (hK.norm.const_mul B)
    (Eventually.of_forall fun t => ?_))
  simp only [norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hg _) (norm_nonneg _)

section Bounds

variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

theorem integral_norm_KC_le_one (n : ℕ) : ∫ t, ‖KC a r n t‖ ≤ 1 := by
  have : (fun t => ‖KC a r n t‖) = Kc a r n := by
    funext t; simp [KC, Complex.norm_real, abs_of_nonneg (Kc_nonneg ha hr n t)]
  rw [this]; exact integral_Kc_le_one ha hr n

theorem contDiff_ρ (n : ℕ) : ContDiff ℝ ∞ (ρ a r n) := by
  cases n with
  | zero => exact contDiff_ηC a r 0
  | succ n =>
    simp only [ρ]
    exact ContDiff.sum fun p _ => contDiff_const.mul
      (contDiff_iteratedDeriv_of_contDiff (contDiff_conv_ηC ha hr n) p)

theorem support_ρ_subset (n : ℕ) : support (ρ a r n) ⊆ Icc 0 (Rs r n) := by
  cases n with
  | zero =>
    intro t ht
    have : t ∈ Icc (r 0) (2 * r 0) := by
      by_contra h; exact ht (by simp [ρ, ηC, rem_eq_zero (hr 0) h])
    exact ⟨(hr 0).le.trans this.1, by simpa [Rs] using this.2⟩
  | succ n =>
    have hs : tsupport (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) ⊆ Icc 0 (Rs r (n + 1)) := by
      refine closure_minimal ?_ isClosed_Icc
      refine (support_convolution_subset (mul ℂ ℂ)).trans ?_
      have h1 : support (KC a r n) ⊆ Icc 0 (Rs r n) := fun t ht =>
        support_Kc_subset ha hr n (by simpa [KC] using ht)
      have h2 : support (ηC a r (n + 1)) ⊆ Icc (r (n + 1)) (2 * r (n + 1)) := fun t ht =>
        support_rem_subset (hr (n + 1)) (by simpa [ηC] using ht)
      refine (Set.add_subset_add h1 h2).trans ((Set.Icc_add_Icc_subset _ _ _ _).trans
        (Icc_subset_Icc (by linarith [hr (n + 1)]) (le_of_eq ?_)))
      simp [Rs, Finset.sum_range_succ]
    intro t ht
    by_contra h
    apply ht
    simp only [ρ]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hs (tsupport_iteratedDeriv_subset p h'))),
      mul_zero]

theorem norm_iteratedDeriv_ηC (j q : ℕ) (t : ℝ) :
    ‖iteratedDeriv q (ηC a r j) t‖ = ‖iteratedDeriv q (rem (a j) (r j)) t‖ := by
  have := iteratedDeriv_ofReal (contDiff_rem (a j) (r j)) q
  show ‖iteratedDeriv q (fun t => ((rem (a j) (r j) t : ℝ) : ℂ)) t‖ = _
  rw [this, Complex.norm_real]

theorem norm_iteratedDeriv_ρ_succ_le (n m : ℕ) {B : ℕ → ℝ}
    (hB : ∀ q t, ‖iteratedDeriv q (rem (a (n + 1)) (r (n + 1))) t‖ ≤ B q) (t : ℝ) :
    ‖iteratedDeriv m (ρ a r (n + 1)) t‖ ≤
      ∑ p ∈ Finset.range (n + 2), coef a (n + 1) p * B (p + m) := by
  have hKi := (integrable_KC ha hr n).locallyIntegrable
  have hηc := contDiff_ηC a r (n + 1)
  have hηs := hasCompactSupport_ηC ha hr (n + 1)
  set Φ : ℕ → ℝ → ℂ := fun m u => ∑ p ∈ Finset.range (n + 2),
    (coef a (n + 1) p : ℂ) * (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u
    with hΦ
  have h0 : ρ a r (n + 1) = Φ 0 := by
    funext u
    simp only [ρ, hΦ, add_zero, iteratedDeriv_convolution hKi hηc hηs]
  have hd : ∀ m, deriv (Φ m) = Φ (m + 1) := by
    intro m; funext x
    have hsum := HasDerivAt.sum (u := Finset.range (n + 2))
      (A := fun p u => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u)
      (A' := fun p => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m + 1) (ηC a r (n + 1))) x) (x := x)
      (fun p _ => by
        refine HasDerivAt.const_mul _ ?_
        rw [convolution_mul_eq_real, convolution_mul_eq_real, iteratedDeriv_succ]
        exact (hasCompactSupport_iteratedDeriv hηs (p + m)).hasDerivAt_convolution_right
          (mul ℝ ℂ) hKi ((contDiff_iteratedDeriv_of_contDiff hηc _).of_le (by simp)) x)
    have e : Φ m = ∑ p ∈ Finset.range (n + 2), fun u => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u := by
      funext u; simp [hΦ, Finset.sum_apply]
    rw [e, hsum.deriv]
    simp only [hΦ, add_assoc]
  rw [h0, iteratedDeriv_eq_of_deriv hd m]
  simp only [hΦ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coef_nonneg ha _ _)]
  refine mul_le_mul_of_nonneg_left ?_ (coef_nonneg ha _ _)
  have hB' : ∀ u, ‖iteratedDeriv (p + m) (ηC a r (n + 1)) u‖ ≤ B (p + m) := fun u => by
    rw [norm_iteratedDeriv_ηC ha hr]; exact hB _ _
  refine (norm_convolution_le (integrable_KC ha hr n) hB' t).trans ?_
  have h1 := integral_norm_KC_le_one ha hr n
  have h2 : 0 ≤ B (p + m) := (norm_nonneg _).trans (hB (p + m) 0)
  have h3 : 0 ≤ ∫ t, ‖KC a r n t‖ := integral_nonneg fun t => norm_nonneg _
  nlinarith

theorem fourier_KC_zero (ξ : ℝ) : 𝓕 (KC a r 0) ξ = khat (a 0) (r 0) ξ := rfl

theorem fourier_KC_succ (n : ℕ) (ξ : ℝ) :
    𝓕 (KC a r (n + 1)) ξ = 𝓕 (KC a r n) ξ * khat (a (n + 1)) (r (n + 1)) ξ := by
  rw [KC_succ ha hr n, fourier_mul_convolution_eq (f₂ := kC a r (n + 1)) (integrable_KC ha hr n)
    (integrable_kern (ha (n + 1)).le (hr (n + 1))).ofReal]
  rfl

theorem norm_fourier_KC_le_one (n : ℕ) (ξ : ℝ) : ‖𝓕 (KC a r n) ξ‖ ≤ 1 := by
  induction n with
  | zero => rw [fourier_KC_zero ha hr]; exact norm_khat_le_one (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_KC_succ ha hr, norm_mul]
    exact mul_le_one₀ ih (norm_nonneg _) (norm_khat_le_one (ha _) (hr _) ξ)

theorem norm_fourier_KC_succ_sub_le (n : ℕ) (ξ : ℝ) :
    ‖𝓕 (KC a r (n + 1)) ξ - 𝓕 (KC a r n) ξ‖ ≤
      4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1)) := by
  rw [fourier_KC_succ ha hr, ← mul_sub_one, norm_mul]
  calc ‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ - 1‖
      ≤ 1 * (4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1))) :=
        mul_le_mul (norm_fourier_KC_le_one ha hr n ξ) (norm_khat_sub_one_le (ha _) (hr _) ξ)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem abs_pow_mul_norm_fourier_KC_le (n m : ℕ) (hmn : m ≤ n + 1) (ξ : ℝ) :
    |ξ| ^ m * ‖𝓕 (KC a r n) ξ‖ ≤ ∏ j ∈ Finset.range m, (a j / π) := by
  induction n generalizing m with
  | zero =>
    interval_cases m
    · simpa using norm_fourier_KC_le_one ha hr 0 ξ
    · simpa [fourier_KC_zero ha hr] using abs_mul_norm_khat_le (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_KC_succ ha hr, norm_mul]
    rcases Nat.lt_or_ge m (n + 2) with h | h
    · calc |ξ| ^ m * (‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ‖)
          ≤ |ξ| ^ m * (‖𝓕 (KC a r n) ξ‖ * 1) := by
            gcongr; exact norm_khat_le_one (ha _) (hr _) ξ
        _ ≤ _ := by rw [mul_one]; exact ih m (by omega)
    · obtain rfl : m = n + 2 := le_antisymm hmn h
      rw [Finset.prod_range_succ, pow_succ]
      calc |ξ| ^ (n + 1) * |ξ| * (‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ‖)
          = (|ξ| ^ (n + 1) * ‖𝓕 (KC a r n) ξ‖) * (|ξ| * ‖khat (a (n + 1)) (r (n + 1)) ξ‖) := by
            ring
        _ ≤ (∏ j ∈ Finset.range (n + 1), (a j / π)) * (a (n + 1) / π) :=
            mul_le_mul (ih (n + 1) le_rfl) (abs_mul_norm_khat_le (ha _) (hr _) ξ)
              (by positivity) (Finset.prod_nonneg fun j _ => div_nonneg (ha j).le pi_pos.le)

end Bounds

theorem coef_mono {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (n p : ℕ) : coef a n p ≤ coef a (n + 1) p := by
  cases p with
  | zero => simp [coef]
  | succ p => simp only [coef]; linarith [div_nonneg (coef_nonneg ha n p) (ha n).le]

theorem coef_le_of {a β : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hβ0 : β 0 = 1) (hβp : ∀ p, 0 ≤ β p)
    (hβ : ∀ n p, 1 ≤ p → p ≤ n + 1 → (a n)⁻¹ * β (p - 1) ≤ (1 / 2) ^ (n + 1) * β p)
    (n p : ℕ) : coef a n p ≤ β p := by
  have key : ∀ n p, 1 ≤ p → coef a n p ≤ β p * (1 - (1 / 2) ^ n) := by
    intro n
    induction n with
    | zero =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp [coef]
    | succ n ih =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [coef]
      have h1 := ih (q + 1) (by omega)
      have h2 : coef a n q / a n ≤ (1 / 2) ^ (n + 1) * β (q + 1) := by
        rcases Nat.lt_or_ge n q with hq | hq
        · rw [coef_eq_zero a hq, zero_div]
          have := hβ n (q + 1) (by omega)
          have hb : 0 ≤ β (q + 1) := hβp _
          positivity
        · have hc : coef a n q ≤ β q := by
            rcases Nat.eq_zero_or_pos q with rfl | hq0
            · rw [coef_zero_right, hβ0]
            · have := ih q hq0
              have hbq : 0 ≤ β q := hβp q
              nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
          have := hβ n (q + 1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel] at this
          calc coef a n q / a n = (a n)⁻¹ * coef a n q := by ring
            _ ≤ (a n)⁻¹ * β q := mul_le_mul_of_nonneg_left hc (inv_nonneg.2 (ha n).le)
            _ ≤ _ := this
      calc coef a n (q + 1) + coef a n q / a n
          ≤ β (q + 1) * (1 - (1 / 2) ^ n) + (1 / 2) ^ (n + 1) * β (q + 1) := add_le_add h1 h2
        _ = β (q + 1) * (1 - (1 / 2) ^ (n + 1)) := by ring
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [coef_zero_right, hβ0]
  · have := key n p hp
    nlinarith [hβp p, pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

end LineKernel

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.HaarCosets
section
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [IsFiniteMeasureOnCompacts μ]

theorem integral_eq_smul_finsum_coset (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    ∫ g, f g ∂μ = μ.real (K : Set G) • ∑ᶠ x : G ⧸ (K : Subgroup G), f x.out := by
  set S := (finite_image_mk_tsupport K hf).toFinset with hS
  have hmeas : ∀ g : G, MeasurableSet (g • (K : Set G)) := fun g =>
    (K.isOpen.smul g).measurableSet
  have hfin : ∀ g : G, μ (g • (K : Set G)) ≠ ∞ := fun g =>
    (hKc.smul g).measure_lt_top.ne
  have hvol : ∀ g : G, μ.real (g • (K : Set G)) = μ.real (K : Set G) := fun g => by
    simp [Measure.real, measure_smul]
  have hdec := eq_sum_indicator_coset K hf hK
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · calc ∫ g, f g ∂μ
        = ∫ g, ∑ x ∈ S, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_congr_ae (Eventually.of_forall fun g => by
            rw [congrFun hdec g, Finset.sum_apply])
      _ = ∑ x ∈ S, ∫ g, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_finsetSum _ fun x _ =>
            (integrable_indicator_iff (hmeas _)).2 (integrableOn_const (hfin _))
      _ = μ.real (K : Set G) • ∑ x ∈ S, f x.out := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [integral_indicator_const _ (hmeas _), hvol]
  · intro x hx
    rw [hS, Set.Finite.coe_toFinset]
    exact ⟨x.out, subset_tsupport f hx, QuotientGroup.out_eq' x⟩

end Integral

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.QuotientRightRegular
section
open MeasureTheory Topology Filter Set
open scoped ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

theorem compMeasurePreserving_congr {α : Type*} [MeasurableSpace α] {ν : Measure α} {p : ℝ≥0∞}
    {f f' : α → α} (h : f = f') (hf : MeasurePreserving f ν ν) (hf' : MeasurePreserving f' ν ν)
    (φ : Lp ℂ p ν) :
    Lp.compMeasurePreserving f hf φ = Lp.compMeasurePreserving f' hf' φ := by
  subst h
  rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
  [μ.IsMulRightInvariant]

def rightTranslate (g : G) :
    Lp ℂ 2 (quotientMeasure Γ μ) ≃ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure Γ μ) where
  toLinearEquiv :=
    { Lp.compMeasurePreservingₗ ℂ (rightMul Γ g) (measurePreserving_rightMul μ g) with
      invFun := Lp.compMeasurePreservingₗ ℂ (rightMul Γ g⁻¹) (measurePreserving_rightMul μ g⁻¹)
      left_inv := fun φ ↦ by
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ) = φ
        rw [← Lp.compMeasurePreserving_comp_apply, compMeasurePreserving_congr _ _
          (MeasurePreserving.id _), Lp.compMeasurePreserving_id_apply]
        rw [← rightMul_mul, inv_mul_cancel, rightMul_one]
      right_inv := fun φ ↦ by
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ) = φ
        rw [← Lp.compMeasurePreserving_comp_apply, compMeasurePreserving_congr _ _
          (MeasurePreserving.id _), Lp.compMeasurePreserving_id_apply]
        rw [← rightMul_mul, mul_inv_cancel, rightMul_one] }
  norm_map' φ := Lp.norm_compMeasurePreserving φ _

theorem rightTranslate_apply (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightTranslate Γ μ g φ =
      Lp.compMeasurePreserving (rightMul Γ g) (measurePreserving_rightMul μ g) φ :=
  rfl

theorem coeFn_rightTranslate (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightTranslate Γ μ g φ =ᵐ[quotientMeasure Γ μ] fun x ↦ φ (rightMul Γ g x) :=
  Lp.coeFn_compMeasurePreserving φ _

def rightRegular : G →* (Lp ℂ 2 (quotientMeasure Γ μ) ≃ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure Γ μ)) where
  toFun := rightTranslate Γ μ
  map_one' := by
    ext1 φ
    change Lp.compMeasurePreserving _ _ φ = φ
    rw [compMeasurePreserving_congr (rightMul_one Γ) _ (MeasurePreserving.id _),
      Lp.compMeasurePreserving_id_apply]
  map_mul' g h := by
    ext1 φ
    rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
    change Lp.compMeasurePreserving _ _ φ =
      Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ)
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact compMeasurePreserving_congr (rightMul_mul Γ g h) _ _ φ

@[simp]
theorem rightRegular_apply (g : G) : rightRegular Γ μ g = rightTranslate Γ μ g :=
  rfl

def rightRegularUnitary :
    G →* unitary (Lp ℂ 2 (quotientMeasure Γ μ) →L[ℂ] Lp ℂ 2 (quotientMeasure Γ μ)) :=
  (Unitary.linearIsometryEquiv (𝕜 := ℂ)).symm.toMonoidHom.comp (rightRegular Γ μ)

theorem rightRegularUnitary_apply (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    (rightRegularUnitary Γ μ g : Lp ℂ 2 (quotientMeasure Γ μ) →L[ℂ] _) φ = rightRegular Γ μ g φ :=
  rfl

theorem inner_rightRegular (g : G) (φ ψ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    inner ℂ (rightRegular Γ μ g φ) (rightRegular Γ μ g ψ) = inner ℂ φ ψ :=
  (rightRegular Γ μ g).inner_map_map φ ψ

section Continuity

variable [IsFiniteMeasureOnCompacts μ]

omit [μ.IsMulRightInvariant] in

theorem tendsto_lintegral_rightMul_sub {ψ : RightCosetSpace Γ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (g₀ : G) :
    Tendsto (fun g ↦ ∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
      ∂quotientMeasure Γ μ) (𝓝 g₀) (𝓝 0) := by
  obtain ⟨N, hN, hNn⟩ := exists_compact_mem_nhds g₀
  set K : Set (RightCosetSpace Γ) :=
    (fun p : RightCosetSpace Γ × G ↦ rightMul Γ p.2⁻¹ p.1) '' (tsupport ψ ×ˢ N) with hKdef
  have hK : IsCompact K := (hs.prod hN).image
    ((continuous_rightMul_prod Γ).comp (continuous_fst.prodMk continuous_snd.inv))
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  have hzero : ∀ g ∈ N, ∀ x ∉ K, ψ (rightMul Γ g x) = 0 := by
    intro g hg x hx
    by_contra h
    refine hx ⟨(rightMul Γ g x, g), ⟨subset_tsupport ψ h, hg⟩, ?_⟩
    change rightMul Γ g⁻¹ (rightMul Γ g x) = x
    rw [rightMul_rightMul, mul_inv_cancel, rightMul_one, id]
  have hg₀N : g₀ ∈ N := mem_of_mem_nhds hNn
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * M) ^ (2 : ℝ) with hc_def
  have hmeas : ∀ g, Measurable fun x ↦ ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ) :=
    fun g ↦ (((hc.comp (continuous_rightMul Γ g)).sub
      (hc.comp (continuous_rightMul Γ g₀))).measurable.enorm).pow_const _
  suffices key : Tendsto (fun g ↦ ∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
      ∂quotientMeasure Γ μ) (𝓝 g₀) (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂quotientMeasure Γ μ)) by
    rwa [lintegral_zero] at key
  refine tendsto_lintegral_filter_of_dominated_convergence (K.indicator fun _ ↦ c)
    (Eventually.of_forall hmeas) ?_ ?_ ?_
  · filter_upwards [hNn] with g hg
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖
          ≤ ‖ψ (rightMul Γ g x)‖ + ‖ψ (rightMul Γ g₀ x)‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hM (rightMul Γ g x), hM (rightMul Γ g₀ x)]
    · rw [hzero g hg x hx, hzero g₀ hg₀N x hx, sub_self, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
  · rw [lintegral_indicator_const hK.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hK.measure_lt_top.ne
  · refine Eventually.of_forall fun x ↦ ?_
    have hcont : Continuous fun g ↦ ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ) :=
      (ENNReal.continuous_rpow_const).comp (continuous_enorm.comp
        ((hc.comp ((continuous_rightMul_prod Γ).comp
          (continuous_const.prodMk continuous_id))).sub continuous_const))
    have := hcont.tendsto g₀
    rwa [sub_self, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at this

theorem tendsto_rightRegular_of_continuous {ψ : RightCosetSpace Γ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (g₀ : G) :
    Tendsto (fun g ↦ rightRegular Γ μ g ((hc.memLp_of_hasCompactSupport hs).toLp ψ)) (𝓝 g₀)
      (𝓝 (rightRegular Γ μ g₀ ((hc.memLp_of_hasCompactSupport hs).toLp ψ))) := by
  have hψ : MemLp ψ 2 (quotientMeasure Γ μ) := hc.memLp_of_hasCompactSupport hs
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hae : ∀ g, ⇑(rightRegular Γ μ g (hψ.toLp ψ)) =ᵐ[quotientMeasure Γ μ]
      fun x ↦ ψ (rightMul Γ g x) := fun g ↦
    (coeFn_rightTranslate Γ μ g _).trans
      ((measurePreserving_rightMul μ g).quasiMeasurePreserving.ae_eq_comp hψ.coeFn_toLp)
  have heq : ∀ g, eLpNorm (⇑(rightRegular Γ μ g (hψ.toLp ψ)) - ⇑(rightRegular Γ μ g₀ (hψ.toLp ψ)))
      2 (quotientMeasure Γ μ) = (∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
        ∂quotientMeasure Γ μ) ^ (1 / (2 : ℝ)) := fun g ↦ by
    rw [eLpNorm_congr_ae ((hae g).sub (hae g₀)),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
  simp_rw [heq]
  have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp
    (tendsto_lintegral_rightMul_sub Γ μ hc hs g₀)
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

theorem continuous_rightRegular_apply (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    Continuous fun g ↦ rightRegular Γ μ g φ := by
  refine continuous_iff_continuousAt.2 fun g₀ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨ψ, hs, hψφ, hc, hmem⟩ := (Lp.memLp φ).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 4)) (by simpa using hε4)
  set φ₀ : Lp ℂ 2 (quotientMeasure Γ μ) := (hc.memLp_of_hasCompactSupport hs).toLp ψ
  have hd : dist φ φ₀ ≤ ε / 4 := by
    rw [Lp.dist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub (MemLp.coeFn_toLp _))]
    exact ENNReal.toReal_le_of_le_ofReal hε4.le hψφ
  filter_upwards [Metric.tendsto_nhds.1 (tendsto_rightRegular_of_continuous Γ μ hc hs g₀) (ε / 4)
    hε4] with g hg
  calc dist (rightRegular Γ μ g φ) (rightRegular Γ μ g₀ φ)
      ≤ dist (rightRegular Γ μ g φ) (rightRegular Γ μ g φ₀) +
          (dist (rightRegular Γ μ g φ₀) (rightRegular Γ μ g₀ φ₀) +
            dist (rightRegular Γ μ g₀ φ₀) (rightRegular Γ μ g₀ φ)) :=
        (dist_triangle _ _ _).trans (add_le_add le_rfl (dist_triangle _ _ _))
    _ = dist φ φ₀ + (dist (rightRegular Γ μ g φ₀) (rightRegular Γ μ g₀ φ₀) + dist φ₀ φ) := by
        rw [LinearIsometryEquiv.dist_map, LinearIsometryEquiv.dist_map]
    _ < ε := by
        rw [dist_comm φ₀ φ]
        linarith

theorem continuous_rightRegular_prod :
    Continuous fun p : G × Lp ℂ 2 (quotientMeasure Γ μ) ↦ rightRegular Γ μ p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun ⟨g₀, φ₀⟩ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have h1 := (continuous_rightRegular_apply Γ μ φ₀).tendsto g₀
  have h2 : ∀ᶠ p : G × Lp ℂ 2 (quotientMeasure Γ μ) in 𝓝 (g₀, φ₀),
      dist (rightRegular Γ μ p.1 φ₀) (rightRegular Γ μ g₀ φ₀) < ε / 2 :=
    (Metric.tendsto_nhds.1 h1 (ε / 2) (by positivity)).prod_inl_nhds φ₀
  have h3 : ∀ᶠ p : G × Lp ℂ 2 (quotientMeasure Γ μ) in 𝓝 (g₀, φ₀), dist p.2 φ₀ < ε / 2 :=
    (Metric.tendsto_nhds.1 tendsto_id (ε / 2) (by positivity)).prod_inr_nhds g₀
  filter_upwards [h2, h3] with p hp2 hp3
  calc dist (rightRegular Γ μ p.1 p.2) (rightRegular Γ μ g₀ φ₀)
      ≤ dist (rightRegular Γ μ p.1 p.2) (rightRegular Γ μ p.1 φ₀) +
          dist (rightRegular Γ μ p.1 φ₀) (rightRegular Γ μ g₀ φ₀) := dist_triangle _ _ _
    _ = dist p.2 φ₀ + dist (rightRegular Γ μ p.1 φ₀) (rightRegular Γ μ g₀ φ₀) := by
        rw [LinearIsometryEquiv.dist_map]
    _ < ε := by linarith

end Continuity

end RightCosetSpace

end

end GroundTheory.Automorphic
end

