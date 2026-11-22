import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralLeftVerticalLineBound
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.ExplZeta.LeftShift

lemma rpow_le_exp_half {x σ : ℝ} (hx : 2 ≤ x) (hσ : σ ≤ 0) :
    x ^ σ ≤ Real.exp (σ / 2) := by
  have h1 : x ^ σ ≤ (2 : ℝ) ^ σ := Real.rpow_le_rpow_of_nonpos (by norm_num) hx hσ
  have h2 : (2 : ℝ) ^ σ = Real.exp (Real.log 2 * σ) := Real.rpow_def_of_pos (by norm_num) σ
  have h3 : Real.log 2 * σ ≤ σ / 2 := by
    have := Real.log_two_gt_d9
    nlinarith
  calc x ^ σ ≤ (2 : ℝ) ^ σ := h1
    _ = Real.exp (Real.log 2 * σ) := h2
    _ ≤ Real.exp (σ / 2) := Real.exp_le_exp.mpr h3

lemma poly_mul_exp_le {σ : ℝ} (hσ : σ ≤ 0) :
    (2 + |σ|) * Real.exp (σ / 2) ≤ 4 * Real.exp (σ / 4) := by
  rw [abs_of_nonpos hσ]
  have h1 : -σ / 4 + 1 ≤ Real.exp (-σ / 4) := Real.add_one_le_exp _
  have h2 : Real.exp (σ / 2) = Real.exp (σ / 4) * Real.exp (σ / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-σ / 4) * Real.exp (σ / 4) = 1 := by
    rw [← Real.exp_add]; simp [show -σ / 4 + σ / 4 = 0 by ring]
  have hp := Real.exp_pos (σ / 4)
  have h4 : (2 + -σ) * Real.exp (σ / 4) ≤ 4 := by
    have : (2 + -σ) * Real.exp (σ / 4) ≤ 4 * Real.exp (-σ / 4) * Real.exp (σ / 4) := by
      apply mul_le_mul_of_nonneg_right _ hp.le
      linarith
    calc _ ≤ _ := this
      _ = 4 * (Real.exp (-σ / 4) * Real.exp (σ / 4)) := by ring
      _ = 4 := by rw [h3]; ring
  rw [h2]
  calc (2 + -σ) * (Real.exp (σ / 4) * Real.exp (σ / 4))
      = ((2 + -σ) * Real.exp (σ / 4)) * Real.exp (σ / 4) := by ring
    _ ≤ 4 * Real.exp (σ / 4) := mul_le_mul_of_nonneg_right h4 hp.le

lemma norm_quot {g s : ℂ} {x : ℝ} (hx : 2 ≤ x) :
    ‖g * (x : ℂ) ^ s / s‖ = ‖g‖ * x ^ s.re / ‖s‖ := by
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]

lemma horiz_bound {g s : ℂ} {A x : ℝ} (hA : 0 ≤ A) (hx : 2 ≤ x) (hs : s.re ≤ 0)
    (him : 1 ≤ |s.im|) (hg : ‖g‖ ≤ A * (1 + |s.re| + |s.im|)) :
    ‖g * (x : ℂ) ^ s / s‖ ≤ 4 * A * Real.exp (s.re / 4) := by
  rw [norm_quot hx]
  have hn : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hnpos : 0 < ‖s‖ := by linarith
  have hxp : 0 ≤ x ^ s.re := Real.rpow_nonneg (by linarith) _
  have h1 : ‖g‖ ≤ A * (2 + |s.re|) * ‖s‖ := by
    refine hg.trans ?_
    have h0 := abs_nonneg s.re
    have : 1 + |s.re| + |s.im| ≤ (2 + |s.re|) * ‖s‖ := by nlinarith
    calc A * (1 + |s.re| + |s.im|) ≤ A * ((2 + |s.re|) * ‖s‖) :=
          mul_le_mul_of_nonneg_left this hA
      _ = _ := by ring
  rw [div_le_iff₀ hnpos]
  have h2 := rpow_le_exp_half hx hs
  have h3 := poly_mul_exp_le hs
  calc ‖g‖ * x ^ s.re ≤ (A * (2 + |s.re|) * ‖s‖) * Real.exp (s.re / 2) :=
        mul_le_mul h1 h2 hxp (le_trans (norm_nonneg _) h1)
    _ = A * ((2 + |s.re|) * Real.exp (s.re / 2)) * ‖s‖ := by ring
    _ ≤ A * (4 * Real.exp (s.re / 4)) * ‖s‖ := by
        apply mul_le_mul_of_nonneg_right _ hnpos.le
        exact mul_le_mul_of_nonneg_left h3 hA
    _ = _ := by ring

lemma left_bound {g s : ℂ} {A x B : ℝ} (hA : 0 ≤ A) (hx : 2 ≤ x) (hs : s.re ≤ -1)
    (hB : |s.im| ≤ B) (hg : ‖g‖ ≤ A * (1 + |s.re| + |s.im|)) :
    ‖g * (x : ℂ) ^ s / s‖ ≤ A * (1 + |s.re| + B) * Real.exp (s.re / 2) := by
  rw [norm_quot hx]
  have hn : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hre : 1 ≤ |s.re| := by rw [abs_of_nonpos (by linarith)]; linarith
  have hn1 : 1 ≤ ‖s‖ := by linarith
  have hxp : 0 ≤ x ^ s.re := Real.rpow_nonneg (by linarith) _
  have h1 : ‖g‖ ≤ A * (1 + |s.re| + B) := by
    refine hg.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  have h2 := rpow_le_exp_half hx (show s.re ≤ 0 by linarith)
  calc ‖g‖ * x ^ s.re / ‖s‖ ≤ ‖g‖ * x ^ s.re :=
        div_le_self (mul_nonneg (norm_nonneg _) hxp) hn1
    _ ≤ _ := mul_le_mul h1 h2 hxp (le_trans (norm_nonneg _) h1)

lemma integral_exp_quarter {R : ℝ} :
    ∫ σ : ℝ in (-R)..(-(1 / 2)), Real.exp (σ / 4)
      = 4 * (Real.exp (-(1 / 2) / 4) - Real.exp (-R / 4)) := by
  have hd : ∀ σ ∈ Set.uIcc (-R) (-(1 / 2) : ℝ),
      HasDerivAt (fun σ : ℝ => 4 * Real.exp (σ / 4)) (Real.exp (σ / 4)) σ := by
    intro σ _
    have h := ((hasDerivAt_id' σ).div_const 4).exp.const_mul 4
    exact h.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_id.div_const 4)).intervalIntegrable _ _)]
  ring

lemma horiz_integral {f : ℝ → ℂ} {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R)
    (h : ∀ σ : ℝ, -R ≤ σ → σ ≤ -(1 / 2) → ‖f σ‖ ≤ 4 * A * Real.exp (σ / 4)) :
    ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f σ‖ ≤ 16 * A := by
  have hle : (-R) ≤ (-(1 / 2) : ℝ) := by linarith
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f)
    (g := fun σ => 4 * A * Real.exp (σ / 4)) hle
    (Eventually.of_forall fun σ hσ => h σ hσ.1.le hσ.2)
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 4))
      ).intervalIntegrable _ _)
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul, integral_exp_quarter]
  have e1 : Real.exp (-(1 / 2) / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have e2 := Real.exp_pos (-R / 4)
  nlinarith

theorem main : ∃ K : ℝ, 0 < K ∧ ∀ (G : ℂ → ℂ) (A x a b : ℝ), 0 ≤ A → 2 ≤ x → a ≤ b → 1 ≤ |a| → 1 ≤ |b| → (∀ s : ℂ, s.re ≤ -(1 / 2) → a ≤ s.im → s.im ≤ b → DifferentiableAt ℂ G s ∧ ‖G s‖ ≤ A * (1 + |s.re| + |s.im|)) → ‖∫ t : ℝ in a..b, G (((-(1/2) : ℝ) : ℂ) + t * I) * (x : ℂ) ^ (((-(1/2) : ℝ) : ℂ) + t * I) / (((-(1/2) : ℝ) : ℂ) + t * I)‖ ≤ K * A := by
  refine ⟨32, by norm_num, ?_⟩
  intro G A x a b hA hx hab ha hb hG
  have hxC : (x : ℂ) ≠ 0 := by
    have : x ≠ 0 := by linarith
    exact_mod_cast this
  set f : ℂ → ℂ := fun s => G s * (x : ℂ) ^ s / s with hf
  set B : ℝ := max |a| |b| with hBdef
  have hB0 : 0 ≤ B := (abs_nonneg a).trans (le_max_left _ _)
  have key : ∀ R : ℝ, 1 ≤ R →
      ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖
        ≤ 32 * A + (b - a) * (A * (1 + R + B) * Real.exp (-R / 2)) := by
    intro R hR
    have H : DifferentiableOn ℂ f
        (Set.uIcc (-R) (-(1 / 2)) ×ℂ Set.uIcc a b) := by
      intro s hs
      rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le hab] at hs
      obtain ⟨⟨_, h2⟩, ⟨h3, h4⟩⟩ := hs
      have hs0 : s ≠ 0 := by
        intro h0
        rw [h0] at h2
        norm_num at h2
      have hd := (hG s h2 h3 h4).1
      have hc : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
        (differentiableAt_id).const_cpow (Or.inl hxC)
      exact ((hd.mul hc).div differentiableAt_id hs0).differentiableWithinAt
    have rect : (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I))
        - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I))
        + I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))
        - I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)) = 0 :=
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨-R, a⟩ ⟨-(1 / 2), b⟩ H
    have horiz : ∀ τ : ℝ, a ≤ τ → τ ≤ b → 1 ≤ |τ| →
        ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + τ * I)‖ ≤ 16 * A := by
      intro τ h1 h2 h3
      refine horiz_integral hA hR fun σ _ hσ => ?_
      have hre : ((σ : ℂ) + τ * I).re = σ := by simp
      have him : ((σ : ℂ) + τ * I).im = τ := by simp
      have hg := (hG (σ + τ * I) (by rw [hre]; exact hσ) (by rw [him]; exact h1)
        (by rw [him]; exact h2)).2
      have := horiz_bound (s := (σ : ℂ) + τ * I) hA hx (by rw [hre]; linarith)
        (by rw [him]; exact h3) hg
      rwa [hre] at this
    have hleft : ‖∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)‖
        ≤ (b - a) * (A * (1 + R + B) * Real.exp (-R / 2)) := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
        (f := fun t : ℝ => f (((-R : ℝ) : ℂ) + t * I))
        (C := A * (1 + R + B) * Real.exp (-R / 2)) ?_
      · rw [abs_of_nonneg (by linarith)] at h1
        linarith
      · intro t ht
        rw [Set.uIoc_of_le hab] at ht
        have hre : (((-R : ℝ) : ℂ) + t * I).re = -R := by simp
        have him : (((-R : ℝ) : ℂ) + t * I).im = t := by simp
        have hg := (hG (((-R : ℝ) : ℂ) + t * I) (by rw [hre]; linarith)
          (by rw [him]; exact ht.1.le) (by rw [him]; exact ht.2)).2
        have htB : |t| ≤ B := by
          rw [abs_le]
          constructor
          · have := neg_abs_le a
            have := le_max_left |a| |b|
            linarith [ht.1]
          · have := le_abs_self b
            have := le_max_right |a| |b|
            linarith [ht.2]
        have := left_bound (s := ((-R : ℝ) : ℂ) + t * I) (B := B) hA hx
          (by rw [hre]; linarith) (by rw [him]; exact htB) hg
        rw [hre, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R)] at this
        exact this
    have hI : ‖I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))‖
        = ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have hI' : ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖
        = ‖∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have heq : I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))
        = (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I))
          - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I))
          + I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)) := by
      linear_combination rect
    have hha := horiz a le_rfl hab ha
    have hhb := horiz b hab le_rfl hb
    rw [← hI, heq]
    calc _ ≤ ‖(∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I))
            - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I))‖
            + ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖ := norm_add_le _ _
      _ ≤ ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I)‖
            + ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I)‖
            + ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by rw [hI']; linarith
  have hlim : Tendsto (fun u : ℝ => 32 * A + (b - a) * (A * (1 + 2 * u + B) * Real.exp (-(2 * u) / 2)))
      atTop (𝓝 (32 * A)) := by
    have e0 : Tendsto (fun u : ℝ => u ^ 0 * Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    have e1 : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h := ((e0.const_mul (1 + B)).add (e1.const_mul 2)).const_mul ((b - a) * A)
    have h' := h.const_add (32 * A)
    simp only [mul_zero, add_zero] at h'
    refine h'.congr fun u => ?_
    have : -(2 * u) / 2 = -u := by ring
    rw [this]
    ring
  have hev : ∀ᶠ u : ℝ in atTop,
      ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖
        ≤ 32 * A + (b - a) * (A * (1 + 2 * u + B) * Real.exp (-(2 * u) / 2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    exact key (2 * u) (by linarith)
  exact ge_of_tendsto hlim hev

end GlobalTheory.CompanionTheory.ExplZeta.LeftShift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolution
section
namespace GlobalTheory.CompanionTheory.DiagDom

theorem perturb_bound {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → κ → ℝ) (ε C : ℝ)
    (hW : ∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) (c : κ → ℝ)
    (hC : ∀ i, |c i| ≤ C) (σ : κ) :
    |∑ i, W σ i * c i - c σ| ≤ (Fintype.card κ : ℝ) * ε * C := by
  have hrw : ∑ i, W σ i * c i - c σ = ∑ i, (W σ i - if σ = i then 1 else 0) * c i := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [hrw]
  calc |∑ i, (W σ i - if σ = i then 1 else 0) * c i|
      ≤ ∑ i, |(W σ i - if σ = i then 1 else 0) * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : κ, ε * C := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hW σ i).le (hC i) (abs_nonneg _) ((abs_nonneg _).trans (hW σ i).le)
    _ = (Fintype.card κ : ℝ) * ε * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem small_perturbation_injective_pos :
    ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ,
      (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
      (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
      ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) →
        (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  intro κ _ _ M
  have hn0 : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hM1 : 0 < |M| + 1 := by positivity
  refine ⟨1 / (2 * ((Fintype.card κ : ℝ) + 1) * (|M| + 1)), by positivity, fun W hW => ?_⟩
  set n : ℝ := (Fintype.card κ : ℝ) with hn
  set ε := 1 / (2 * (n + 1) * (|M| + 1)) with hε
  have hδ : n * ε * (2 * (|M| + 1)) ≤ 1 := by
    have e : n * ε * (2 * (|M| + 1)) = n / (n + 1) := by
      rw [hε]
      field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hε0 : 0 < ε := by positivity
  have hδ0 : 0 ≤ n * ε := by positivity
  have hδh : n * ε ≤ 1 / 2 := by nlinarith [abs_nonneg M]
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨fun c _ => funext fun i => (IsEmpty.false i).elim, fun c _ _ i => (IsEmpty.false i).elim⟩
  have bound : ∀ c : κ → ℝ, ∃ j, ∀ σ,
      |∑ i, W σ i * c i - c σ| ≤ n * ε * |c j| ∧ |c σ| ≤ |c j| := by
    intro c
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|) Finset.univ_nonempty
    exact ⟨j, fun σ => ⟨perturb_bound W ε |c j| hW c (fun i => hj i (Finset.mem_univ i)) σ,
      hj σ (Finset.mem_univ σ)⟩⟩
  constructor
  · intro c hc
    obtain ⟨j, hj⟩ := bound c
    have h1 := (hj j).1
    rw [hc j, zero_sub, abs_neg] at h1
    have hC : |c j| = 0 := by nlinarith [abs_nonneg (c j)]
    funext i
    have h2 := (hj i).2
    rw [hC] at h2
    exact abs_nonpos_iff.mp h2
  · intro c hpos hratio i
    obtain ⟨j, hj⟩ := bound c
    have hC0 : 0 ≤ |c j| := abs_nonneg _
    have h1 : |c j| ≤ ∑ k, W j k * c k + n * ε * |c j| := by
      have e := abs_sub_abs_le_abs_sub (c j) (∑ k, W j k * c k)
      rw [abs_sub_comm (c j), abs_of_pos (hpos j)] at e
      linarith [(hj j).1]
    have h2 : ∑ k, W i k * c k - n * ε * |c j| ≤ c i := by
      linarith [(abs_le.mp (hj i).1).2]
    have h3 := hratio j i
    have hyi := hpos i
    have hMy : M * ∑ k, W i k * c k ≤ |M| * ∑ k, W i k * c k :=
      mul_le_mul_of_nonneg_right (le_abs_self M) hyi.le
    have s1 : n * ε * |c j| * (2 * (|M| + 1)) ≤ |c j| := by
      nlinarith [mul_le_mul_of_nonneg_right hδ hC0]
    have s2 : |c j| * (1 - n * ε) ≤ |M| * ∑ k, W i k * c k := by nlinarith
    have s3 : n * ε * |c j| * (|M| + 1) < (∑ k, W i k * c k) * (|M| + 1) := by
      nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ 1 - 2 * (n * ε))]
    have s4 : n * ε * |c j| < ∑ k, W i k * c k := lt_of_mul_lt_mul_right s3 hM1.le
    linarith

end GlobalTheory.CompanionTheory.DiagDom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TraceIdempotentNotDivisible
section
namespace GlobalTheory.CompanionTheory.IdemTrace

theorem exists_nat_trace_of_idem {O : Type} [CommRing O] [IsLocalRing O] {g : ℕ}
    (P : Matrix (Fin g) (Fin g) O) (h : P * P = P) :
    ∃ r : ℕ, r ≤ g ∧ Matrix.trace P = (r : O) ∧ (r = 0 → P = 0) := by
  classical
  set f : (Fin g → O) →ₗ[O] (Fin g → O) := Matrix.toLin' P with hf
  have hidem : IsIdempotentElem f := by
    unfold IsIdempotentElem
    rw [hf, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have hff : ∀ z, f (f z) = f z := fun z => by
    rw [← Module.End.mul_apply, hidem.eq]
  have hproj := (LinearMap.isProj_range_iff_isIdempotentElem f).mpr hidem
  have hPr : Module.Projective O (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype f.rangeRestrict
      (LinearMap.ext fun y => Subtype.ext (by
        obtain ⟨z, hz⟩ := y.2
        simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.id_apply]
        rw [← hz]
        exact hff z))
  let sK : (Fin g → O) →ₗ[O] LinearMap.ker f :=
    (LinearMap.id - f).codRestrict (LinearMap.ker f) (fun y => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hff, sub_self])
  have hsK : sK.comp (LinearMap.ker f).subtype = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (by
      have hy : f y = 0 := y.2
      simp [sK, hy])
  have hPk : Module.Projective O (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype sK hsK
  have hFk : Module.Finite O (LinearMap.ker f) :=
    Module.Finite.of_surjective sK (fun y => ⟨y, by
      exact LinearMap.congr_fun hsK y⟩)
  have : Module.Free O (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  have : Module.Free O (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  have htr := hproj.trace
  refine ⟨Module.finrank O (LinearMap.range f), ?_, ?_, ?_⟩
  · calc Module.finrank O (LinearMap.range f) ≤ Module.finrank O (Fin g → O) :=
          Submodule.finrank_le _
      _ = g := Module.finrank_fin_fun O
  · rw [← Matrix.trace_toLin'_eq, ← hf, htr]
  · intro h0
    have hs : Subsingleton (LinearMap.range f) := (Module.finrank_eq_zero_iff_of_free O _).mp h0
    have hbot : LinearMap.range f = ⊥ := Submodule.subsingleton_iff_eq_bot.mp hs
    rw [LinearMap.range_eq_bot, hf] at hbot
    exact Matrix.toLin'.injective (by rw [hbot, map_zero])

private lemma isLocalRing_zmod_prime_pow (p m : ℕ) [hp : Fact p.Prime] (hm : 0 < m) :
    IsLocalRing (ZMod (p ^ m)) := by
  have : Fact (1 < p ^ m) := ⟨Nat.one_lt_pow hm.ne' hp.out.one_lt⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra hcon0
  have hcon := not_or.mp hcon0
  let φ := ZMod.castHom (dvd_pow_self p hm.ne') (ZMod p)
  have key : ∀ b : ZMod (p ^ m), ¬ IsUnit b → φ b = 0 := by
    intro b hb
    rw [← ZMod.natCast_zmod_val b] at hb ⊢
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hm, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd hp.out, not_not] at hb
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact hb
  have h1 := congrArg φ (add_sub_cancel a 1)
  rw [map_add, key a hcon.1, key _ hcon.2, add_zero, map_one] at h1
  exact zero_ne_one h1

theorem not_dvd_trace : ∀ (B : Type) [CommRing B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B)
    (p m : ℕ), p.Prime → Module.finrank ℤ B < p ^ m →
    x * x - x ∈ Ideal.span {((p : B)) ^ m} → x ∉ Ideal.span {((p : B)) ^ m} →
    ¬ ((p : ℤ) ^ m ∣ Algebra.trace ℤ B x) := by
  intro B _ _ _ x p m hp hrank hidem hnot hdvd
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · apply hnot
    simp
  have : Fact p.Prime := ⟨hp⟩
  have := isLocalRing_zmod_prime_pow p m hm
  classical
  let b := Module.finBasis ℤ B
  let M := Algebra.leftMulMatrix b x
  let φ := Int.castRingHom (ZMod (p ^ m))
  let P := φ.mapMatrix M
  have hpm : (((p : ℤ) ^ m : ℤ) : ZMod (p ^ m)) = 0 := by
    push_cast
    exact_mod_cast ZMod.natCast_self (p ^ m)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hidem
  have hz : y * (p : B) ^ m = ((p : ℤ) ^ m) • y := by
    rw [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast, mul_comm]
  have hP : P * P = P := by
    have hMM : M * M - M = ((p : ℤ) ^ m) • Algebra.leftMulMatrix b y := by
      rw [← map_zsmul, ← hz, hy, map_sub, map_mul]
    rw [← sub_eq_zero]
    show φ.mapMatrix M * φ.mapMatrix M - φ.mapMatrix M = 0
    rw [← map_mul, ← map_sub, hMM, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (p ^ m)), hpm,
      zero_smul]
  obtain ⟨r, hr, htr, hr0⟩ := exists_nat_trace_of_idem P hP
  have htrace : ((Algebra.trace ℤ B x : ℤ) : ZMod (p ^ m)) = P.trace := by
    rw [Algebra.trace_eq_matrix_trace b x]
    simp [P, M, φ, Matrix.trace, Matrix.diag]
  obtain ⟨k, hk⟩ := hdvd
  have hr_zero : (r : ZMod (p ^ m)) = 0 := by
    rw [← htr, ← htrace, hk, Int.cast_mul, hpm, zero_mul]
  rw [ZMod.natCast_eq_zero_iff] at hr_zero
  have hr' : r = 0 := Nat.eq_zero_of_dvd_of_lt hr_zero (by omega)
  have hP0 := hr0 hr'
  have hent : ∀ i j, ((p : ℤ) ^ m) ∣ M i j := by
    intro i j
    have h1 : φ (M i j) = 0 := by
      have := congrFun (congrFun hP0 i) j
      simpa [P] using this
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (M i j) (p ^ m)).mp h1
    exact_mod_cast h2
  apply hnot
  have hxb : ∀ j, x * b j ∈ Ideal.span {((p : B)) ^ m} := by
    intro j
    rw [← b.sum_repr (x * b j)]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    have hM : b.repr (x * b j) i = M i j := (Algebra.leftMulMatrix_eq_repr_mul b x i j).symm
    obtain ⟨c, hc⟩ := hent i j
    rw [hM, hc, Ideal.mem_span_singleton]
    refine ⟨c • b i, ?_⟩
    rw [mul_smul, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
  rw [← mul_one x, ← b.sum_repr 1, Finset.mul_sum]
  refine Ideal.sum_mem _ (fun j _ => ?_)
  rw [mul_smul_comm]
  exact Submodule.smul_of_tower_mem _ _ (hxb j)

end GlobalTheory.CompanionTheory.IdemTrace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentative
section
namespace GlobalTheory.CompanionTheory.SiegelKlingen

theorem exists_unique_minimal_translate :
    ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) →
    Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  intro G M _ _ φ f hpos hinj D hfin x ⟨g0, hg0⟩
  have key : ∀ a b : G, φ (a * b⁻¹) * (φ b * x) = φ a * x := by
    intro a b
    rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
  have hS : {g : G | φ g * x ∈ D}.Finite := by
    refine (hfin.image (fun h => h * g0)).subset ?_
    intro g hg
    exact ⟨g * g0⁻¹, ⟨φ g0 * x, hg0, by rw [key]; exact hg⟩, inv_mul_cancel_right g g0⟩
  obtain ⟨g, hgS, hmin⟩ := Set.exists_min_image _ f hS ⟨g0, hg0⟩
  refine ⟨g, ⟨hgS, fun g' hg' hD => ?_⟩, ?_⟩
  · have hmem : φ (g' * g) * x ∈ D := by rwa [map_mul, mul_assoc]
    have h1 := hmin _ hmem
    rw [map_mul] at h1
    have hp := hpos g
    nlinarith
  · rintro g2 ⟨hg2, hmin2⟩
    have h1 : 1 ≤ f (g * g2⁻¹) := not_lt.1 fun hlt => hmin2 _ hlt (by rw [key]; exact hgS)
    rw [map_mul, map_inv] at h1
    have hp2 := hpos g2
    have h3 := mul_le_mul_of_nonneg_right h1 hp2.le
    rw [one_mul, inv_mul_cancel_right₀ hp2.ne'] at h3
    exact hinj (le_antisymm h3 (hmin g2 hg2))

end GlobalTheory.CompanionTheory.SiegelKlingen
end

