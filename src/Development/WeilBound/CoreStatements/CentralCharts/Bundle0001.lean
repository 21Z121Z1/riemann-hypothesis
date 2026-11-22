import Development.WeilBound.CoreStatements.CentralCharts.TraceMulReNonneg
import Development.WeilBound.CoreStatements.CentralCharts.ContDiffAtLogNorm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0052
import Development.WeilBound.CoreStatements.CentralCharts.ExistsPermFirst

-- bundled from Development.WeilBound.CoreStatements.CentralCharts.AnalyticAtDet
section
noncomputable section

namespace AnalyticReference.An.H

open ReciprocityTheory.AnForm Filter Topology Matrix
open scoped ComplexOrder MatrixOrder

variable {n k r : ℕ}

theorem posDef_ofReal {Y : Matrix (Fin k) (Fin k) ℝ} (hY : Y.PosDef) : (Y.map Complex.ofReal).PosDef := by
  have h0 : 0 ≤ Y := hY.posSemidef.nonneg
  have h1 : (CFC.sqrt Y).PosSemidef := (CFC.sqrt_nonneg Y).posSemidef
  have h2 : Y = (CFC.sqrt Y)ᴴ * CFC.sqrt Y := by rw [h1.1.eq, CFC.sqrt_mul_sqrt_self Y h0]
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin k) (Fin k) ℝ, Y = Sᴴ * S := ⟨_, h2⟩
  have h3 : Y.map Complex.ofReal = (S.map Complex.ofReal)ᴴ * S.map Complex.ofReal := by
    rw [hS]
    ext i j
    simp [mul_apply]
  have h4 : (Y.map Complex.ofReal).PosSemidef := by rw [h3]; exact posSemidef_conjTranspose_mul_self _
  refine h4.posDef_iff_det_ne_zero.2 ?_
  have h5 := Complex.ofRealHom.map_det Y
  rw [RingHom.mapMatrix_apply] at h5
  have h6 : (Y.map Complex.ofReal).det = (Y.det : ℂ) := h5.symm
  rw [h6]
  exact_mod_cast hY.det_pos.ne'

theorem inv_map_ofReal {Y : Matrix (Fin k) (Fin k) ℝ} (hY : Y.PosDef) :
    Y⁻¹.map Complex.ofReal = (Y.map Complex.ofReal)⁻¹ := by
  symm
  refine inv_eq_left_inv ?_
  have h := Matrix.map_mul (L := Y⁻¹) (M := Y) (f := Complex.ofRealHom)
  rw [nonsing_inv_mul _ (IsUnit.mk0 _ hY.det_pos.ne'), Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h.symm

theorem analyticAt_det {m : ℕ} {A : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ} {t : Fin n → ℂ}
    (h : ∀ p q, AnalyticAt ℂ (fun u => A u p q) t) : AnalyticAt ℂ (fun u => (A u).det) t := by
  simp only [det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_inv {A : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ} {t : Fin n → ℂ}
    (h : ∀ p q, AnalyticAt ℂ (fun u => A u p q) t) (h0 : (A t).det ≠ 0) (p q : Fin k) :
    AnalyticAt ℂ (fun u => (A u)⁻¹ p q) t := by
  simp only [inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, adjugate_apply]
  refine ((analyticAt_det h).inv h0).mul (analyticAt_det fun i j => ?_)
  simp only [updateRow_apply]
  split_ifs
  · exact analyticAt_const
  · exact h _ _

theorem psh_core {τ : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ} {V : (Fin n → ℂ) → Matrix (Fin r) (Fin k) ℂ}
    {f : (Fin n → ℂ) → ℝ} (d : ℝ) (hτ : ∀ p q, AnalyticAt ℂ (fun u => τ u p q) 0)
    (hV : ∀ p q, AnalyticAt ℂ (fun u => V u p q) 0) (hV0 : Function.Injective (V 0).vecMul)
    (hpos : ∀ᶠ u in 𝓝 0, ((τ u).map Complex.im).PosDef) (hf : ContDiffAt ℝ 2 f 0)
    (he : ∀ᶠ u in 𝓝 0, (V u * (((τ u).map Complex.im).map Complex.ofReal)⁻¹ * (V u)ᴴ).PosDef →
      f u = d + Real.log (V u * (((τ u).map Complex.im).map Complex.ofReal)⁻¹ * (V u)ᴴ).det.re) : PshAt0 f := by
  obtain ⟨Y, hY⟩ : ∃ Y : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ,
      ∀ u, Y u = ((τ u).map Complex.im).map Complex.ofReal := ⟨_, fun _ => rfl⟩
  simp only [← hY] at he
  have hYp : ∀ᶠ u in 𝓝 0, (Y u).PosDef := hpos.mono fun u hu => by rw [hY]; exact posDef_ofReal hu
  have hY0 := hYp.self_of_nhds
  have huY : IsUnit (Y 0).det := IsUnit.mk0 _ hY0.det_pos.ne'
  obtain ⟨C, hC⟩ : ∃ C, C = (Y 0)⁻¹ * (V 0)ᴴ := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = V 0 * (Y 0)⁻¹ * (V 0)ᴴ := ⟨_, rfl⟩
  have hGp : G.PosDef := by rw [hG]; exact hY0.inv.mul_mul_conjTranspose_same hV0
  have huG : IsUnit G.det := IsUnit.mk0 _ hGp.det_pos.ne'
  have hVC : V 0 * C = G := by rw [hC, hG, Matrix.mul_assoc]
  have hM0 : Cᴴ * Y 0 * C = G := by
    rw [hC, hG, conjTranspose_mul, conjTranspose_conjTranspose, hY0.inv.1.eq]
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ huY]
  have hCi : Function.Injective C.mulVec := by
    have h1 : Function.Injective G.mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 huG)
    intro x y hxy
    apply h1
    rw [← hVC, ← mulVec_mulVec, ← mulVec_mulVec, hxy]
  have hF : AnalyticAt ℂ (fun u => (V u * C).det) 0 := analyticAt_det fun p q => by
    simp only [mul_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hV _ _).mul analyticAt_const
  have hF0 : (V 0 * C).det ≠ 0 := by rw [hVC]; exact huG.ne_zero
  obtain ⟨Km, hK⟩ : ∃ Km, Km = C * G⁻¹ * Cᴴ := ⟨_, rfl⟩
  have hT : AnalyticAt ℂ (fun u => ∑ p, ∑ q, ((Km p q).re : ℂ) * (Complex.I * τ u q p)) 0 :=
    Finset.analyticAt_fun_sum _ fun p _ => Finset.analyticAt_fun_sum _ fun q _ =>
      analyticAt_const.mul (analyticAt_const.mul (hτ _ _))
  have htr : ∀ u, (∑ p, ∑ q, ((Km p q).re : ℂ) * (Complex.I * τ u q p)).re = -(G⁻¹ * (Cᴴ * Y u * C)).trace.re := by
    intro u
    have e : (G⁻¹ * (Cᴴ * Y u * C)).trace = (Km * Y u).trace := by
      rw [hK, ← Matrix.mul_assoc, trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e, hY]
    simp [trace, mul_apply, Complex.re_sum]
  have hg := padd (plog_norm 2 (d - Real.log G.det.re + r) hF hF0) (pre hT)
  refine ptouch hf hg ?_ ?_
  · rw [he.self_of_nhds (hG ▸ hGp), htr, hM0, hVC, ← hG, nonsing_inv_mul _ huG, trace_one]
    have : ‖G.det‖ = G.det.re := by
      rw [det_eq_re hGp, Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg (det_re_pos hGp).le]
    rw [this]
    simp
    ring
  · filter_upwards [he, hYp, hF.continuousAt.eventually_ne hF0] with u h1 h2 h3
    have hN : Cᴴ * (V u)ᴴ = (V u * C)ᴴ := (conjTranspose_mul _ _).symm
    have hVi : Function.Injective (V u).vecMul := by
      have h4 : Function.Injective (V u * C).vecMul :=
        Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ h3))
      intro x y hxy
      apply h4
      have hxy' : x ᵥ* V u = y ᵥ* V u := hxy
      show x ᵥ* (V u * C) = y ᵥ* (V u * C)
      rw [← vecMul_vecMul, ← vecMul_vecMul, hxy']
    have hGu := h2.inv.mul_mul_conjTranspose_same hVi
    have hM := h2.conjTranspose_mul_mul_same hCi
    have a1 := logdet_dual_ge h2 (V u)ᴴ C hM (by rwa [conjTranspose_conjTranspose])
      (by rw [hN, det_conjTranspose]; exact star_ne_zero.2 h3)
    rw [hN, det_conjTranspose, norm_star, conjTranspose_conjTranspose] at a1
    have a2 := logdet_le hM hGp
    rw [h1 hGu, htr]
    linarith

end AnalyticReference.An.H
end
end

-- bundled from Development.WeilBound.CoreStatements.CentralCharts.ContDiffAtLogdet
section
noncomputable section

namespace AnalyticReference.An.H

open ReciprocityTheory.AnForm GlobalTheory.CompanionTheory.Ar Filter Topology Matrix
open scoped ComplexOrder

theorem contDiffAt_logdet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ} {m : WithTop ℕ∞}
    {Γ : E → Matrix (Fin r) (Fin r) ℂ} {t : E} (h : ∀ p q, ContDiffAt ℝ m (fun u => Γ u p q) t) (hp : (Γ t).PosDef) :
    ContDiffAt ℝ m (fun u => Real.log (Γ u).det.re) t := by
  classical
  have hdet : ContDiffAt ℝ m (fun u => (Γ u).det) t := by
    simp only [Matrix.det_apply]
    refine ContDiffAt.sum fun σ _ => ?_
    refine ContDiffAt.const_smul _ ?_
    exact contDiffAt_prod fun i _ => h (σ i) i
  have hre : ContDiffAt ℝ m (fun u => (Γ u).det.re) t :=
    Complex.reCLM.contDiff.contDiffAt.comp t hdet
  refine hre.log ?_
  have hpos := hp.det_pos
  have h0 : 0 < (Γ t).det.re := (Complex.pos_iff.mp hpos).1
  exact h0.ne'

variable {n a : ℕ}

theorem tame_logdet {a₀ k r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ k Λ)
    (U : Fin r → (Fin n → ℂ) → Fin k → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hU : ∀ j, DifferentiableOn ℂ (U j) (Metric.ball 0 1)) (hli : LinearIndependent ℂ fun j => U j 0)
    (ha : ∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a) :
    Tame a fun t => Real.log (HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π t)).det.re := by
  classical
  obtain ⟨ε, c, C, hε, hερ, hc, hC, hB⟩ := GlobalTheory.T.period_gram_comparison_bound n a₀ k r a Λ L U 0 π ρ hρ hρ1 hU hli
    (fun i hi => ⟨ha i hi, rfl⟩)
  set G : (Fin n → ℂ) → Matrix (Fin r) (Fin r) ℂ :=
    fun y => HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π y) with hGdef
  have hpunct : ∀ y : Fin n → ℂ, ‖y‖ < ε → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      HodgeMetric.uncentre 0 ρ π y ∈ Flat.punct n a₀ 1 := by
    intro y hy hy0
    refine ⟨HodgeMetric.uncentre_mem_ball hρ π (by simpa using hy.trans_le hερ), ?_⟩
    intro i hi
    simp only [HodgeMetric.uncentre, Pi.zero_apply, sub_zero]
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hρ.ne')) (hy0 _ (ha i hi))
  have hB' : ∀ y : Fin n → ℂ, ‖y‖ < ε → ‖y‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      ((G y)⁻¹ - (c : ℂ) • 1).PosSemidef ∧ (((C * logR a y : ℝ) : ℂ) • 1 - (G y)⁻¹).PosSemidef ∧
      ∀ p q, ‖fderiv ℝ (fun y' => G y' p q) y‖ ≤ C * Real.exp (logR a y / 2) := by
    intro y hy hy1 hy0
    exact hB y (by simpa using hy) hy1 (hpunct y hy hy0)
  have hPD : ∀ y : Fin n → ℂ, ‖y‖ < ε → ‖y‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      (G y).PosDef := fun y hy hy1 hy0 => posDef_of_inv_ge hc (hB' y hy hy1 hy0).1
  have hentry : ∀ y : Fin n → ℂ, ‖y‖ < ε → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞) (fun u => G u p q) y := by
    intro y hy hy0 p q
    exact (GlobalTheory.T.period_gram_smooth_punctured n a₀ k r Λ L U hU p q _ (hpunct y hy hy0)).comp y
      (HodgeMetric.contDiff_uncentre 0 ρ π).contDiffAt
  have hgood : ∀ y : Fin n → ℂ, ‖y‖ < ε → ‖y‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      ∀ᶠ z in 𝓝 y, ‖z‖ < ε ∧ ‖z‖ < 1 ∧ ∀ i : Fin n, (i : ℕ) < a → z i ≠ 0 := by
    intro y hy hy1 hy0
    refine (continuous_norm.continuousAt.eventually_lt continuousAt_const hy).and
      ((continuous_norm.continuousAt.eventually_lt continuousAt_const hy1).and ?_)
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : (i : ℕ) < a
    · have hc' : ContinuousAt (fun z : Fin n → ℂ => z i) y := (continuous_apply i).continuousAt
      filter_upwards [hc'.eventually_ne (hy0 i hi)] with z hz _ using hz
    · exact Filter.Eventually.of_forall fun z h => absurd h hi
  refine tame_of (C₁ := r * (|Real.log c| + |Real.log C| + 1))
    (C₂ := 3 * r ^ 4 * (max 1 c⁻¹) ^ 2 * max (max 1 c⁻¹) C * C) (e := 1) hε (by positivity)
    (by positivity) zero_le_one ?_
  intro y hy hy1 hy0
  have hB1 := hB' y hy hy1 hy0
  have hpd := hPD y hy hy1 hy0
  have hR1 : 1 ≤ logR a y := one_le_logR hy1 hy0
  have hLL : 1 ≤ Real.log (logR a y) := one_le_log_logR hy1 hy0
  have hK : 0 < C * logR a y := mul_pos hC (by linarith)
  refine ⟨contDiffAt_logdet (Γ := G) (hentry y hy hy0) hpd, ?_, ?_⟩
  · have hlo := logdet_mono (posDef_smul_one (r := r) hc) hpd.inv hB1.1
    have hhi := logdet_mono hpd.inv (posDef_smul_one (r := r) hK) hB1.2.1
    rw [logdet_smul_one hc, logdet_inv hpd] at hlo
    rw [logdet_smul_one hK, logdet_inv hpd, Real.log_mul hC.ne' (by linarith)] at hhi
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have h1 : -|Real.log c| ≤ Real.log c := neg_abs_le _
    have h2 : Real.log C ≤ |Real.log C| := le_abs_self _
    have h3 : -((r : ℝ) * |Real.log c|) ≤ r * Real.log c := by
      have := mul_le_mul_of_nonneg_left h1 hr
      rwa [mul_neg] at this
    have p1 : 0 ≤ (r : ℝ) * |Real.log C| := mul_nonneg hr (abs_nonneg _)
    have p2 : 0 ≤ (r : ℝ) * |Real.log c| := mul_nonneg hr (abs_nonneg _)
    have p3 : (r : ℝ) * (|Real.log c| + |Real.log C|) ≤
        r * (|Real.log c| + |Real.log C|) * Real.log (logR a y) := by
      have : 0 ≤ (r : ℝ) * (|Real.log c| + |Real.log C|) := by positivity
      nlinarith
    have h4 : (r : ℝ) * Real.log C ≤ r * |Real.log C| := mul_le_mul_of_nonneg_left h2 hr
    have h5 : (r : ℝ) * (|Real.log c| + |Real.log C| + 1) ≤
        r * (|Real.log c| + |Real.log C| + 1) * Real.log (logR a y) := by
      have : 0 ≤ (r : ℝ) * (|Real.log c| + |Real.log C| + 1) := by positivity
      nlinarith
    have h6 : (r : ℝ) * Real.log (logR a y) ≤ r * (|Real.log c| + |Real.log C| + 1) * Real.log (logR a y) := by
      have : 0 ≤ Real.log (logR a y) := by linarith
      have : (0 : ℝ) ≤ |Real.log c| + |Real.log C| := by positivity
      nlinarith
    rw [abs_le]
    constructor <;> linarith
  · set P : ℝ := max 1 c⁻¹ with hP
    set Q : ℝ := max P C * Real.exp (logR a y / 2) with hQ
    have hP1 : 1 ≤ P := le_max_left _ _
    have hE : 1 ≤ Real.exp (logR a y / 2) := Real.one_le_exp (by linarith)
    have hPQ : P ≤ Q := by
      have : P ≤ max P C := le_max_left _ _
      have : 0 ≤ max P C := by linarith
      nlinarith
    have hd := GlobalTheory.T.gram_matrix_sub_scalar_posSemidef r r (Fin n → ℂ) G (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) y
      (C * logR a y)⁻¹ P Q (inv_pos.2 hK) (by linarith) hPQ
      (fun p q => ((hentry y hy hy0 p q).differentiableAt (by simp)))
      (fun p q => differentiableAt_const _)
      (by
        filter_upwards [hgood y hy hy1 hy0] with z hz
        refine ⟨hPD z hz.1 hz.2.1 hz.2.2, ?_⟩
        have h1 : (1 : Matrix (Fin r) (Fin r) ℂ) = ⇑(Pi.basisFun ℂ (Fin r)) := by
          ext i j
          simp [Matrix.one_apply, Pi.single_apply, eq_comm]
        rw [Matrix.transpose_one, h1]
        exact (Pi.basisFun ℂ (Fin r)).linearIndependent)
      (by
        rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
        exact ge_of_inv_le hK hpd hB1.2.1)
      (fun p q => ⟨(norm_entry_le hpd.posSemidef (le_of_inv_ge hc hpd hB1.1) p q).trans (le_max_right _ _),
        (hB1.2.2 p q).trans (by
          have : C ≤ max P C := le_max_right _ _
          have : 0 ≤ Real.exp (logR a y / 2) := by positivity
          nlinarith)⟩)
      (fun p q => ⟨by
          rw [Matrix.one_apply]
          split_ifs <;> simp <;> linarith,
        by simp [fderiv_const_apply]; linarith⟩)
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hd
    refine hd.trans (le_of_eq ?_)
    rw [Real.rpow_one, hQ, div_inv_eq_mul]
    ring

end AnalyticReference.An.H
end
end

-- bundled from Development.WeilBound.CoreStatements.CentralCharts.SmoothOnOfTame
section
noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric

variable {n : ℕ} {X : Type} [TopologicalSpace X]

theorem exp_le_logR (a : ℕ) {t : Fin n → ℂ} (ht : ‖t‖ < 1) : Real.exp 1 ≤ logR a t := by
  unfold logR
  have hs : 0 ≤ ∑ i : Fin n, (if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) := by
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · have h1 := norm_le_pi_norm t i
      have h2 : ‖t i‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (t i)]
      rw [one_div, Real.log_inv, neg_nonneg]
      exact Real.log_nonpos (by positivity) h2
    · exact le_rfl
  linarith

theorem one_le_of_exp_le {r : ℝ} (h : Real.exp 1 ≤ r) : 1 ≤ r ∧ 1 ≤ Real.log r := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hr : 0 < r := by linarith
  exact ⟨le_trans he h, (Real.le_log_iff_exp_le hr).mpr h⟩

theorem tame_smooth (a : ℕ) {g : (Fin n → ℂ) → ℝ}
    (hg : ∀ t ∈ ball (0 : Fin n → ℂ) 1, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g t) : Tame a g := by
  have hon : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 1) := fun t ht => (hg t ht).contDiffWithinAt
  have hK : IsCompact (closedBall (0 : Fin n → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hsub : closedBall (0 : Fin n → ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn (hon.continuousOn.mono hsub)
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn
    ((hon.continuousOn_fderiv_of_isOpen isOpen_ball (by exact_mod_cast le_top)).mono hsub)
  refine ⟨1 / 2, max (max B1 B2) 0, by norm_num, by norm_num, le_max_right _ _, fun t ht _ => ?_⟩
  have htK : t ∈ closedBall (0 : Fin n → ℂ) (1 / 2) := by
    rw [mem_closedBall, dist_zero_right]
    exact ht.le
  have hR := exp_le_logR a (t := t) (by linarith)
  obtain ⟨hR1, hL1⟩ := one_le_of_exp_le hR
  have hC : 0 ≤ max (max B1 B2) 0 := le_max_right _ _
  refine ⟨hg t (hsub htK), ?_, ?_⟩
  · have h1 := hB1 t htK
    rw [Real.norm_eq_abs] at h1
    calc |g t| ≤ max (max B1 B2) 0 := le_trans h1 (le_trans (le_max_left _ _) (le_max_left _ _))
      _ = max (max B1 B2) 0 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL1 hC
  · have h1 := hB2 t htK
    have h2 : 1 ≤ logR a t ^ max (max B1 B2) 0 := Real.one_le_rpow hR1 hC
    have h3 : 1 ≤ Real.exp (logR a t / 2) := Real.one_le_exp (by linarith)
    calc ‖fderiv ℝ g t‖ ≤ max (max B1 B2) 0 :=
          le_trans h1 (le_trans (le_max_right _ _) (le_max_left _ _))
      _ = max (max B1 B2) 0 * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 zero_le_one (by positivity)

theorem exp_le_rW {L : LocPot X} {s : X → X → ℂ} (hn : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    Real.exp 1 ≤ rW L s y := by
  have := hn y
  unfold rW
  linarith

variable {A : FinHolAtlas n X} {L : LocPot X} {s : X → X → ℂ} {U : X → Set X} {ph : X → ℝ}

theorem NChart.symm_zero {V : Set X} {x₀ : X} {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} {a : ℕ} {M : ℝ}
    (h : NChart A V L s x₀ ψ a M) : ψ.symm 0 = x₀ := by
  rw [← h.2.2.1]
  exact ψ.left_inv h.2.1

theorem NChart.zero_of_not_mem {V : Set X} {x₀ : X} {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} {a : ℕ} {M : ℝ}
    (h : NChart A V L s x₀ ψ a M) (hx : x₀ ∉ bdry s) : a = 0 := by
  by_contra ha
  have h0 := (h.2.2.2.2 0 (mem_ball_self one_pos)).2.2.1
  rw [NChart.symm_zero h] at h0
  have hpos : 0 < a := Nat.pos_of_ne_zero ha
  exact hx (h0.mpr ⟨⟨0, lt_of_lt_of_le hpos h.2.2.2.1⟩, hpos, rfl⟩)

theorem smoothOn_of_tame (hT : ∀ x, ∃ ψ a M, NChart A (U x) L s x ψ a M ∧ Tame a fun t => ph (ψ.symm t)) :
    A.SmoothOn (bdry s)ᶜ ph := by
  intro j y hy
  obtain ⟨hyt, hyb⟩ := hy
  obtain ⟨ψ, a, M, hN, hTm⟩ := hT ((A.chart j).symm y)
  have ha : a = 0 := hN.zero_of_not_mem hyb
  subst ha
  obtain ⟨ε, C, hε, -, -, hTt⟩ := hTm
  have hxs : (A.chart j).symm y ∈ ψ.source := hN.2.1
  have hs0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ph (ψ.symm t)) (ψ ((A.chart j).symm y)) := by
    rw [hN.2.2.1]
    exact (hTt 0 (by simpa using hε) (fun i hi => absurd hi (Nat.not_lt_zero _))).1
  have hcomp : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hN.1 j).1 y ⟨hyt, hxs⟩
  have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ ∘ (A.chart j).symm) y :=
    (hcomp.contDiffAt).restrict_scalars ℝ
  have heq : (fun t => ph (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm) =ᶠ[𝓝 y] ph ∘ (A.chart j).symm := by
    have hopen : (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm ψ.open_source).mem_nhds ⟨hyt, hxs⟩
    filter_upwards [hopen] with w hw
    simp [Function.comp, ψ.left_inv hw.2]
  exact ((hs0.comp y hsm).congr_of_eventuallyEq heq.symm).contDiffWithinAt

theorem local_of_tame (hn : ∀ y, logNormSec L s y ≤ 0) {V : Set X} {x : X}
    {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} {a : ℕ} {M : ℝ} (h : NChart A V L s x ψ a M)
    (hT : Tame a fun t => ph (ψ.symm t)) :
    ∃ (V' : Set X) (c : ℝ), IsOpen V' ∧ x ∈ V' ∧ V' ⊆ ψ.source ∧ ∀ x' ∈ V', x' ∉ bdry s →
      |ph x'| ≤ c * Real.log (rW L s x') ∧
      ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2) := by
  obtain ⟨ε, C, hε, hε1, hC, hTt⟩ := hT
  set K : ℝ := 1 + max M 0 with hK
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hMM : M ≤ max M 0 := le_max_left _ _
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  set c1 := C * (1 + Real.log K) with hc1d
  set c2 := C * K ^ C * Real.exp (K / 2) with hc2d
  have hKC : 1 ≤ K ^ C := Real.one_le_rpow hK1 hC
  have heK : 1 ≤ Real.exp (K / 2) := Real.one_le_exp (by linarith)
  have hCc2 : C ≤ c2 := by
    have h1 : 1 ≤ K ^ C * Real.exp (K / 2) := by nlinarith
    calc C = C * 1 := by ring
      _ ≤ C * (K ^ C * Real.exp (K / 2)) := mul_le_mul_of_nonneg_left h1 hC
      _ = c2 := by rw [hc2d]; ring
  have hc1 : c1 ≤ max c1 c2 := le_max_left _ _
  have hc2 : c2 ≤ max c1 c2 := le_max_right _ _
  refine ⟨ψ.source ∩ ψ ⁻¹' ball 0 ε, max c1 c2, ψ.isOpen_inter_preimage isOpen_ball,
    ⟨h.2.1, by simp [h.2.2.1, hε]⟩, Set.inter_subset_left, ?_⟩
  rintro x' ⟨hxs, hxb⟩ hxbd
  have htb : ‖ψ x'‖ < ε := by simpa using hxb
  have ht1 : ψ x' ∈ ball (0 : Fin n → ℂ) 1 := by
    rw [mem_ball_zero_iff]
    linarith
  have hsy : ψ.symm (ψ x') = x' := ψ.left_inv hxs
  have hN := h.2.2.2.2 (ψ x') ht1
  rw [hsy] at hN
  have hnz : ∀ i : Fin n, (i : ℕ) < a → ψ x' i ≠ 0 := fun i hi h0 => hxbd (hN.2.2.1.mpr ⟨i, hi, h0⟩)
  have hRb : logR a (ψ x') ≤ rW L s x' + M := hN.2.2.2 hxbd
  obtain ⟨-, hbd1, hbd2⟩ := hTt (ψ x') htb hnz
  have hrW := exp_le_rW hn x'
  obtain ⟨hrW1, hlrW⟩ := one_le_of_exp_le hrW
  obtain ⟨hR1, hlR⟩ := one_le_of_exp_le (exp_le_logR a (t := ψ x') (by linarith))
  have hRK : logR a (ψ x') ≤ rW L s x' * K := by
    rw [hK]
    nlinarith
  have hlog : Real.log (logR a (ψ x')) ≤ (1 + Real.log K) * Real.log (rW L s x') := by
    have h1 : Real.log (logR a (ψ x')) ≤ Real.log (rW L s x' * K) := Real.log_le_log (by linarith) hRK
    rw [Real.log_mul (by linarith) (by linarith)] at h1
    nlinarith
  refine ⟨?_, ?_⟩
  · have hb1 : |ph x'| ≤ C * Real.log (logR a (ψ x')) := by simpa [hsy] using hbd1
    calc |ph x'| ≤ C * Real.log (logR a (ψ x')) := hb1
      _ ≤ C * ((1 + Real.log K) * Real.log (rW L s x')) := mul_le_mul_of_nonneg_left hlog hC
      _ = c1 * Real.log (rW L s x') := by rw [hc1d]; ring
      _ ≤ max c1 c2 * Real.log (rW L s x') := mul_le_mul_of_nonneg_right hc1 (by linarith)
  · have hp1 : logR a (ψ x') ^ C ≤ rW L s x' ^ C * K ^ C := by
      rw [← Real.mul_rpow (by linarith) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) hRK hC
    have hp2 : Real.exp (logR a (ψ x') / 2) ≤ Real.exp (rW L s x' / 2) * Real.exp (K / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hK]
      linarith
    have hp3 : rW L s x' ^ C ≤ rW L s x' ^ max c1 c2 :=
      Real.rpow_le_rpow_of_exponent_le hrW1 (le_trans hCc2 hc2)
    have hfd : ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ C * logR a (ψ x') ^ C * Real.exp (logR a (ψ x') / 2) :=
      hbd2
    have hE0 : 0 ≤ Real.exp (rW L s x' / 2) := (Real.exp_pos _).le
    have hrC : 0 ≤ rW L s x' ^ C := by positivity
    calc ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ C * logR a (ψ x') ^ C * Real.exp (logR a (ψ x') / 2) := hfd
      _ ≤ C * (rW L s x' ^ C * K ^ C) * (Real.exp (rW L s x' / 2) * Real.exp (K / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp1 hC) hp2 (Real.exp_pos _).le (by positivity)
      _ = c2 * rW L s x' ^ C * Real.exp (rW L s x' / 2) := by rw [hc2d]; ring
      _ ≤ max c1 c2 * rW L s x' ^ max c1 c2 * Real.exp (rW L s x' / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hc2 hp3 hrC (le_trans (le_trans hC hCc2) hc2)) hE0

theorem size_of_tame [CompactSpace X] (hn : ∀ y, logNormSec L s y ≤ 0)
    (hT : ∀ x, ∃ ψ a M, NChart A (U x) L s x ψ a M ∧ Tame a fun t => ph (ψ.symm t)) :
    ∃ C : ℝ, ∀ y ∉ bdry s, |ph y| ≤ C * Real.log (rW L s y) := by
  have key : ∀ x, ∃ (V' : Set X) (c : ℝ), IsOpen V' ∧ x ∈ V' ∧ ∀ x' ∈ V', x' ∉ bdry s →
      |ph x'| ≤ c * Real.log (rW L s x') := fun x => by
    obtain ⟨ψ, a, M, h, ht⟩ := hT x
    obtain ⟨V', c, h1, h2, -, h3⟩ := local_of_tame hn h ht
    exact ⟨V', c, h1, h2, fun x' a b => (h3 x' a b).1⟩
  choose V c h1 h2 h3 using key
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover V h1 fun x _ => Set.mem_iUnion.2 ⟨x, h2 x⟩
  refine ⟨∑ x ∈ F, |c x|, fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  have := (one_le_of_exp_le (exp_le_rW hn y)).2
  refine (h3 x y hyx hy).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (by linarith))
  exact Finset.single_le_sum (f := fun x => |c x|) (fun _ _ => abs_nonneg _) hx

theorem pshOn_of_local {V : Set X} (P : LocPot X)
    (hP : ∀ x z, z ∈ P.U x → ∃ W : Set X, IsOpen W ∧ z ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ w ∈ W ∩ P.U x ∩ P.U z, P.φ x w - P.φ z w = (G w).re)
    (h : ∀ z ∈ V, ∃ ψ : OpenPartialHomeomorph X (Fin n → ℂ), IsCompatChart A ψ ∧ z ∈ ψ.source ∧ ψ z = 0 ∧
      PshAt0 fun t => P.φ z (ψ.symm t)) : IsPshOn A V P := by
  intro x j y hy w
  obtain ⟨hyt, hyU, hyV⟩ := hy
  obtain ⟨ψ, hψc, hzs, hz0, hpsh⟩ := h _ hyV
  obtain ⟨Wd, hWo, hzW, G, hG, hdiff⟩ := hP x _ hyU
  have hτ : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψc j).1 y ⟨hyt, hzs⟩
  have hτy : (ψ ∘ (A.chart j).symm) y = 0 := hz0
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hyt, hzW⟩
  have hg2 : ContDiffAt ℝ 2 (fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ((ψ ∘ (A.chart j).symm) y) := by
    rw [hτy]
    exact hpsh.1
  have hgc : ContDiffAt ℝ 2 ((fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm)) y :=
    hg2.comp y ((hτ.contDiffAt).restrict_scalars ℝ)
  have hre : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart j).symm) y').re) y :=
    (Complex.reCLM.contDiff.contDiffAt).comp y ((hGa.contDiffAt).restrict_scalars ℝ)
  have hN : (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (Wd ∩ P.U x ∩ P.U ((A.chart j).symm y) ∩ ψ.source) ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm
      (((hWo.inter (P.isOpen_U x)).inter (P.isOpen_U _)).inter ψ.open_source)).mem_nhds
      ⟨hyt, ⟨⟨hzW, hyU⟩, P.mem_U _⟩, hzs⟩
  have heq : (P.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun y' =>
      ((fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm)) y' +
        1 * ((G ∘ (A.chart j).symm) y').re := by
    filter_upwards [hN] with y' hy'
    obtain ⟨-, ⟨⟨hW', hx'⟩, hz'⟩, hs'⟩ := hy'
    have := hdiff _ ⟨⟨hW', hx'⟩, hz'⟩
    simp only [Function.comp, ψ.left_inv hs', one_mul]
    linarith
  rw [levi_congr heq, levi_add_smul 1 hgc hre, levi_re_analytic hGa, levi_comp w hτ hg2, hτy]
  simpa using hpsh.2 _

end AnalyticReference.An
end
end

