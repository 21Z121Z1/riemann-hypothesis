import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormCutoffLogWeightLowerBound
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeightLevi

open Complex ComplexConjugate Filter

theorem deriv_zero_of_eqOn {χ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {c : ℝ}
    (h : ∀ s ∈ U, χ s = c) : ∀ s ∈ U, deriv χ s = 0 ∧ deriv (deriv χ) s = 0 := by
  have h1 : ∀ s ∈ U, deriv χ s = 0 := fun s hs => by
    have e : χ =ᶠ[𝓝 s] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hs) h
    rw [e.deriv_eq]; simp
  intro s hs
  refine ⟨h1 s hs, ?_⟩
  have e : deriv χ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := Filter.eventually_of_mem (hU.mem_nhds hs) h1
  rw [e.deriv_eq]; simp

theorem hasDerivAt_logShift {δ s : ℝ} (hs : 0 < s + δ) :
    HasDerivAt (fun s => Real.log ((s + δ) / 2)) (s + δ)⁻¹ s := by
  have h1 : HasDerivAt (fun s : ℝ => (s + δ) / 2) (1 / 2) s :=
    ((hasDerivAt_id' s).add_const δ).div_const 2
  convert h1.log (by positivity) using 1
  field_simp

theorem hasDerivAt_cutLog {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {δ s : ℝ} (hs : 0 < s + δ) :
    HasDerivAt (fun s => χ s * Real.log ((s + δ) / 2))
      (deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹) s := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  exact (hd s).hasDerivAt.mul (hasDerivAt_logShift hs)

theorem derivs_cutLog {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {δ t : ℝ} (ht : 0 < t + δ) :
    deriv (fun s => χ s * Real.log ((s + δ) / 2)) t =
        deriv χ t * Real.log ((t + δ) / 2) + χ t * (t + δ)⁻¹ ∧
      deriv (deriv (fun s => χ s * Real.log ((s + δ) / 2))) t =
        deriv (deriv χ) t * Real.log ((t + δ) / 2) + 2 * deriv χ t * (t + δ)⁻¹ -
          χ t * ((t + δ)⁻¹) ^ 2 := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hd2 : Differentiable ℝ (deriv χ) :=
    (contDiff_infty_iff_deriv.1 hχ).2.differentiable (by simp)
  have hU : Set.Ioi (-δ) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have e : deriv (fun s => χ s * Real.log ((s + δ) / 2)) =ᶠ[𝓝 t]
      fun s => deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹ :=
    Filter.eventually_of_mem hU fun s hs =>
      (hasDerivAt_cutLog hχ (by simp only [Set.mem_Ioi] at hs; linarith)).deriv
  refine ⟨(hasDerivAt_cutLog hχ ht).deriv, ?_⟩
  rw [e.deriv_eq]
  have hinv : HasDerivAt (fun s => (s + δ)⁻¹) (-1 / (t + δ) ^ 2) t :=
    ((hasDerivAt_id' t).add_const δ).inv ht.ne'
  have h : HasDerivAt (fun s => deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹) _ t :=
    ((hd2 t).hasDerivAt.mul (hasDerivAt_logShift ht)).add ((hd t).hasDerivAt.mul hinv)
  rw [h.deriv]
  field_simp
  ring

theorem cutLog_bounds (χ : ℝ → ℝ) (A : ℝ) (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (h1 : ∀ t, t ≤ 1 / 4 → χ t = 1) (h0 : ∀ t, 1 ≤ t → χ t = 0) (hA1 : ∀ t, |deriv χ t| ≤ A)
    (hA2 : ∀ t, |deriv (deriv χ) t| ≤ A) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    -(13 * A + 20) ≤ deriv (fun s => χ s * Real.log ((s + δ) / 2)) t ∧
      -(13 * A + 20) ≤ deriv (fun s => χ s * Real.log ((s + δ) / 2)) t +
        t * deriv (deriv (fun s => χ s * Real.log ((s + δ) / 2))) t := by
  have htd : 0 < t + δ := by linarith
  obtain ⟨e1, e2⟩ := derivs_cutLog hχ htd
  rw [e1, e2]
  have hA : 0 ≤ A := (abs_nonneg _).trans (hA1 0)
  set L := Real.log ((t + δ) / 2)
  set u := (t + δ)⁻¹ with hu_def
  have hu : 0 < u := inv_pos.2 htd
  have htu : t * u ≤ 1 := by
    rw [hu_def, ← div_eq_mul_inv, div_le_one htd]; linarith
  have htu0 : 0 ≤ t * u := mul_nonneg ht hu.le
  have hc0 := h01 t
  have hpos : 0 ≤ χ t * u * (1 - t * u) :=
    mul_nonneg (mul_nonneg hc0.1 hu.le) (by linarith)
  have hexp : deriv χ t * L + χ t * u + t * (deriv (deriv χ) t * L + 2 * deriv χ t * u - χ t * u ^ 2) =
      deriv χ t * L + t * (deriv (deriv χ) t * L) + 2 * (deriv χ t * (t * u)) +
        χ t * u * (1 - t * u) := by ring
  rw [hexp]
  by_cases hc : t < 1 / 4 ∨ 1 < t
  · have hz : deriv χ t = 0 ∧ deriv (deriv χ) t = 0 := by
      rcases hc with hc | hc
      · exact deriv_zero_of_eqOn isOpen_Iio (fun s hs => h1 s (le_of_lt hs)) t hc
      · exact deriv_zero_of_eqOn isOpen_Ioi (fun s hs => h0 s (le_of_lt hs)) t hc
    rw [hz.1, hz.2]
    have : 0 ≤ χ t * u := mul_nonneg hc0.1 hu.le
    constructor <;> nlinarith
  · push_neg at hc
    have hx1 : (t + δ) / 2 ≤ 1 := by linarith
    have hx0 : 1 / 8 ≤ (t + δ) / 2 := by linarith
    have hL0 : L ≤ 0 := Real.log_nonpos (by linarith) hx1
    have hl8 : Real.log (1 / 8) = -(3 * Real.log 2) := by
      rw [show (1 : ℝ) / 8 = ((2 : ℝ) ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
    have hL1 : -3 ≤ L := by
      have := Real.log_le_log (by norm_num) hx0
      have := Real.log_two_lt_d9
      linarith
    have hLabs : |L| ≤ 3 := abs_le.2 ⟨hL1, by linarith⟩
    have b1 : -(3 * A) ≤ deriv χ t * L := by
      have : |deriv χ t * L| ≤ A * 3 := by
        rw [abs_mul]; exact mul_le_mul (hA1 t) hLabs (abs_nonneg _) hA
      linarith [neg_abs_le (deriv χ t * L)]
    have b2 : -(3 * A) ≤ t * (deriv (deriv χ) t * L) := by
      have : |t * (deriv (deriv χ) t * L)| ≤ 1 * (A * 3) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht]
        exact mul_le_mul (by linarith) (mul_le_mul (hA2 t) hLabs (abs_nonneg _) hA)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
      linarith [neg_abs_le (t * (deriv (deriv χ) t * L))]
    have b3 : -A ≤ deriv χ t * (t * u) := by
      have : |deriv χ t * (t * u)| ≤ A * 1 := by
        rw [abs_mul, abs_of_nonneg htu0]
        exact mul_le_mul (hA1 t) htu htu0 hA
      linarith [neg_abs_le (deriv χ t * (t * u))]
    have : 0 ≤ χ t * u := mul_nonneg hc0.1 hu.le
    constructor <;> nlinarith

theorem normSq_sum_conj_mul_le {n : ℕ} (a b : Fin n → ℂ) :
    Complex.normSq (∑ m, conj (a m) * b m) ≤
      (∑ m, Complex.normSq (a m)) * ∑ m, Complex.normSq (b m) := by
  have h1 : ‖∑ m, conj (a m) * b m‖ ≤ ∑ m, ‖a m‖ * ‖b m‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ => by
      rw [norm_mul, Complex.norm_conj]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun m => ‖a m‖) (fun m => ‖b m‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ m, conj (a m) * b m‖ ^ 2 ≤ (∑ m, ‖a m‖ * ‖b m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem levi_cutLog_lower : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) →
    (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) →
    (∀ t, |deriv (deriv χ) t| ≤ A) → ∀ (n : ℕ) (ρ δ : ℝ), 0 < ρ → 0 < δ → δ ≤ 1 →
    ∀ (z : V n) (ξ : Fin n → ℂ), -((13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) ≤
      (leviV n (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ))
        z ξ).re := by
  intro χ A hχ h01 h1 h0 hA1 hA2 n ρ δ hρ hδ hδ1 z ξ
  set k : ℝ → ℝ := fun s => χ s * Real.log ((s + δ) / 2) with hk
  let L : Fin n → V n →L[ℂ] ℂ := fun j => ((ρ : ℂ)⁻¹) • EuclideanSpace.proj j
  have hLapp : ∀ j y, L j y = (ρ : ℂ)⁻¹ * y j := fun j y => by simp [L]
  set v : V n → ℝ := fun y => ∑ j, Complex.normSq (L j y) with hvdef
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hv : ∀ y : V n, ‖y‖ ^ 2 / ρ ^ 2 = v y := by
    intro y
    simp only [hvdef, hLapp, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal,
      EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    field_simp
  have hfun : (fun w : V n => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ))
      = fun w => ((k (v w) : ℝ) : ℂ) := by
    funext w; rw [hv w]
  rw [hfun]
  have hLc : ∀ j, ContDiffAt ℂ 2 (fun y => L j y) z := fun j => (L j).contDiff.contDiffAt
  have hu : ∀ j, ContDiffAt ℝ 2 (fun y => Complex.normSq (L j y)) z := fun j =>
    H.contDiffAt_normSq_comp (hLc j)
  have hvC : ContDiffAt ℝ 2 v z := ContDiffAt.sum fun j _ => hu j
  have ht0 : 0 ≤ v z := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hkC : ContDiffAt ℝ 2 k (v z) := by
    have hχ2 : ContDiffAt ℝ 2 χ (v z) := hχ.contDiffAt.of_le (by norm_cast)
    exact hχ2.mul (((contDiffAt_id.add contDiffAt_const).div_const (2 : ℝ)).log
      (by simp only [id]; positivity))
  rw [H.leviChain n k v z ξ hvC hkC]
  have hwdL : ∀ j m, wd n m (fun y => L j y) z = (ρ : ℂ)⁻¹ * (if j = m then 1 else 0) := by
    intro j m
    rw [wd_of_differentiableAt (L j).differentiableAt, (L j).fderiv, hLapp]
    simp [bas, EuclideanSpace.single_apply]
  have hLevi : leviV n (fun y => ((v y : ℝ) : ℂ)) z ξ =
      ((∑ j, Complex.normSq ((ρ : ℂ)⁻¹ * ξ j) : ℝ) : ℂ) := by
    rw [show (fun y => ((v y : ℝ) : ℂ)) = fun y => ((∑ j, Complex.normSq (L j y) : ℝ) : ℂ) from rfl,
      H.leviV_ofReal_sum hu, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.leviV_normSq_comp (hLc j)]
    simp [hwdL]
  have hwd : ∀ m, wd n m (fun y => ((v y : ℝ) : ℂ)) z = (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) := by
    intro m
    rw [show (fun y => ((v y : ℝ) : ℂ)) = fun y => ((∑ j, Complex.normSq (L j y) : ℝ) : ℂ) from rfl,
      H.wd_ofReal_sum (fun j => (hu j).differentiableAt (by simp))]
    refine (Finset.sum_congr rfl fun j _ => by rw [H.wd_normSq_comp (hLc j), hwdL]).trans ?_
    simp [hLapp]
  rw [hLevi]
  simp only [hwd]
  set P := ∑ j, Complex.normSq ((ρ : ℂ)⁻¹ * ξ j) with hP
  set N := Complex.normSq (∑ m, (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) * ξ m) with hN
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hNt : N ≤ v z * P := by
    have e : ∑ m, (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) * ξ m =
        ∑ m, conj ((ρ : ℂ)⁻¹ * z m) * ((ρ : ℂ)⁻¹ * ξ m) :=
      Finset.sum_congr rfl fun m _ => by ring
    have ev : v z = ∑ m, Complex.normSq ((ρ : ℂ)⁻¹ * z m) :=
      Finset.sum_congr rfl fun m _ => by rw [hLapp]
    rw [hN, e, ev, hP]
    exact normSq_sum_conj_mul_le _ _
  have hPe : (13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 = (13 * A + 20) * P := by
    rw [hP, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    field_simp
  rw [hPe]
  obtain ⟨b1, b2⟩ := cutLog_bounds χ A hχ h01 h1 h0 hA1 hA2 hδ hδ1 ht0
  by_cases hs : 0 ≤ deriv (deriv k) (v z)
  · have := mul_le_mul_of_nonneg_right b1 hP0
    have := mul_nonneg hs hN0
    nlinarith
  · push_neg at hs
    have h3 : deriv (deriv k) (v z) * (v z * P) ≤ deriv (deriv k) (v z) * N :=
      mul_le_mul_of_nonpos_left hNt hs.le
    have := mul_le_mul_of_nonneg_right b2 hP0
    nlinarith

end GlobalTheory.PeakWeightLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOrigin
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviWeightChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nmat_hasDerivAt (X : Data E r) {f : ℂ → V (nd X)} {f' : V (nd X)} {t : ℂ}
    (hf : HasDerivAt f f' t) (τ : X.Ψ) (a c : Fin r) :
    HasDerivAt (fun s => nmat X (f s) τ a c) (nmat X f' τ a c - if a = c then 1 else 0) t := by
  unfold nmat
  by_cases h : c < a
  · simp only [h, dif_pos, h.ne', if_false, sub_zero]
    exact
      ((PiLp.proj 2 (fun _ : Fin (nd X) => ℂ) ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).hasFDerivAt).comp_hasDerivAt t hf
  · simp only [h, dif_neg, not_false_eq_true, sub_self]
    exact hasDerivAt_const _ _

theorem nmat_zero_apply (X : Data E r) (τ : X.Ψ) (a c : Fin r) :
    nmat X 0 τ a c = if a = c then 1 else 0 := by
  have := congrFun (congrFun (IW.nmat_zero X τ) a) c
  simpa [mat, Matrix.one_apply] using this

theorem levi_transport_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x1 b : Frame X.Ψ r) (z : V (nd X)), IsOrth X x1 → z ∈ OmF X x0 → b ∈ Bor X.Ψ r → cpt X x0 z = rmul x1 b → ∀ ξ : Fin (nd X) → ℂ, ∃ ξ' : Fin (nd X) → ℂ, (∀ la : Wt X.Ψ r, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 ξ') ∧ ∃ B : Frame X.Ψ r, (∀ τ (a c : Fin r), c < a → B τ a c = 0) ∧ ∀ τ, mat x0 τ * (mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) = mat x1 τ * ((mat (nmat X (WithLp.toLp 2 ξ')) τ - 1) * mat b τ + mat B τ) := by
  intro E _ _ _ r X x0 x1 b z ho hz hb hxb ξ
  have hz1 : (0 : V (nd X)) ∈ OmF X x1 := IW.zero_mem_OmF X x1 ho
  have hxb' : cpt X x0 z = rmul (cpt X x1 0) b := by rw [IW.cpt_zero]; exact hxb
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 hz1 b hb
  rw [← hxb'] at h0
  have hcd : Differentiable ℂ (cpt X x0) := IW.cpt_diff X x0
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hbz : bf z = b := h0.2.2
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  set v : V (nd X) := WithLp.toLp 2 ξ with hv
  have hγ : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hγU : ∀ᶠ t in 𝓝 (0 : ℂ), z + t • v ∈ U := by
    have h := (hγ.continuousAt)
    simp only [ContinuousAt, zero_smul, add_zero] at h
    exact h (hU.mem_nhds hzU)
  have hbfD : HasDerivAt (fun t : ℂ => bf (z + t • v)) (fderiv ℂ bf z v) 0 :=
    (hbf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hΦD : HasDerivAt (fun t : ℂ => Φ (z + t • v)) (fderiv ℂ Φ z v) 0 :=
    (hΦ.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hbfE : ∀ τ a c, HasDerivAt (fun t : ℂ => bf (z + t • v) τ a c) (fderiv ℂ bf z v τ a c) 0 :=
    fun τ a c => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hbfD τ) a) c
  refine ⟨fun k => (fderiv ℂ Φ z v).ofLp k, fun la => ?_, fderiv ℂ bf z v, ?_, ?_⟩
  · have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
      classical
      intro w hw
      unfold bchar
      refine DifferentiableAt.differentiableWithinAt ?_
      refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
        fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
        fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
      have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
        differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
      have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
        differentiableAt_zpow.2
          (Or.inl (GlobalTheory.LeviTransfer.borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
      exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
    have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
      (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
    have hne : bchar la (bf z) ≠ 0 := IW.bchar_ne_zero X (hsplit _ hz h0.1).2.1 _
    have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
      rw [← GlobalTheory.LeviTransfer.metric_rmul normFactor_rightBorel_holds X la h1 h2, ← h3]
    have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
      rw [hΦz]
      exact (IW.phla_cpt_cdAt X x1 hz1 la).of_le HE.two_le_inf
    have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
      hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
    have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
      (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
    have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
    have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
    rw [hΦz] at hc
    unfold leviM
    rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
      HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
    exact congrArg Complex.re hc
  · intro τ a c hca
    have hev : (fun t : ℂ => bf (z + t • v) τ a c) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hγU] with t ht
      exact ((hsplit _ ht.1 ht.2).2.1 τ).2 a c hca
    exact (hbfE τ a c).unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev)
  · intro τ
    ext a c
    have hL : HasDerivAt (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c)
        (∑ k, x0 τ a k * (nmat X v τ k c - if k = c then 1 else 0)) 0 :=
      HasDerivAt.fun_sum fun k _ => (nmat_hasDerivAt X hγ τ k c).const_mul _
    have hR : HasDerivAt (fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c)
        (∑ k, ((∑ l, x1 τ a l * (nmat X (fderiv ℂ Φ z v) τ l k - if l = k then 1 else 0)) * bf (z + (0:ℂ) • v) τ k c
          + (∑ l, x1 τ a l * nmat X (Φ (z + (0:ℂ) • v)) τ l k) * fderiv ℂ bf z v τ k c)) 0 :=
      HasDerivAt.fun_sum fun k _ =>
        (HasDerivAt.fun_sum fun l _ => (nmat_hasDerivAt X hΦD τ l k).const_mul _).fun_mul (hbfE τ k c)
    have hev : (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c) =ᶠ[𝓝 0]
        fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c := by
      filter_upwards [hγU] with t ht
      have e0 : cpt X x0 (z + t • v) = rmul (cpt X x1 (Φ (z + t • v))) (bf (z + t • v)) :=
        (hsplit _ ht.1 ht.2).2.2
      have e := congrFun (congrFun (congrFun e0 τ) a) c
      simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at e
      exact e
    have heq := hL.unique (hR.congr_of_eventuallyEq hev)
    simp only [zero_smul, add_zero, hΦz, hbz, nmat_zero_apply] at heq
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, mat, Matrix.of_apply,
      WithLp.toLp_ofLp]
    rw [heq]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]

end GlobalTheory.LeviWeightChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMarginOrthonormalChartOrigin
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviOriginMargin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem chain_drop (r p : ℕ) (f : ℕ → ℝ) (g : ℝ)
    (hg : ∀ i, i + 1 < r → i + 1 ≠ p → g ≤ f i - f (i + 1)) :
    ∀ n i, i + n < r → (∀ k, i < k → k ≤ i + n → k ≠ p) → (n : ℝ) * g ≤ f i - f (i + n) := by
  intro n
  induction n with
  | zero => intro i _ _; simp
  | succ n ih =>
    intro i hr hk
    have h1 := ih i (by omega) (fun k h1 h2 => hk k h1 (by omega))
    have h2 := hg (i + n) (by omega) (hk _ (by omega) (by omega))
    have e : i + (n + 1) = i + n + 1 := by omega
    rw [e]
    push_cast
    linarith

theorem coeff_la {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) (hp0 : 0 < X.p0) (hpr : X.p0 < r)
    (hg0 : 0 ≤ g)
    (h1 : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b)
    (h2 : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a)
    (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    g ≤ sgn X.p0 a * sgn X.p0 b * ((la τ b : ℝ) - la τ a) := by
  set f : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) else 0 with hf
  have hfa : ∀ c : Fin r, f c = la τ c := fun c => by simp [hf, c.isLt]
  have hg : ∀ i, i + 1 < r → i + 1 ≠ X.p0 → g ≤ f i - f (i + 1) := by
    intro i hi hip
    have := h1 τ ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl hip
    simpa [hf, hi, show i < r by omega] using this
  have hch := chain_drop r X.p0 f g hg
  have hab' : (b : ℕ) < a := hab
  have hsame : (∀ k, (b : ℕ) < k → k ≤ b + ((a : ℕ) - b) → k ≠ X.p0) → g ≤ (la τ b : ℝ) - la τ a := by
    intro hk
    have := hch ((a : ℕ) - b) b (by omega) hk
    have e : (b : ℕ) + ((a : ℕ) - b) = a := by omega
    rw [e, hfa, hfa] at this
    have hn : (1 : ℝ) ≤ (((a : ℕ) - b : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ (a : ℕ) - b by omega)
    nlinarith
  rcases GlobalTheory.CurvMargin.coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
  · rw [e]; exact hsame (fun k _ hk => by omega)
  · rw [e]; exact hsame (fun k hk _ => by omega)
  · rw [e]

    have hA := hch ((r - 1) - a) a (by omega) (fun k hk _ => by omega)
    have hB := hch (b : ℕ) 0 (by omega) (fun k _ hk => by omega)
    have eA : (a : ℕ) + ((r - 1) - a) = r - 1 := by omega
    rw [eA, hfa] at hA
    rw [zero_add] at hB
    have hB' := hB
    rw [hfa] at hB'
    have h0 := h2 τ ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl
    have f0 : f 0 = (la τ ⟨0, by omega⟩ : ℝ) := by simp [hf, show 0 < r by omega]
    have fr : f (r - 1) = (la τ ⟨r - 1, by omega⟩ : ℝ) := by simp [hf, show r - 1 < r by omega]
    have hn1 : (0 : ℝ) ≤ (((r - 1 - a : ℕ)) : ℝ) * g := by positivity
    have hn2 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) * g := by positivity
    rw [fr] at hA
    rw [f0] at hB'
    linarith

theorem coeff_blk {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    0 ≤ sgn X.p0 a * sgn X.p0 b * ((GlobalTheory.CurvMargin.blockWt X τ b : ℝ) - GlobalTheory.CurvMargin.blockWt X τ a) ∧
    sgn X.p0 a * sgn X.p0 b * ((GlobalTheory.CurvMargin.blockWt X τ b : ℝ) - GlobalTheory.CurvMargin.blockWt X τ a) ≤ 1 := by
  have hab' : (b : ℕ) < a := hab
  unfold GlobalTheory.CurvMargin.blockWt sgn
  by_cases ha : (a : ℕ) < X.p0
  · have hb : (b : ℕ) < X.p0 := hab'.trans ha
    simp [ha, hb]
  · by_cases hb : (b : ℕ) < X.p0
    · simp [ha, hb]
    · simp [ha, hb]

theorem coeff_kap {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    sgn X.p0 a * sgn X.p0 b * ((kapW X τ b : ℝ) - kapW X τ a) ≤ 2 * r := by
  have hab' : (b : ℕ) < a := hab
  have ha : (a : ℕ) < r := a.isLt
  have hk : ((kapW X τ b : ℝ) - kapW X τ a) = 2 * (b : ℝ) - 2 * (a : ℝ) := by
    simp [kapW]
  rw [hk]
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have hba : (b : ℝ) < a := by exact_mod_cast hab'
  have har : (a : ℝ) < r := by exact_mod_cast ha
  unfold sgn
  split_ifs <;> nlinarith

theorem levi_margin_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (g bb : ℝ), 0 < X.p0 → X.p0 < r → IsOrth X x → 0 ≤ g → 0 ≤ bb → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a) → ∀ ξ : Fin (nd X) → ℂ, (g - bb - 2 * r) * ∑ j, ‖ξ j‖ ^ 2 ≤ leviM X (phla X la) x 0 ξ - bb * leviM X (phla X (GlobalTheory.CurvMargin.blockWt X)) x 0 ξ - leviM X (phla X (kapW X)) x 0 ξ := by
  intro E _ _ _ r X la x g bb hp0 hpr ho hg0 hbb h1 h2 ξ
  have hs : ∑ j, ‖ξ j‖ ^ 2 = ∑ e : Ent X, ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2 :=
    ((Fintype.equivFin (Ent X)).sum_comp (fun j => ‖ξ j‖ ^ 2)).symm
  rw [GlobalTheory.LeviZero.levi_phla_zero r X la x ho ξ, GlobalTheory.LeviZero.levi_phla_zero r X _ x ho ξ,
    GlobalTheory.LeviZero.levi_phla_zero r X _ x ho ξ,
    hs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
  have c1 := coeff_la X la g hp0 hpr hg0 h1 h2 τ a b hab
  have c2 := coeff_blk X τ a b hab
  have c3 := coeff_kap X τ a b hab
  set N := ‖ξ (Fintype.equivFin (Ent X) ⟨τ, ⟨(a, b), hab⟩⟩)‖ ^ 2
  have hN : 0 ≤ N := by positivity
  simp only at c1 c2 c3 ⊢
  nlinarith [mul_nonneg hbb hN, mul_nonneg (mul_nonneg hbb c2.1) hN, mul_nonneg (sub_nonneg.2 c2.2) (mul_nonneg hbb hN),
    mul_nonneg (sub_nonneg.2 c1) hN, mul_nonneg (sub_nonneg.2 c3) hN]

end GlobalTheory.LeviOriginMargin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsSumEqDefinitePairsSum
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem marked_field_pairs_sum_eq_definite_pairs_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ := by
  intro p _ G ha hn wt sel hsel Kf f r K φ hr hf hφ
  obtain ⟨e, he⟩ := GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd p G ha hn sel hsel
  unfold markedSumIrr dSumIrr
  convert GlobalTheory.finsum_ite_eq_of_equiv _ _ e (fun a : Cls G => wt (Quot.out a).pol * (Quot.out a).term Kf f r K φ)
    (fun b : DCls G => wt (Quot.out b).pol * (Quot.out b).term Kf f r K φ) fun q => by
    obtain ⟨hpol, hterm⟩ := he q
    show wt (Quot.out (e q).1).pol * (Quot.out (e q).1).term Kf f r K φ = wt (Quot.out q.1).pol * (Quot.out q.1).term Kf f r K φ
    rw [hpol, hterm Kf f r K φ hr hf hφ]

end GlobalTheory.LKDef
end

