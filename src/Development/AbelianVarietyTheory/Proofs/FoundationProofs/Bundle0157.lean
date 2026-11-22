import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmul
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

def rowZ (γ : SL(2, ℤ)) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun x := (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1)
  invFun x := (x.1 * γ 1 1 - x.2 * γ 1 0, -(x.1 * γ 0 1) + x.2 * γ 0 0)
  left_inv x := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    ext
    · simp only; linear_combination x.1 * h
    · simp only; linear_combination x.2 * h
  right_inv x := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    ext
    · simp only; linear_combination x.1 * h
    · simp only; linear_combination x.2 * h

theorem rowZ_apply (γ : SL(2, ℤ)) (x : ℤ × ℤ) :
    rowZ γ x = (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) := rfl

theorem rowZ_add_smul (γ : SL(2, ℤ)) (x v : ℤ × ℤ) (r : ℤ) :
    rowZ γ (x + r • v) = rowZ γ x + r • rowZ γ v := by
  simp only [rowZ_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.mk_add_mk, Prod.smul_mk]
  ext <;> simp only <;> ring

theorem dif_comp_rowZ (L : ℕ) (γ : SL(2, ℤ)) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => F (rowZ γ y)) = fun x => dif L (rowZ γ v) F (rowZ γ x) := by
  funext x
  simp only [dif, rowZ_add_smul]

theorem dif_const_mul (L : ℕ) (v : ℤ × ℤ) (c : ℂ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => c * F y) = fun x => c * dif L v F x := by
  funext x
  simp only [dif, ← Finset.mul_sum]
  ring

theorem lat_smul (j L : ℕ) (v : ℤ × ℤ) (Φ Φ' : ℤ × ℤ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ)
    (hΦ : ∀ x : ℤ × ℤ, Φ' (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x) :
    lat j 0 L v Φ (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ j *
      lat j 0 L (v.1 * γ 0 0 + v.2 * γ 1 0, v.1 * γ 0 1 + v.2 * γ 1 1) Φ' τ := by
  set D : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hD
  have hD0 : D ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ τ
    simpa [UpperHalfPlane.denom, hD] using this
  have hcoe : ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [hD]
  set H : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hH
  have hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + y.2)) =
      fun y => D ^ j * H (rowZ γ y) := by
    funext y
    simp only [hH, trm, rowZ_apply, hcoe, mul_zero, neg_mul, Real.rpow_zero, Complex.ofReal_one, mul_one]
    have : (y.1 : ℂ) * ((((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / D) + y.2 =
        ((((y.1 * γ 0 0 + y.2 * γ 1 0 : ℤ)) : ℂ) * τ + ((y.1 * γ 0 1 + y.2 * γ 1 1 : ℤ) : ℂ)) / D := by
      field_simp
      push_cast
      ring
    rw [this, div_pow, inv_div]
    ring_nf
  have hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + y.2)) x =
      D ^ j * dif L (rowZ γ v) (dif L (rowZ γ v) H) (rowZ γ x) := by
    intro x
    rw [hG, dif_const_mul, dif_const_mul]
    simp only
    rw [dif_comp_rowZ]
    rw [show (fun x => dif L (rowZ γ v) H (rowZ γ x)) = fun x => (dif L (rowZ γ v) H) (rowZ γ x) from rfl,
      dif_comp_rowZ]
  unfold lat
  simp_rw [hdd]
  have hΦ' : ∀ x, Φ x = Φ' (rowZ γ x) := fun x => (hΦ x).symm
  simp_rw [hΦ']
  rw [Equiv.tsum_eq (rowZ γ) (fun z => Φ' z * (D ^ j * dif L (rowZ γ v) (dif L (rowZ γ v) H) z)),
    ← tsum_mul_left]
  congr 1
  funext x
  rw [hH]
  simp only [rowZ_apply]
  ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrence
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem norm_le_of_bounded_two_step_recursion (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ) (hR : 0 ≤ R)
    (h0 : c 0 = 1) (h1 : c 1 = x + y)
    (hrec : ∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r)
    (hb : ∀ r, ‖c r‖ ≤ C * R ^ r) : ‖x‖ ≤ R := by
  have hd : ∀ r : ℕ, c (r + 1) - y * c r = x ^ (r + 1) := by
    intro r
    induction r with
    | zero => simp [h0, h1]
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by ring]
      linear_combination hrec n + x * ih
  have key : ∀ r : ℕ, ‖x‖ ^ (r + 1) ≤ C * (R + ‖y‖) * R ^ r := by
    intro r
    calc ‖x‖ ^ (r + 1) = ‖c (r + 1) - y * c r‖ := by rw [hd r, norm_pow]
      _ ≤ ‖c (r + 1)‖ + ‖y‖ * ‖c r‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ C * R ^ (r + 1) + ‖y‖ * (C * R ^ r) :=
          add_le_add (hb _) (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
      _ = C * (R + ‖y‖) * R ^ r := by ring
  by_contra hlt
  push_neg at hlt
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hlt
  have hq0 : 0 ≤ R / ‖x‖ := div_nonneg hR hxpos.le
  have hq1 : R / ‖x‖ < 1 := (div_lt_one hxpos).2 hlt
  have ht : Tendsto (fun r : ℕ => C * (R + ‖y‖) * (R / ‖x‖) ^ r) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C * (R + ‖y‖))
  have hle : ∀ r : ℕ, ‖x‖ ≤ C * (R + ‖y‖) * (R / ‖x‖) ^ r := by
    intro r
    have hpos : 0 < ‖x‖ ^ r := pow_pos hxpos r
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpos, ← pow_succ']
    exact key r
  have : ‖x‖ ≤ 0 := ge_of_tendsto' ht hle
  linarith

theorem roots_norm_le_of_bounded_two_step_recursion :
    ∀ (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ), 0 ≤ R → c 0 = 1 → c 1 = x + y →
      (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∀ r, ‖c r‖ ≤ C * R ^ r) →
      ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
  intro x y c C R hR h0 h1 hrec hb
  refine ⟨norm_le_of_bounded_two_step_recursion x y c C R hR h0 h1 hrec hb,
    norm_le_of_bounded_two_step_recursion y x c C R hR h0 (by rw [h1, add_comm]) ?_ hb⟩
  intro r
  rw [hrec r]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SecondDifferenceInvPowBound
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.SecondDiff

lemma half_le_norm {z w : ℂ} (hw : ‖w - z‖ ≤ ‖z‖ / 2) : ‖z‖ / 2 ≤ ‖w‖ := by
  have h := norm_sub_norm_le z w
  rw [norm_sub_rev] at h
  linarith

lemma ne_zero_of_near {z w : ℂ} (hz : z ≠ 0) (hw : ‖w - z‖ ≤ ‖z‖ / 2) : w ≠ 0 := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := half_le_norm hw
  intro h0
  rw [h0, norm_zero] at h
  linarith

lemma zpow_neg_lip (n : ℕ) {z u v : ℂ} (hz : z ≠ 0)
    (hu : ‖u - z‖ ≤ ‖z‖ / 2) (hv : ‖v - z‖ ≤ ‖z‖ / 2) :
    ‖u ^ (-(n:ℤ)) - v ^ (-(n:ℤ))‖ ≤ n * (2 / ‖z‖) ^ (n + 1) * ‖u - v‖ := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hmem : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), ‖w - z‖ ≤ ‖z‖ / 2 := by
    intro w hw; simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hd : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), HasDerivAt (fun x : ℂ => x ^ (-(n:ℤ)))
      (((-(n:ℤ) : ℤ) : ℂ) * w ^ (-(n:ℤ) - 1)) w :=
    fun w hw => hasDerivAt_zpow _ w (Or.inl (ne_zero_of_near hz (hmem w hw)))
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x : ℂ => x ^ (-(n:ℤ)))
    (s := Metric.closedBall z (‖z‖ / 2)) (x := v) (y := u) (C := n * (2 / ‖z‖) ^ (n + 1))
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by
      rw [(hd w hw).deriv]
      have hw' : ‖z‖ / 2 ≤ ‖w‖ := half_le_norm (hmem w hw)
      have hwpos : 0 < ‖w‖ := by linarith
      rw [norm_mul, norm_zpow]
      have e1 : ‖(((-(n:ℤ)) : ℤ) : ℂ)‖ = n := by simp
      have e2 : -(n:ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, zpow_neg, zpow_natCast, ← inv_div, inv_pow]
      gcongr)
    (convex_closedBall z _)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hv)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hu)
  simpa using key

theorem second_diff_inv_pow : ∀ j : ℕ, ∃ C : ℝ, ∀ z a b : ℂ, z ≠ 0 → 4 * ‖a‖ ≤ ‖z‖ → 4 * ‖b‖ ≤ ‖z‖ →
    ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹‖
      ≤ C * ‖a‖ * ‖b‖ / ‖z‖ ^ (j + 2) := by
  intro j
  refine ⟨j * (j + 1) * 2 ^ (j + 2), ?_⟩
  intro z a b hz ha hb
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set g : ℂ → ℂ := fun w => w ^ (-(j:ℤ)) - (w + a) ^ (-(j:ℤ)) with hg
  have hmem : ∀ w ∈ Metric.closedBall z (‖z‖ / 4), ‖w - z‖ ≤ ‖z‖ / 2 ∧ ‖w + a - z‖ ≤ ‖z‖ / 2 := by
    intro w hw
    have h : ‖w - z‖ ≤ ‖z‖ / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    refine ⟨by linarith, ?_⟩
    calc ‖w + a - z‖ = ‖(w - z) + a‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖a‖ := norm_add_le _ _
      _ ≤ ‖z‖ / 2 := by linarith
  have hd : ∀ w ∈ Metric.closedBall z (‖z‖ / 4), HasDerivAt g
      ((((-(j:ℤ)) : ℤ) : ℂ) * (w ^ (-(j:ℤ) - 1) - (w + a) ^ (-(j:ℤ) - 1))) w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hmem w hw
    have d1 := hasDerivAt_zpow (-(j:ℤ)) w (Or.inl (ne_zero_of_near hz h1))
    have d2 := (hasDerivAt_zpow (-(j:ℤ)) (w + a) (Or.inl (ne_zero_of_near hz h2))).comp_add_const w a
    rw [mul_sub]
    exact d1.sub d2
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := g)
    (s := Metric.closedBall z (‖z‖ / 4)) (x := z) (y := z + b)
    (C := j * ((j + 1 : ℕ) * (2 / ‖z‖) ^ ((j + 1 : ℕ) + 1) * ‖a‖))
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by
      rw [(hd w hw).deriv, norm_mul]
      obtain ⟨h1, h2⟩ := hmem w hw
      have e1 : ‖(((-(j:ℤ)) : ℤ) : ℂ)‖ = j := by simp
      have e2 : -(j:ℤ) - 1 = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2]
      have L := zpow_neg_lip (j + 1) hz h1 h2
      have e3 : ‖w - (w + a)‖ = ‖a‖ := by rw [sub_add_cancel_left, norm_neg]
      rw [e3] at L
      gcongr)
    (convex_closedBall z _)
    (by simp [Metric.mem_closedBall, dist_eq_norm]; positivity)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using (by linarith : ‖b‖ ≤ ‖z‖ / 4))
  have eq : (z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹ = -(g (z + b) - g z) := by
    simp only [hg, zpow_neg, zpow_natCast]
    rw [show z + b + a = z + a + b by ring]
    ring
  rw [eq, norm_neg]
  refine key.trans (le_of_eq ?_)
  rw [add_sub_cancel_left, div_pow]
  push_cast
  field_simp

end GlobalTheory.EisM.SecondDiff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem slzDen_ne_zero (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    ((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rcases him with h0 | h0
  · rw [h0] at hre
    simp at hre
    rw [Matrix.det_fin_two, h0, hre] at hδ
    simp at hδ
  · exact absurd h0 τ.im_pos.ne'

theorem slzMob_im (δ : M2) (τ : ℍ) :
    ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))).im
      = (δ.det : ℝ) * τ.im / Complex.normSq (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
  rw [Complex.div_im, Matrix.det_fin_two]
  simp
  push_cast
  ring

theorem slzMob_im_pos (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    0 < ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))).im := by
  rw [slzMob_im]
  apply div_pos
  · exact mul_pos (by exact_mod_cast hδ) τ.im_pos
  · exact Complex.normSq_pos.2 (slzDen_ne_zero δ hδ τ)

theorem slzMob_coe (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    ((ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))) : ℍ) : ℂ)
      = (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
  rw [ofComplex_apply_of_im_pos (slzMob_im_pos δ hδ τ)]

theorem automorphyFactor_mobius_cocycle_complex (a b c d a' b' c' d' t : ℂ) (h1 : c' * t + d' ≠ 0)
    (h2 : c * ((a' * t + b') / (c' * t + d')) + d ≠ 0) :
    (c * a' + d * c') * t + (c * b' + d * d') = (c * ((a' * t + b') / (c' * t + d')) + d) * (c' * t + d') ∧
    ((a * a' + b * c') * t + (a * b' + b * d')) / ((c * a' + d * c') * t + (c * b' + d * d'))
      = (a * ((a' * t + b') / (c' * t + d')) + b) / (c * ((a' * t + b') / (c' * t + d')) + d) := by
  have e1 : (c * a' + d * c') * t + (c * b' + d * d') = (c * ((a' * t + b') / (c' * t + d')) + d) * (c' * t + d') := by
    field_simp
    ring
  refine ⟨e1, ?_⟩
  rw [e1]
  field_simp
  ring

theorem slz_mul (k : ℕ) (f : ℍ → ℂ) (δ δ' : M2) (hδ : 0 < δ.det) (hδ' : 0 < δ'.det) :
    slz k (δ * δ') f = slz k δ' (slz k δ f) := by
  funext τ
  have h2 := slzDen_ne_zero δ hδ (ofComplex ((((δ' 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ' 0 1 : ℤ) : ℂ)) / (((δ' 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ' 1 1 : ℤ) : ℂ))))
  rw [slzMob_coe δ' hδ' τ] at h2
  obtain ⟨e1, e2⟩ := automorphyFactor_mobius_cocycle_complex ((δ 0 0 : ℤ) : ℂ) ((δ 0 1 : ℤ) : ℂ) ((δ 1 0 : ℤ) : ℂ) ((δ 1 1 : ℤ) : ℂ)
    ((δ' 0 0 : ℤ) : ℂ) ((δ' 0 1 : ℤ) : ℂ) ((δ' 1 0 : ℤ) : ℂ) ((δ' 1 1 : ℤ) : ℂ) (τ : ℂ) (slzDen_ne_zero δ' hδ' τ) h2
  simp only [slz]
  rw [slzMob_coe δ' hδ' τ, Matrix.det_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [e2, e1]
  simp only [mul_pow, mul_inv]
  ring

theorem slz_SL (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ) := by
  have hdet : (γ : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  have hg : ofComplex (((((γ : M2) 0 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : M2) 0 1 : ℤ) : ℂ)) / ((((γ : M2) 1 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : M2) 1 1 : ℤ) : ℂ))) = γ • τ := by
    ext
    rw [slzMob_coe _ (by rw [hdet]; exact one_pos) τ, coe_specialLinearGroup_apply]
    simp
  simp only [slz]
  rw [hg, hdet]
  simp

theorem slzDen_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ≠ 0 :=
  slzDen_ne_zero (γ : M2) (by rw [Matrix.SpecialLinearGroup.det_coe γ]; exact one_pos) τ

theorem slz_continuous (k : ℕ) (f : ℍ → ℂ) (δ : M2) (hδ : 0 < δ.det) (hf : Continuous f) :
    Continuous (slz k δ f) := by
  have hw : Continuous (fun τ : ℍ => (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))) :=
    ((continuous_const.mul continuous_coe).add continuous_const).div
      ((continuous_const.mul continuous_coe).add continuous_const) (slzDen_ne_zero δ hδ)
  have hg : Continuous (fun τ : ℍ => ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)))) := by
    rw [isOpenEmbedding_coe.isInducing.continuous_iff]
    have : (UpperHalfPlane.coe ∘ fun τ : ℍ => ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))))
        = fun τ : ℍ => (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
      funext τ
      exact slzMob_coe δ hδ τ
    rw [this]
    exact hw
  have hj : Continuous (fun τ : ℍ => ((((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹) :=
    (((continuous_const.mul continuous_coe).add continuous_const).pow k).inv₀
      (fun τ => pow_ne_zero k (slzDen_ne_zero δ hδ τ))
  exact (continuous_const.mul hj).mul (hf.comp hg)

theorem slz_scalar (k : ℕ) (f : ℍ → ℂ) (hk : 1 ≤ k) (n : ℕ) (τ : ℍ) (hn : 0 < n) :
    slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hτ : ofComplex ((((n : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((n : ℤ) : ℂ))) = τ := by
    have : (((n : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((n : ℤ) : ℂ)) = (τ : ℂ) := by
      simp only [Int.cast_zero, Int.cast_natCast, add_zero, zero_mul, zero_add]
      exact mul_div_cancel_left₀ _ hn'
    rw [this]
    exact ofComplex_apply τ
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of]
  rw [hτ]
  push_cast
  field_simp
  ring

theorem slz_props : ∀ (k : ℕ) (f : ℍ → ℂ), 1 ≤ k → (∀ δ δ' : M2, 0 < δ.det → 0 < δ'.det → slz k (δ * δ') f = slz k δ' (slz k δ f)) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ)) ∧ (∀ (L : ℕ) (χ : ℤ → ℂ), Inv k L χ f ↔ ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → slz k (γ : M2) f = fun τ => χ (γ 1 1) * f τ) ∧ (∀ δ : M2, 0 < δ.det → Continuous f → Continuous (slz k δ f)) ∧ ∀ (n : ℕ) (τ : ℍ), 0 < n → slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  intro k f hk
  refine ⟨fun δ δ' hδ hδ' => slz_mul k f δ δ' hδ hδ', fun γ τ => slz_SL k f γ τ, ?_,
    fun δ hδ hf => slz_continuous k f δ hδ hf, fun n τ hn => slz_scalar k f hk n τ hn⟩
  intro L χ
  constructor
  · intro h γ hγ
    funext τ
    have hne := pow_ne_zero k (slzDen_SL_ne_zero γ τ)
    rw [slz_SL, h γ hγ τ]
    field_simp
  · intro h γ hγ τ
    have := congrFun (h γ hγ) τ
    rw [slz_SL, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero k (slzDen_SL_ne_zero γ τ))] at this
    rw [this]
    ring

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductModularSTransform
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory

open GlobalTheory.Sieg

lemma Sieg.cthS_ee_pow (w : ℂ) (n : ℕ) : ee w ^ n = ee ((n : ℂ) * w) := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma Sieg.cthS_negI_pow (c : ℕ) (hc : Nat.Coprime c 6) : (-Complex.I) ^ (c ^ 2) = -Complex.I := by
  have h2 : Nat.Coprime c 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
  have hodd : Odd c := by
    rcases Nat.even_or_odd c with h | h
    · exfalso
      obtain ⟨j, hj⟩ := h
      have : 2 ∣ Nat.gcd c 2 := Nat.dvd_gcd ⟨j, by omega⟩ dvd_rfl
      rw [h2] at this
      omega
    · exact h
  obtain ⟨j, rfl⟩ := hodd
  have : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring
  rw [this, pow_succ, pow_mul]
  have h4 : (-Complex.I) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp
  rw [h4, one_pow, one_mul]

theorem Sieg.cth_modular_S (c : ℕ) (τ : ℍ) (z : ℂ) (h1 : 1 < c) (hc : Nat.Coprime c 6)
    (hz : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) :
    cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [inv_neg]

  have hB : th ((c : ℂ) * z) τ ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice τ _).1 h
    exact hz m n hmn

  have hB' : th ((c : ℂ) * (z / (τ : ℂ))) (ModularGroup.S • τ) ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice _ _).1 h
    rw [hS] at hmn
    apply hz n (-m)
    have : (c : ℂ) * z = (τ : ℂ) * ((c : ℂ) * (z / (τ : ℂ))) := by field_simp
    rw [this, hmn]
    push_cast
    field_simp
    ring
  rw [GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB', GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB]
  rw [show (c : ℂ) * (z / (τ : ℂ)) = ((c : ℂ) * z) / (τ : ℂ) by ring]
  rw [GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ z, GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ ((c : ℂ) * z)]
  have hee : ee (z ^ 2 / (2 * (τ : ℂ))) ^ (c ^ 2) = ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) := by
    rw [Sieg.cthS_ee_pow]
    congr 1
    push_cast
    ring
  have hE : ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have hI : (-Complex.I) ≠ 0 := by simp
  rw [mul_pow, mul_pow, Sieg.cthS_negI_pow c hc, hee]
  field_simp
  rw [mul_comm, mul_div_assoc, div_self (by unfold ee; exact Complex.exp_ne_zero _), mul_one]

end GlobalTheory
end

