import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0004
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
import Development.AutomorphicArithmetic.WhittakerHecke.SummableTsumInvOneAddHeightPowLe
import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0013
import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0002

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.MeasurableWhittakerIdeleDiagTorusMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open private UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_n UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_mkE UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_ψ from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE

private theorem cont_aE {K : Type} [Field K] [NumberField K] : Continuous (aE : (A K)ˣ → GL (Fin 2) (A K)) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_val, continuous_const, continuous_const, continuous_const]
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_coe_inv, continuous_const, continuous_const, continuous_const]

theorem UpperTheory.measurable_whittaker_idele_diagTorus_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        Measurable (fun p : IdeleGroup ℚ × G1 ℚ => Wo D φ (em E (aE p.1 * gl p.2))) := by
  intro E _ _ D ω φ h
  have hem : Continuous (em E) := Continuous.units_map _
    (continuous_matrix fun i j => AdeleBaseChange.continuous_adeleMap.comp (continuous_id.matrix_elem i j))
  have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => em E (aE p.1 * gl p.2) :=
    hem.comp ((cont_aE.comp continuous_fst).mul (M.continuous_gl.comp continuous_snd))
  have h2 : Continuous fun q : (IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ) => φ (nE D q.2 * em E (aE q.1.1 * gl q.1.2)) * ψ (q.2 1) :=
    (h.cont.comp (((UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_n.comp (UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_mkE D)).comp continuous_snd).mul (h1.comp continuous_fst))).mul
      (UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_ψ.comp ((continuous_apply 1).comp continuous_snd))
  haveI : BorelSpace ((IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ)) := inferInstance
  exact (h2.measurable.stronglyMeasurable.integral_prod_right' (ν := (adeleMeasurePi ℚ).restrict (FS2 ℚ))).measurable
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.NormThetaSeriesSiegelSetLeExp
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.QuaternionSwap

private noncomputable def Yv (b : A ℚ) (a : (A ℚ)ˣ) (ξ : Fin 2 → ℚ) : Fin 2 → A ℚ :=
  ![rt (ξ 0) * (a : A ℚ), (rt (ξ 0) * b + rt (ξ 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)]

private theorem row_eq (b : A ℚ) (a : (A ℚ)ˣ) (k : GL (Fin 2) (A ℚ)) (ξ : Fin 2 → ℚ) :
    (fun i => rt (ξ i)) ᵥ* (gl (nU b * mD a) * k).val = Yv b a ξ ᵥ* k.val := by
  have h1 : (gl (nU b * mD a) * k).val = (nU b * mD a).val * k.val := rfl
  rw [h1, ← Matrix.vecMul_vecMul]
  congr 1
  have h2 : (nU b * mD a).val = !![1, b; 0, 1] * !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  rw [h2]
  funext j
  fin_cases j <;> simp [Yv, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply] <;> ring

private def swapQ (q : ℚ) (hq : q ≠ 0) : Rw ℚ ≃ Rw ℚ where
  toFun ξ := ⟨![q * ξ.1 0, q⁻¹ * ξ.1 1], fun h => ξ.2 (by
    funext i
    fin_cases i
    · have := congrFun h 0
      simpa [hq] using this
    · have := congrFun h 1
      simpa [hq] using this)⟩
  invFun ξ := ⟨![q⁻¹ * ξ.1 0, q * ξ.1 1], fun h => ξ.2 (by
    funext i
    fin_cases i
    · have := congrFun h 0
      simpa [hq] using this
    · have := congrFun h 1
      simpa [hq] using this)⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [hq]
  right_inv ξ := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [hq]

private theorem Yv_swap (q : ℚ) (hq : q ≠ 0) (b : A ℚ) (a a' : (A ℚ)ˣ) (ha : (a' : A ℚ) = rt q * (a : A ℚ))
    (ξ : Rw ℚ) : Yv b a (swapQ q hq ξ).1 = Yv (rt (q ^ 2) * b) a' ξ.1 := by
  have hqq : rt q * rt q⁻¹ = (1 : A ℚ) := by
    rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  have hinv : ((a'⁻¹ : (A ℚ)ˣ) : A ℚ) = rt q⁻¹ * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [ha]
    calc rt q * (a : A ℚ) * (rt q⁻¹ * ((a⁻¹ : (A ℚ)ˣ) : A ℚ))
        = (rt q * rt q⁻¹) * ((a : A ℚ) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)) := by ring
      _ = 1 := by rw [hqq, Units.mul_inv, one_mul]
  have rm : ∀ x y : ℚ, rt (x * y) = rt x * rt y := fun x y => map_mul (algebraMap ℚ (A ℚ)) x y
  funext j
  fin_cases j
  · change rt (q * ξ.1 0) * (a : A ℚ) = rt (ξ.1 0) * (a' : A ℚ)
    rw [ha, rm]
    ring
  · change (rt (q * ξ.1 0) * b + rt (q⁻¹ * ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) =
      (rt (ξ.1 0) * (rt (q ^ 2) * b) + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ)
    have e2 : rt (q ^ 2) = rt q * rt q := by rw [pow_two, rm]
    rw [hinv, rm, rm, e2]
    have e : rt q = rt q * rt q * rt q⁻¹ := by rw [mul_assoc, hqq, mul_one]
    calc (rt q * rt (ξ.1 0) * b + rt q⁻¹ * rt (ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)
        = ((rt q * rt q * rt q⁻¹) * rt (ξ.1 0) * b + rt q⁻¹ * rt (ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by rw [← e]
      _ = _ := by ring

private theorem re_mul (x y : A ℚ) : re (x * y) = re x * re y := by
  simp [re, map_mul]
private theorem re_add (x y : A ℚ) : re (x + y) = re x + re y := by
  simp [re, map_add]
private theorem re_rat (q : ℚ) : re (rt q) = (q : ℝ) := by
  refine (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal Rat.infinitePlace) (WithAbs.toAbs _ q)).trans ?_
  simp
private theorem re_inv (a : (A ℚ)ˣ) : re ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = (re (a : A ℚ))⁻¹ := by
  have h : re (a : A ℚ) * re ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
    rw [← re_mul, Units.mul_inv]
    simp [re]
  exact eq_inv_of_mul_eq_one_right h

end UpperTheory.QuaternionSwap

open UpperTheory.QuaternionSwap in
theorem UpperTheory.norm_thetaSeries_siegelSet_le_exp :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi ℚ (Fin 2) → ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ (c : ℝ), 0 < c → ∀ n : ℕ,
        ∃ (r : ℕ) (B : ℝ), ∀ t : ℝ, 0 ≤ t → ∀ (b : A ℚ) (a : (A ℚ)ˣ), ∀ k ∈ C, c ≤ ab a →
          ‖ThR Φ t (gl (nU b * mD a) * k)‖ ≤ B * Real.exp (-((n : ℝ) * t)) * ab a ^ r := by
  intro Φ hΦ C hC c hc n
  obtain ⟨B0, κ, L, hB0, hκ, hκ1, hL, hmaj⟩ := UpperTheory.schwartzBruhat_translate_decay_bound Φ hΦ C hC (n + 4)
  obtain ⟨S, Bu, hS, hBu, hred⟩ := UpperTheory.exists_rat_mul_idele_finitePart_mem_compact_of_le_norm c hc
  obtain ⟨d, hd, hden⟩ := UpperTheory.exists_common_denom_of_isCompact_unipotent_translates L hL S hS
  obtain ⟨B1, hB1, hsum⟩ := UpperTheory.summable_tsum_inv_one_add_height_pow_le n d κ Bu hd hκ hκ1 hBu
  refine ⟨n + 2, B0 * B1 * (Bu / c) ^ (n + 2), fun t ht b a k hk hca => ?_⟩
  obtain ⟨q, a', u, hq, ha', hu, hf, hfi, hlo, hhi⟩ := hred a hca
  set b' : A ℚ := rt (q ^ 2) * b with hb'
  set α : ℝ := |re (a' : A ℚ)| with hα
  set β : ℝ := re b' with hβ
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.2 (by linarith)) hlo
  have hab : 0 < ab a := lt_of_lt_of_le hc hca
  set T : ℝ := Bu * (ab a / c) with hT
  have hT1 : 1 ≤ T := by
    have : 1 ≤ ab a / c := (one_le_div hc).2 hca
    nlinarith
  let R : Set (Rw ℚ) := {ξ | (fun j => (Yv b' a' ξ.1 j).2) ∈ L}
  let Wt : Rw ℚ → ℝ := fun ξ =>
    ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹
  have hfin : ∀ ξ : Fin 2 → ℚ, (fun j => (Yv b' a' ξ j).2) =
      ![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2,
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b'.2 + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) *
          ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2] := by
    intro ξ
    funext j
    fin_cases j
    · change (rt (ξ 0)).2 * (a' : A ℚ).2 = _
      rw [hf]
      rfl
    · change ((rt (ξ 0)).2 * b'.2 + (rt (ξ 1)).2) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _
      rw [hfi]
      rfl
  have hR : ∀ ξ ∈ R, ∀ ξ' ∈ R, _ := fun ξ h ξ' h' =>
    hden u hu b'.2 ξ.1 ξ'.1 (by have := h; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this)
      (by have := h'; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this)
  obtain ⟨hs, hle⟩ := hsum R β α T t ht hlo hhi hT1 (fun ξ h => (hR ξ h ξ h).1) (fun ξ h => (hR ξ h ξ h).2.1)
    (fun ξ h ξ' h' => (hR ξ h ξ' h').2.2)
  have hterm : ∀ ξ : Rw ℚ, ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ ≤ B0 * R.indicator Wt ξ := by
    intro ξ
    obtain ⟨h1, h2⟩ := hmaj t k hk (Yv b' a' ξ.1)
    have e0 : |re (Yv b' a' ξ.1 0)| = |((ξ.1 0 : ℚ) : ℝ)| * α := by
      change |re (rt (ξ.1 0) * (a' : A ℚ))| = _
      rw [re_mul, re_rat, abs_mul]
    have e1 : |re (Yv b' a' ξ.1 1)| = |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α := by
      change |re ((rt (ξ.1 0) * b' + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ))| = _
      rw [re_mul, re_add, re_mul, re_rat, re_rat, re_inv, abs_mul, abs_inv, div_eq_mul_inv]
    by_cases hξ : ξ ∈ R
    · rw [Set.indicator_of_mem hξ]
      rw [e0, e1] at h1
      exact h1
    · rw [Set.indicator_of_notMem hξ, mul_zero]
      have h0 : (Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j) = 0 := by
        by_contra h
        exact hξ (h2 h)
      rw [h0, norm_zero]
  have hrew : ThR Φ t (gl (nU b * mD a) * k) =
      ∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j := by
    unfold ThR
    rw [← (swapQ q hq).tsum_eq]
    refine tsum_congr fun ξ => ?_
    rw [row_eq, Yv_swap q hq b a a' ha' ξ]
  have hsn : Summable fun ξ : Rw ℚ => ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hs.mul_left B0)
  rw [hrew]
  calc ‖∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖
      ≤ ∑' ξ : Rw ℚ, ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ξ : Rw ℚ, B0 * R.indicator Wt ξ := hsn.tsum_le_tsum hterm (hs.mul_left _)
    _ = B0 * ∑' ξ : Rw ℚ, R.indicator Wt ξ := tsum_mul_left
    _ ≤ B0 * (B1 * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)) := mul_le_mul_of_nonneg_left hle hB0
    _ = B0 * B1 * (Bu / c) ^ (n + 2) * Real.exp (-((n : ℝ) * t)) * ab a ^ (n + 2) := by
        have : T = Bu / c * ab a := by rw [hT]; ring
        rw [this, mul_pow]
        ring
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.PowerSeriesCompleteHomogeneousTwoMulEqOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem UpperTheory.geometric_power_series_inverse (x : ℂ) :
    (PowerSeries.mk fun k : ℕ => x ^ k) * (1 - PowerSeries.C x * PowerSeries.X) = 1 := by
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases n with
  | zero => simp
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
    simp [PowerSeries.coeff_one, pow_succ]

theorem UpperTheory.powerSeries_completeHomogeneous_two_mul_eq_one :
    ∀ x y : ℂ, (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i))) * ((1 - PowerSeries.C x * PowerSeries.X) * (1 - PowerSeries.C y * PowerSeries.X)) = 1 := by
  intro x y
  have h : (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)))
      = (PowerSeries.mk fun k : ℕ => x ^ k) * (PowerSeries.mk fun k : ℕ => y ^ k) := by
    ext n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp
  rw [h, mul_mul_mul_comm, UpperTheory.geometric_power_series_inverse, UpperTheory.geometric_power_series_inverse, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.RankinSelbergLocalGeneratingSeriesIdentity
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private def UpperTheory.powerSeriesFirstDifferenceSeq (a : ℂ) (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => f 0
  | k + 1 => f (k + 1) - a * f k

private theorem UpperTheory.power_series_mul_linear (a : ℂ) (f : ℕ → ℂ) :
    PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk (UpperTheory.powerSeriesFirstDifferenceSeq a f) := by
  have h : PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk f - PowerSeries.C a * (PowerSeries.mk f * PowerSeries.X) := by ring
  rw [h]
  ext k
  cases k with
  | zero => simp [UpperTheory.powerSeriesFirstDifferenceSeq]
  | succ k =>
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X]
    simp [UpperTheory.powerSeriesFirstDifferenceSeq]

private theorem UpperTheory.geometric_sum_recurrence (x y : ℂ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1 + 1), x ^ i * y ^ (k + 1 - i)) =
      x ^ (k + 1) + y * ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.succ_sub hi', pow_succ]
  ring

private theorem UpperTheory.product_four_geometric_series (x y x' y' c : ℂ) (S T : ℕ → ℂ)
    (hS0 : S 0 = 1) (hT0 : T 0 = 1)
    (hS : ∀ k, S (k + 1) = x ^ (k + 1) + y * S k)
    (hT : ∀ k, T (k + 1) = x' ^ (k + 1) + y' * T k) :
    (PowerSeries.mk fun k : ℕ => c ^ k * S k * T k) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear,
    UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear]
  have hS2 : ∀ k, S (k + 1 + 1) = (x + y) * S (k + 1) - x * y * S k := fun k => by
    rw [hS (k + 1), hS k]; ring
  have hT2 : ∀ k, T (k + 1 + 1) = (x' + y') * T (k + 1) - x' * y' * T k := fun k => by
    rw [hT (k + 1), hT k]; ring
  ext k
  rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one,
    PowerSeries.coeff_mk]
  rcases k with _ | _ | _ | _ | k
  · simp [UpperTheory.powerSeriesFirstDifferenceSeq, hS0, hT0]
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS2, hT2]
    ring

theorem UpperTheory.rankinSelberg_local_generating_series_identity :
    ∀ x y x' y' c : ℂ, (PowerSeries.mk fun k : ℕ => c ^ k * (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)) * (∑ i ∈ Finset.range (k + 1), (x') ^ i * (y') ^ (k - i))) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  intro x y x' y' c
  exact UpperTheory.product_four_geometric_series x y x' y' c
    (fun k => ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i))
    (fun k => ∑ i ∈ Finset.range (k + 1), x' ^ i * y' ^ (k - i))
    (by simp) (by simp) (UpperTheory.geometric_sum_recurrence x y) (UpperTheory.geometric_sum_recurrence x' y')
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.RealIdeleMulAbsContinuousAndUnitAbsEqOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private noncomputable def cu (y : ℝ) (h : y ≠ 0) : (TR.Rinf ℚ)ˣ :=
  ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩

private theorem iy_eq {y : ℝ} (h : y ≠ 0) : iy y = TR.infId ℚ (cu y h) := dif_neg h

private theorem nrm_unit {v : H.P ℚ} {x : H.Kv v} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one :
    (∀ y y' : ℝ, y ≠ 0 → y' ≠ 0 → iy (y * y') = iy y * iy y') ∧ (∀ y : ℝ, y ≠ 0 → ab (iy y) = |y|) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) ∧ ∀ u ∈ UU, ab u = 1 := by
  refine ⟨fun y y' hy hy' => ?_, fun y hy => ?_, ?_, fun u hu => ?_⟩
  · rw [iy_eq (mul_ne_zero hy hy'), iy_eq hy, iy_eq hy', ← map_mul]
    congr 1
    exact Units.ext rfl
  · rw [iy_eq hy]
    show (IdeleGroup.ideleModule ℚ (TR.infId ℚ (cu y hy)) : ℝ) = |y|
    rw [GlobalTheory.HenQ.DetSplit.ideleModule_infId]
    simp [cu]
  · have hu : Continuous fun t : ℝ => cu (Real.exp t) (Real.exp_ne_zero t) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => Real.continuous_exp.inv₀ Real.exp_ne_zero
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (cu (Real.exp t) (Real.exp_ne_zero t)) :=
      funext fun t => iy_eq (Real.exp_ne_zero t)
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
  · show (IdeleGroup.ideleModule ℚ u : ℝ) = 1
    rw [IdeleGroup.ideleModule_eq]
    have h1 : ((u : A ℚ)).1 = 1 := hu.1
    have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖((u : A ℚ)).2 v‖ = 1 :=
      finprod_eq_one_of_forall_eq_one fun v => nrm_unit (hu.2 v)
    rw [h1, h2, mul_one]
    exact Finset.prod_eq_one fun w _ => by
      rw [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.RightInvariantBaseChangeUnipotentOfPlacesAboveFi
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma nL_memK {K : Type} [Field K] [NumberField K] {v : H.P K} {c : H.Kv v} (hc : Valued.v c ≤ 1) :
    H.nL c ∈ GlobalTheory.LFun.KGL v 2 := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : H.Kv v) ∈ v.adicCompletionIntegers K := one_mem _
  have h0 : (0 : H.Kv v) ∈ v.adicCompletionIntegers K := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

private lemma fix_sum {K : Type} [Field K] [NumberField K] (φ : GL (Fin 2) (A K) → ℂ) (S : Finset (H.P K)) :
    (∀ w ∈ S, H.Fix w φ) → ∀ z : A K, z.1 = 0 → (∀ w, w ∉ S → H.cp w z = 0) → (∀ w, Valued.v (H.cp w z) ≤ 1) →
      ∀ g, φ (g * gl (nU z)) = φ g := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ z h1 h2 _ g
    have hz : z = 0 := Prod.ext h1 (FiniteAdeleRing.ext K fun w => h2 w (Finset.notMem_empty w))
    have h : nU (0 : A K) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [nU]
    rw [hz, h, gl, map_one, mul_one]
  | insert w S hw ih =>
    intro hF z h1 h2 h3 g
    obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := H.sgLaws K w
    have hne : ∀ u, u ≠ w → H.cp u (H.sg w (H.cp w z)) = 0 := fun u hu => (hs _).2 u hu
    have e : z = (z - H.sg w (H.cp w z)) + H.sg w (H.cp w z) := (sub_add_cancel _ _).symm
    rw [e, nU_add, gl, map_mul, ← mul_assoc]
    have e2 : Matrix.SpecialLinearGroup.toGL (nU (H.sg w (H.cp w z))) = H.lc w (H.nL (H.cp w z)) :=
      ((H.lcLaws K w).1 _).symm
    rw [e2, hF w (Finset.mem_insert_self _ _) _ _ (nL_memK (h3 w))]
    refine ih (fun u hu => hF u (Finset.mem_insert_of_mem hu)) _ ?_ (fun u hu => ?_) (fun u => ?_) g
    · show z.1 - (H.sg w (H.cp w z)).1 = 0
      rw [h1, (hs _).1, sub_zero]
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self]
      · rw [hne u h, sub_zero]
        exact h2 u (by simp [h, hu])
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self, map_zero]
        exact zero_le'
      · rw [hne u h, sub_zero]
        exact h3 u

private lemma fin_over {E : Type} [Field E] [NumberField E] (v : H.P ℚ) :
    {w : H.P E | AdeleBaseChange.below ℚ w = v}.Finite := by
  have := v.isMaximal
  refine Set.Finite.of_finite_image (f := fun w : H.P E => w.asIdeal) ?_ fun a _ b _ h => HeightOneSpectrum.ext h
  refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, (AdeleBaseChange.below_eq_iff _ _).1 hw⟩

theorem UpperTheory.right_invariant_baseChangeUnipotent_of_places_above_fixed :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (v : H.P ℚ), H.Gd D.δ v → (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.Fix w φ) → ∀ c : H.Kv v, H.IsInt c → ∀ g, φ (g * Xg.nu D (H.sg v c)) = φ g := by
  intro E _ _ D φ v hG hF c hc g
  obtain ⟨-, -, hcp, -, -, -, -, hs, -, -⟩ := H.sgLaws ℚ v
  have hz : D.mkE 0 (H.sg v c) = AdeleBaseChange.adeleMap ℚ E (H.sg v c) * rt D.θ := by
    rw [Dat.mkE, map_zero, zero_add]
  have hoff : ∀ w : H.P E, AdeleBaseChange.below ℚ w ≠ v → H.cp w (D.mkE 0 (H.sg v c)) = 0 := fun w hw => by
    have h : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg v c)) = 0 := by
      change SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w ((H.sg v c).2 (AdeleBaseChange.below ℚ w)) = 0
      rw [(hs c).2 _ hw, map_zero]
    rw [hz, map_mul, h, zero_mul]
  change φ (g * gl (nU (D.mkE 0 (H.sg v c)))) = φ g
  refine fix_sum φ (fin_over (E := E) v).toFinset (fun w hw => hF w ((fin_over v).mem_toFinset.1 hw)) _ ?_
    (fun w hw => hoff w fun h => hw ((fin_over v).mem_toFinset.2 h)) (fun w => ?_) g
  · rw [hz]
    change InfinitePlace.infiniteAdeleRingMap (H.sg v c).1 * _ = 0
    rw [(hs c).1, map_zero, zero_mul]
  · by_cases hw : AdeleBaseChange.below ℚ w = v
    · subst hw
      have hk : ∀ x : H.Kv (AdeleBaseChange.below ℚ w), Valued.v x ≤ 1 →
          Valued.v (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w x) ≤ 1 := fun x hx => by
        rw [SemiLocal.valued_completionMap]
        exact pow_le_one' hx _
      have h1 : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg _ c)) = SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w c :=
        congrArg (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w) (hcp c)
      have h2 : H.cp w (rt D.θ) ^ 2 =
          SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (D.δ : H.Kv (AdeleBaseChange.below ℚ w)) := by
        rw [← map_pow, ← map_pow, D.sq]
        have a := eq_ratCast (((H.cp w).comp (algebraMap E (A E))).comp (algebraMap ℚ E)) D.δ
        rw [map_ratCast]
        exact a
      have h3 : Valued.v (H.cp w (rt D.θ)) ≤ 1 := by
        have hd := hG.del
        rw [eq_ratCast] at hd
        have h := hk _ hd.le
        rw [← h2, map_pow] at h
        exact (pow_le_one_iff two_ne_zero).1 h
      rw [hz, map_mul, h1, map_mul]
      exact mul_le_one' (hk c hc) h3
    · rw [hoff w hw, map_zero]
      exact zero_le'
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.StandardAddCharNegArchimedeanRat
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.standardAddChar_neg_archimedean_rat :
    ∀ x : ℝ, ψ (-(TR.sInf ℚ fun _ => x)) = Complex.exp (2 * Real.pi * Complex.I * x) := by
  intro x
  have hu : Nonempty (InfinitePlace ℚ) := inferInstance
  obtain ⟨w⟩ := hu
  have huniq : ∀ v : InfinitePlace ℚ, v = w := fun v => Subsingleton.elim v w
  have hreal : InfinitePlace.IsReal w := IsTotallyReal.isReal w
  have h : adelicChar ℚ (TR.sInf ℚ fun _ => x) = Real.fourierChar (-x) := by
    have e : TR.sInf ℚ (fun _ => x) = infiniteAdeleInl (TR.infEq ℚ fun _ => x) := rfl
    rw [e, adelicChar_infiniteAdeleInl, Fintype.prod_eq_single w (fun v hv => absurd (huniq v) hv)]
    rw [infiniteAdelicChar_apply_of_isReal hreal]
    have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal (TR.infEq ℚ (fun _ => x) w) = x :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hreal).apply_symm_apply x
    rw [e2]
  have h2 : adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) = Real.fourierChar x := by
    rw [AddChar.map_neg_eq_inv, h, AddChar.map_neg_eq_inv, inv_inv]
  have h3 : ψ (-(TR.sInf ℚ fun _ => x)) = ((adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) : Circle) : ℂ) := rfl
  rw [h3, h2, Real.fourierChar_apply]
  congr 1
  push_cast
  ring
end

