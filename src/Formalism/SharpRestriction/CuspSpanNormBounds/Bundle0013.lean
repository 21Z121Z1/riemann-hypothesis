import Formalism.SharpRestriction.CuspSpanNormBounds.StarVecMulDM
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0009
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
import Formalism.FlagUnipotentLattices.HeightThresholdInequalities
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0010
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.HermitianCurvature.BesselNonvanishingReduction

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BcWeightEqZeroOf
section
open MeasureTheory Matrix Finset
open scoped ContDiff

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def sBig (r : ℕ) (κ τ : ℝ) (p : (Fin r → ℂ) × ℂ) : (Fin r → ℂ) × ℂ :=
  (fun a => ((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * p.1 a, ((τ ^ 2 : ℝ) : ℂ) * p.2)

def sBigL (r : ℕ) (κ τ : ℝ) : ((Fin r → ℂ) × ℂ) →ₗ[ℝ] ((Fin r → ℂ) × ℂ) :=
  LinearMap.prodMap (LinearMap.pi fun a => ((tF r κ τ a.val ^ 2) • LinearMap.id) ∘ₗ LinearMap.proj a)
    ((τ ^ 2) • LinearMap.id)

theorem sBigL_apply (r : ℕ) (κ τ : ℝ) (p : (Fin r → ℂ) × ℂ) : sBigL r κ τ p = sBig r κ τ p := by
  ext a <;> simp [sBigL, sBig, Complex.real_smul]

def jacBig (r : ℕ) (κ τ : ℝ) : ℝ := (∏ a : Fin r, tF r κ τ a.val ^ 4) * τ ^ 4

def wBig (k r : ℕ) (κ τ : ℝ) : ℝ :=
  (∏ a : Fin r, (tF r κ τ a.val ^ 2) ^ (2 * (Mdim k r a - 2))) * (τ ^ 4) ^ (k - 1)

section Norm

variable {k r : ℕ} {κ τ : ℝ}

theorem det_sBigL : LinearMap.det (sBigL r κ τ) = jacBig r κ τ := by
  rw [sBigL, LinearMap.det_prodMap, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one, jacBig]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_; ring
  · ring

theorem jacBig_pos (hκ : 0 < κ) (hτ : 0 < τ) : 0 < jacBig r κ τ :=
  mul_pos (Finset.prod_pos fun a _ => pow_pos (tF_pos hκ hτ _) 4) (pow_pos hτ 4)

theorem wBig_pos (hκ : 0 < κ) (hτ : 0 < τ) : 0 < wBig k r κ τ :=
  mul_pos (Finset.prod_pos fun a _ => pow_pos (pow_pos (tF_pos hκ hτ _) 2) _) (pow_pos (pow_pos hτ 4) _)

theorem lintegral_sBig (hκ : 0 < κ) (hτ : 0 < τ) (G : (Fin r → ℂ) × ℂ → ENNReal) :
    ∫⁻ p, G p = ENNReal.ofReal (jacBig r κ τ) * ∫⁻ p, G (sBig r κ τ p) := by
  have hdet : LinearMap.det (sBigL r κ τ) ≠ 0 := by rw [det_sBigL]; exact (jacBig_pos hκ hτ).ne'
  let e : ((Fin r → ℂ) × ℂ) ≃ₗ[ℝ] ((Fin r → ℂ) × ℂ) := LinearMap.equivOfDetNeZero (sBigL r κ τ) hdet
  let eM : ((Fin r → ℂ) × ℂ) ≃ᵐ ((Fin r → ℂ) × ℂ) := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have : (volume : Measure ((Fin r → ℂ) × ℂ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
  have hmap : Measure.map eM (volume : Measure ((Fin r → ℂ) × ℂ)) =
      ENNReal.ofReal |(LinearMap.det (sBigL r κ τ))⁻¹| • volume := by
    rw [← Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet]
    rfl
  have h1 : ∫⁻ p, G (sBig r κ τ p) = ENNReal.ofReal |(jacBig r κ τ)⁻¹| * ∫⁻ p, G p := by
    have : (fun p => G (sBig r κ τ p)) = fun p => G (eM p) := by
      funext p; rw [← sBigL_apply]; rfl
    rw [this, ← lintegral_map_equiv, hmap, lintegral_smul_measure, det_sBigL, smul_eq_mul]
  rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul (jacBig_pos hκ hτ).le, abs_inv,
    abs_of_pos (jacBig_pos hκ hτ), mul_inv_cancel₀ (jacBig_pos hκ hτ).ne', ENNReal.ofReal_one, one_mul]

theorem bcWeight_sBig (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (p : (Fin r → ℂ) × ℂ) :
    bcWeight k r (τ ^ 2 * T) (τ ^ 2 * T') (sBig r κ τ p) = wBig k r κ τ * bcWeight k r T T' p := by
  have hn : Complex.normSq (((τ ^ 2 : ℝ) : ℂ) * p.2) = τ ^ 4 * Complex.normSq p.2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
  have h4 : 0 < τ ^ 4 := pow_pos hτ 4
  unfold bcWeight sBig
  simp only
  rw [hn]
  by_cases hc : T * T' ≤ Complex.normSq p.2
  · rw [if_pos (by nlinarith), if_pos hc]
    have hprod : ∏ a : Fin r, ‖((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * p.1 a‖ ^ (2 * (Mdim k r a - 2)) =
        (∏ a : Fin r, (tF r κ τ a.val ^ 2) ^ (2 * (Mdim k r a - 2))) *
          ∏ a : Fin r, ‖p.1 a‖ ^ (2 * (Mdim k r a - 2)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos (tF_pos hκ hτ _) 2), mul_pow]
    rw [hprod, show τ ^ 4 * Complex.normSq p.2 - τ ^ 2 * T * (τ ^ 2 * T') =
      τ ^ 4 * (Complex.normSq p.2 - T * T') by ring, mul_pow, wBig]
    ring
  · rw [if_neg (by intro h; apply hc; nlinarith), if_neg hc, mul_zero]

theorem hsNormSq_eq_sum {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum]; positivity

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (C : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (C • A) = ‖C‖ ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, mul_pow]

theorem bcWeight_eq_zero_of {T T' : ℝ} (hk : 2 ≤ k) (p : (Fin r → ℂ) × ℂ)
    (h : ¬ ((∀ a, p.1 a ≠ 0) ∧ T * T' < Complex.normSq p.2)) : bcWeight k r T T' p = 0 := by
  unfold bcWeight
  split_ifs with hc
  · rcases not_and_or.mp h with h1 | h1
    · push Not at h1
      obtain ⟨a, ha⟩ := h1
      have hpos : 2 * (Mdim k r a - 2) ≠ 0 := by unfold Mdim; omega
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha, norm_zero, zero_pow hpos]), zero_mul]
    · have : Complex.normSq p.2 = T * T' := le_antisymm (not_lt.mp h1) hc
      rw [this, sub_self, zero_pow (by omega), mul_zero]
  · rfl

theorem jNorm2_tr (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r)
    (e1 : Tz k r L₁.z = τ ^ 2 * Tz k r L.z) (e2 : Tz k r L₁.z' = τ ^ 2 * Tz k r L.z')
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (f₁ : Mx k r → (L₁.Wq →L[ℂ] L₁.Wp))
    (μsec μsec₁ : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (C : ℂ)
    (hk : 2 ≤ k)
    (hJ : ∀ p : (Fin r → ℂ) × ℂ, (∀ a, p.1 a ≠ 0) → Tz k r L.z * Tz k r L.z' < Complex.normSq p.2 →
      hsNormSq (L₁.J f₁ (bigCell k r (sBig r κ τ p).1 (μsec₁ (sBig r κ τ p).2))) =
        ‖C‖ ^ 2 * hsNormSq (L.J f (bigCell k r p.1 (μsec p.2)))) :
    jNorm2 L₁ f₁ μsec₁ = ENNReal.ofReal (jacBig r κ τ * wBig k r κ τ * ‖C‖ ^ 2) * jNorm2 L f μsec := by
  unfold jNorm2 jNormSq
  rw [e1, e2, lintegral_sBig hκ hτ]
  have hw := wBig_pos (k := k) (r := r) hκ hτ
  have hpt : ∀ p : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (τ ^ 2 * Tz k r L.z) (τ ^ 2 * Tz k r L.z') (sBig r κ τ p) *
        ‖Real.sqrt (hsNormSq (L₁.J f₁ (bigCell k r (sBig r κ τ p).1 (μsec₁ (sBig r κ τ p).2))))‖ ^ 2) =
      ENNReal.ofReal (wBig k r κ τ * ‖C‖ ^ 2) *
        ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
          ‖Real.sqrt (hsNormSq (L.J f (bigCell k r p.1 (μsec p.2))))‖ ^ 2) := by
    intro p
    by_cases hD : (∀ a, p.1 a ≠ 0) ∧ Tz k r L.z * Tz k r L.z' < Complex.normSq p.2
    swap
    · have h0 := bcWeight_eq_zero_of (T := Tz k r L.z) (T' := Tz k r L.z') hk p (by tauto)
      rw [bcWeight_sBig hκ hτ, h0]; simp
    rw [← ENNReal.ofReal_mul (by positivity), hJ p hD.1 hD.2, bcWeight_sBig hκ hτ,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      Real.sq_sqrt (mul_nonneg (sq_nonneg _) (hsNormSq_nonneg _)), Real.sq_sqrt (hsNormSq_nonneg _)]
    congr 1; ring
  beta_reduce
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul (jacBig_pos hκ hτ).le,
    mul_assoc (jacBig r κ τ)]

theorem wbPart_smul (z : Fin (2 * r + k + 1) → ℂ) (t : ℂ) : wbPart k r (t • z) = t • wbPart k r z := by
  funext j; rfl

def secTr (τ : ℝ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun ζ => μsec (ζ / ((τ ^ 2 : ℝ) : ℂ))

theorem secTr_sBig (hτ : 0 < τ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin r → ℂ) × ℂ) :
    secTr τ μsec (sBig r κ τ p).2 = μsec p.2 := by
  unfold secTr sBig
  have : ((τ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hτ 2).ne'
  simp only
  rw [mul_div_cancel_left₀ _ this]

theorem isSection_tr (hτ : 0 < τ) {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h : IsSection k r z z' μsec) : IsSection k r ((τ : ℂ) • z) ((τ : ℂ) • z') (secTr τ μsec) := by
  have h2 : ((τ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hτ 2).ne'
  have h4 : 0 < τ ^ 4 := pow_pos hτ 4
  have hns : ∀ ζ : ℂ, Complex.normSq (ζ / ((τ ^ 2 : ℝ) : ℂ)) = Complex.normSq ζ / τ ^ 4 := by
    intro ζ; rw [Complex.normSq_div, Complex.normSq_ofReal]; ring
  have hreg : ∀ ζ : ℂ, Tz k r ((τ : ℂ) • z) * Tz k r ((τ : ℂ) • z') < Complex.normSq ζ →
      Tz k r z * Tz k r z' < Complex.normSq (ζ / ((τ ^ 2 : ℝ) : ℂ)) := by
    intro ζ hζ
    rw [Tz_smul, Tz_smul] at hζ
    rw [hns, lt_div_iff₀ h4]; nlinarith
  refine ⟨fun i j => ?_, fun ζ hζ => ?_⟩
  · have hc : ContDiff ℝ ∞ (fun ζ : ℂ => ζ / ((τ ^ 2 : ℝ) : ℂ)) := by
      have : (fun ζ : ℂ => ζ / ((τ ^ 2 : ℝ) : ℂ)) = fun ζ => ((τ ^ 2)⁻¹ : ℝ) • ζ := by
        funext ζ; rw [Complex.real_smul, div_eq_inv_mul]; push_cast; ring
      rw [this]; exact contDiff_const_smul _
    exact (h.1 i j).comp hc.contDiffOn fun ζ hζ => hreg ζ hζ
  · obtain ⟨hu, hv⟩ := h.2 _ (hreg ζ hζ)
    refine ⟨hu, ?_⟩
    unfold secTr
    rw [wbPart_smul, wbPart_smul]
    unfold herm at hv ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, hv]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    field_simp
    push_cast; ring

end Norm

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeDeepQ
section
noncomputable section

namespace Formalism.MainNotions.BridgeDeepQ

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates
open Formalism.HermitianLatticeCounting.S7 (P0 b1 beP)

def dqRh (X : CData) (t : ℝ) : ℝ :=
  (X.I.n : ℝ) ^ 2 * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) * X.I.rd * (2 * t) ^ ((1 : ℝ) / (X.qq : ℝ)) / 4

def sobT (X : CData) (t volK : ℝ) : ℝ :=
  (6 * beP X.I.n (P0 X.I.n X.qq X.I.f + X.I.n ^ 2 * X.I.f) X.b) ^ (X.I.n ^ 2 * X.I.f) * Real.exp (X.I.f : ℝ) *
    (17 * Real.sqrt (X.I.n : ℝ) / t ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f) * X.Dc / volK

def KerDeep (X : CData) (S : CSize X) (volK : ℝ) : Prop :=
  ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
    |(X.kerD x).re| ≤ sobT X (S.tau1 x) volK ∧
      (dqRh X (S.tau1 x) ≤ Real.log 2 →
        |(X.kerD x).re| ≤ (∏ P ∈ Finset.range (P0 X.I.n X.qq X.I.f),
          (2 * dqRh X (S.tau1 x) * Real.sqrt (X.I.f : ℝ) * beP X.I.n P X.b)) ^ 2 * sobT X (S.tau1 x) volK)

def VolRatioK (X : CData) (volK Cv : ℝ) : Prop :=
  0 < volK ∧ X.I.vol X.μf X.fund / volK ≤ cn_Y X ^ (Cv * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))

def VolRatio (X : CData) (Cv : ℝ) : Prop := VolRatioK X (X.I.volKg X.μf X.g) Cv

def Comparison (X : CData) : Prop := 2 * Real.sqrt (X.I.n : ℝ) ≤ X.b ^ 2

theorem beP₂ {n : ℕ} {b : ℝ} (hn : 1 ≤ n) (hc : 2 * Real.sqrt (n : ℝ) ≤ b ^ 2) (P : ℕ) :
    beP n P b ≤ 3 * (n : ℝ) * (b ^ 2 + (P : ℝ) * n) := by
  unfold beP
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h32 : (n : ℝ) ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [h32]
  set s := Real.sqrt (n : ℝ)
  have hs1 : 1 ≤ s := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn1
  have hss : s * s = n := Real.mul_self_sqrt hn0.le
  have hsn : s ≤ n := by nlinarith
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have e1 : s * b ^ 2 ≤ n * b ^ 2 := mul_le_mul_of_nonneg_right hsn hb2
  have e2 : 3 / 2 * (n * s) ≤ 3 / 4 * (n * b ^ 2) := by nlinarith
  have hnn : (1 : ℝ) ≤ n * n := by nlinarith
  have e3 : 3 * (P : ℝ) ≤ 3 * (P * n * n) := by nlinarith [mul_le_mul_of_nonneg_left hnn hP]
  nlinarith

end Formalism.MainNotions.BridgeDeepQ

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeMainT
section
noncomputable section

namespace Formalism.MainNotions.S.MainBoundWithDegrees

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Formalism.MainNotions.UniformConstantsAndStatements ValuativeRel IsDedekindDomain NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def dStd (D : D7) (u : D.what₂.Word) : ℝ :=
  Formalism.HermitianLatticesTheory.mass (Cnt.stdH D.host.E D.R.k) (Cnt.stdLat D.host.E D.R.k) * gaG D *
    (∏ τ, vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (Tr D u ^ D.R.k - 1) ^ D.R.f

def DsStd (D : D7) : ℝ :=
  Formalism.HermitianLatticesTheory.mass (Cnt.stdH D.host.E D.R.r) (Cnt.stdLat D.host.E D.R.r) * LocalBesselAndTopKernel.idxRows D * ∏ τ, D.dsig τ

def mainBody (D : D7) (large₂ : SizeData₂ D) (C Ce : ℝ) (dd : D.what₂.Word → ℝ) (Ds : ℝ) : Prop :=
  ∀ u u' : D.what₂.Word,
    ∃ (cInf : ℝ) (constP : HeightOneSpectrum (𝓞 D.host.F) → ℝ)
      (dens : Cnt.GramM D → HeightOneSpectrum (𝓞 D.host.F) → ℝ),
      0 < cInf ∧ (∀ p, 0 < constP p) ∧ Multipliable constP ∧ 0 < ∏' p, constP p ∧
      (∀ Z p, |dens Z p - 1| ≤ C * (Ideal.absNorm p.asIdeal : ℝ) ^ (-((D.R.k : ℝ) - 2 * D.R.rS - 3))) ∧
      (∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
        ∀ what₂ : Finset (Cnt.LatV D), IsRowReps D F0 what₂ →
        ∀ Z : Cnt.GramM D, (∀ τ, 0 < Cnt.Gz D (Tr D u) (Tr D u') Z τ) →
          (∃ Λ ∈ what₂, ∃ F' : Cnt.FlagU D u', IsNormFrame D Λ (lf D F0) F' ∧ Lat.ZhatL (lf D F0) F' = Z) →
          Multipliable (dens Z) ∧
          nuTot D u u' F0 what₂ Z =
            ENNReal.ofReal (cInf * (∏' p, constP p) * (∏' p, dens Z p) *
              ∏ τ, Cnt.Gz D (Tr D u) (Tr D u') Z τ ^ ((D.R.k : ℝ) - 1))) ∧
      ∀ θ : ℝ, 0 < θ → ∀ W : D.what₂.Tau → LocW D.R.k D.R.rS, (∀ τ, GoodW D τ u u' θ (W τ)) →
        ∀ A : ∀ τ, LocS (W τ), (∀ τ, GoodS D (lamD D τ) (A τ)) → (∀ τ, (A τ).deg = D.dsig τ) →
        ∀ μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
          (∀ τ, IsSection D.R.k D.R.rS (W τ).z (W τ).z' (μsec τ)) →
          ENNReal.ofReal (gaG D * (cInf * ∏' p, constP p)) * ∏ τ, MMv D u u' (A τ) (μsec τ) ≤
            ENNReal.ofReal (θ ^ (2 * Fintype.card D.what₂.Tau) *
              large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * (Fintype.card D.what₂.Tau : ℝ)) *
              ((1 + eSum D Ce) * (dd u * dd u') / Ds))

def MainEstimateWithDegrees (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (C Ce : ℝ) (dd : D.what₂.Word → ℝ) (Ds : ℝ) : Prop :=
  Hyp D large₂ h → mainBody D large₂ C Ce dd Ds

def mainConclStd (D : D7) (large₂ : SizeData₂ D) (C Ce : ℝ) : Prop := mainBody D large₂ C Ce (dStd D) (DsStd D)

def MainT (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (C Ce : ℝ) : Prop :=
  cdScaleTie D → dsigTie D → LocalBesselAndTopKernel.FamilyMidVolume D → MainEstimateWithDegrees D large₂ h C Ce (dStd D) (DsStd D)

section Family

variable {eps : ℝ} (Fm : FamP eps)

def MainTF (g : Given) (C Ce : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => MainT (Fm.D x i) (Fm.L x i) (g.wth C' Cl) C Ce

end Family

def NuTotIndep (D : D7) (u u' : D.what₂.Word) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
    ∀ what₂ rows' : Finset (Cnt.LatV D), IsRowReps D F0 what₂ → IsRowReps D F0 rows' →
      ∀ Z : Cnt.GramM D, nuTot D u u' F0 what₂ Z = nuTot D u u' F0 rows' Z

end Formalism.MainNotions.S.MainBoundWithDegrees
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.BridgeCS3d

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

theorem dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    PI.UpqRep.dsigW (k := k) (r := r) σ w v = Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v := by
  induction w generalizing v with
  | nil => rfl
  | cons X w ih =>
    show PI.UpqRep.dsig (k := k) (r := r) σ X (PI.UpqRep.dsigW (k := k) (r := r) σ w v) =
      Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v)
    rw [ih]
    rfl

theorem isBesselMapSm_iff {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (l : H → Wp) :
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π l ↔
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π l := by
  simp only [PI.BesselMapUniq.IsBesselMapSm, Formalism.MainNotions.S.IsBesselMapSm, PI.BesselMapUniq.IsCWCont,
    Formalism.MainNotions.S.IsCWCont, dsigW_eq]
  exact Iff.rfl

def GapNearParameters (Cg0 : ℝ) : Prop :=
  ∀ (D : D7) (Ch Cg Cq : ℝ), Cg0 ≤ Cg → 1 ≤ Cq → ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ), NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ →
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast L.ε μ h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h

theorem c_ne_zero {D : D7} {Ch Cg Cq : ℝ} {L : LocBessel D.R.k D.R.rS} {lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ}
    {ka b κ : ℝ} (hN : NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ) : L.c ≠ 0 := by
  obtain ⟨hκ, hL, -, -⟩ := hN
  have hc : L.c = cOfDpsi (κ : ℂ) := hL.2.2.1
  have hka : 0 < ka := hL.2.2.2.2.2.1.2.2.2.1
  have hκ0 : κ ≠ 0 := by
    rcases hκ with h | h
    · rw [h]; exact one_ne_zero
    · rw [h]; exact hka.ne'
  rw [hc, cOfDpsi]
  have : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ0
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  simp [this, hI]

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.BridgeCS3d
end
end

