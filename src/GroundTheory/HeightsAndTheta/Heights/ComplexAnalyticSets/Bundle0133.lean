import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0131
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0108
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0132
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0098
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveNormalisationFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveNormalisationFinite.proof (hN : FieldNumbers.NoetherIntegralClosureFinite.Statement.{0}) :
    CurveNormalisationFinite.Statement := by
  intro n I q hI
  have := isReduced_curveLocalRing I q hI
  exact finite_integralClosure_of_isReduced hN (algebraMap _ (curveLocalRing I q)) (curveLocalRing_eq_div I q)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.POrdFiniteNonZeroDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

variable {n : ℕ}

theorem isLocalRing_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    [Nontrivial (curveLocalRing I q)] : IsLocalRing (curveLocalRing I q) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))))) Ideal.Quotient.mk_surjective

theorem OrdFiniteNonZeroDivisor.proof : OrdFiniteNonZeroDivisor.Statement := by
  intro n I q f hrad hdim hord
  have : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing (curveLocalRing I q) := isLocalRing_curveLocalRing I q
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  rw [mem_nonZeroDivisors_iff_right]
  intro y hyx
  by_contra hy

  obtain ⟨p, hp, hyp⟩ : ∃ p ∈ minimalPrimes (curveLocalRing I q), y ∉ p := by
    have : y ∉ (⊥ : Ideal (curveLocalRing I q)).radical := by
      rintro ⟨k, hk⟩
      exact hy (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
    simpa [← Ideal.sInf_minimalPrimes, minimalPrimes] using this
  have hpP : p.IsPrime := hp.1.1
  have hxp := (hpP.mem_or_mem (hyx ▸ p.zero_mem)).resolve_left hyp

  have hpmax : ¬ p.IsMaximal := by
    intro hm
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := curveLocalRing I q)
    rw [← IsLocalRing.eq_maximalIdeal hm, Ideal.height_eq_zero_iff.mpr hp, hdim] at h1
    exact absurd h1 (by decide)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      (integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal (curveNormalisation I q))
    (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (algebraMap_curveNormalisation_injective I q)]; exact bot_le)
  obtain ⟨P, hPm, hQP⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  apply hord ⟨P, hPm⟩
  have : P.IsPrime := hPm.isPrime
  have hd : Disjoint (P.primeCompl : Set (curveNormalisation I q)) Q :=
    Set.disjoint_left.2 fun a ha haQ ↦ ha (hQP haQ)
  set Q' := Q.map (algebraMap (curveNormalisation I q) (Localization.AtPrime P)) with hQ'def
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q hQ hd
  have hQ'u : Q'.under _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ hQ hd
  have hle : Ideal.span {algebraMap (curveNormalisation I q) (Localization.AtPrime P)
      (algebraMap (curveLocalRing I q) (curveNormalisation I q)
        (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))} ≤ Q' := by
    rw [Ideal.span_singleton_le_iff_mem]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hQp] at hxp
    exact hxp

  change Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ Ideal.span {_}) = ⊤
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨-, hart⟩ := hne
  have : IsArtinian (Localization.AtPrime P) (Localization.AtPrime P ⧸ Q') :=
    isArtinian_of_surjective _ (Submodule.factor hle) (Submodule.factor_surjective hle)
  have : IsArtinianRing (Localization.AtPrime P ⧸ Q') := isArtinian_of_tower (Localization.AtPrime P) this
  have hQ'max : Q'.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hQeq : Q = P := by
    rw [← hQ'u, IsLocalRing.eq_maximalIdeal hQ'max, Localization.AtPrime.under_maximalIdeal]
  apply hpmax
  rw [← hQp]
  have : Q.IsMaximal := hQeq ▸ hPm
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLevelSet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace SliceLevelSet

def moll (k : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨((k : ℝ) + 1)⁻¹ / 2, ((k : ℝ) + 1)⁻¹, by positivity, by
    have : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    linarith⟩

theorem tendsto_moll_rOut : Tendsto (fun k => (moll k).rOut) atTop (𝓝 0) := by
  show Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0)
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa only [one_div] using this

def smooth (a : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  convolution ((moll k).normed volume) a (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem contDiff_smooth {a : ℝ → ℝ} (ha : Continuous a) (k : ℕ) : ContDiff ℝ ∞ (smooth a k) :=
  (moll k).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (moll k).contDiff_normed ha.locallyIntegrable

theorem hasCompactSupport_smooth {a : ℝ → ℝ} (has : HasCompactSupport a) (k : ℕ) :
    HasCompactSupport (smooth a k) :=
  (moll k).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) has

theorem smooth_nonneg {a : ℝ → ℝ} (ha0 : ∀ r, 0 ≤ a r) (k : ℕ) (r : ℝ) : 0 ≤ smooth a k r := by
  unfold smooth
  rw [convolution_def]
  exact integral_nonneg fun u => by
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact mul_nonneg ((moll k).nonneg_normed u) (ha0 _)

theorem integral_smooth {a : ℝ → ℝ} (ha : Continuous a) (has : HasCompactSupport a) (k : ℕ) :
    ∫ r, smooth a k r = ∫ r, a r := by
  unfold smooth
  rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
    ((moll k).continuous_normed.integrable_of_hasCompactSupport (moll k).hasCompactSupport_normed)
    (ha.integrable_of_hasCompactSupport has), (moll k).integral_normed]
  simp

theorem tendsto_smooth {a : ℝ → ℝ} (ha : Continuous a) (r : ℝ) :
    Tendsto (fun k => smooth a k r) atTop (𝓝 (a r)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous tendsto_moll_rOut ha r

theorem sheetSum_abs_nonneg {n d : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ sheetSum I A (fun x s => |F x s|) y := by
  unfold sheetSum
  refine finsum_nonneg fun x => finsum_nonneg fun _ => ?_
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

theorem fatou {n d : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hfin : ∀ y, (fibre I A y).Finite)
    (K : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → (Fin d → ℂ) → ℝ) (T : (Fin n → ℂ) → ℝ)
    (w : ℕ → ℝ → ℝ) (a : ℝ → ℝ) (hw : ∀ r, Tendsto (fun k => w k r) atTop (𝓝 (a r))) {C : ℝ} (hC : 0 ≤ C)
    (hint : ∀ k, Integrable (fun y => sheetSum I A (fun x s => |w k (T x) * K x s y|) y))
    (hle : ∀ k, (∫ y, sheetSum I A (fun x s => |w k (T x) * K x s y|) y) ≤ C) :
    Integrable (fun y => sheetSum I A (fun x s => |a (T x) * K x s y|) y) ∧
      (∫ y, sheetSum I A (fun x s => |a (T x) * K x s y|) y) ≤ C := by
  classical
  set S : ℕ → (Fin d → ℂ) → ℝ := fun k y => sheetSum I A (fun x s => |w k (T x) * K x s y|) y with hS
  set S' : (Fin d → ℂ) → ℝ := fun y => sheetSum I A (fun x s => |a (T x) * K x s y|) y with hS'
  have hlim : ∀ y, Tendsto (fun k => S k y) atTop (𝓝 (S' y)) := by
    intro y
    simp only [hS, hS', CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun x _ => ?_
    by_cases hx : ∃ s, IsSheetAt I A x s
    · simp only [dif_pos hx]
      exact ((hw _).mul_const _).abs
    · simp only [dif_neg hx]
      exact tendsto_const_nhds
  have hS0 : ∀ k y, 0 ≤ S k y := fun k y => sheetSum_abs_nonneg _ y
  have hS'0 : ∀ y, 0 ≤ S' y := fun y => sheetSum_abs_nonneg _ y
  have hmeas : AEStronglyMeasurable S' volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hint k).1) (ae_of_all _ hlim)
  have hlint : ∫⁻ y, ENNReal.ofReal (S' y) ≤ ENNReal.ofReal C := by
    calc ∫⁻ y, ENNReal.ofReal (S' y) = ∫⁻ y, liminf (fun k => ENNReal.ofReal (S k y)) atTop := by
          refine lintegral_congr fun y => ?_
          exact ((ENNReal.continuous_ofReal.tendsto _).comp (hlim y)).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ y, ENNReal.ofReal (S k y)) atTop :=
          lintegral_liminf_le' fun k => (hint k).1.aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal C := by
          refine liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall fun k => ?_))
          rw [← ofReal_integral_eq_lintegral_ofReal (hint k) (ae_of_all _ (hS0 k))]
          exact ENNReal.ofReal_le_ofReal (hle k)
  refine ⟨⟨hmeas, ?_⟩, ?_⟩
  · unfold HasFiniteIntegral
    calc ∫⁻ y, ‖S' y‖ₑ = ∫⁻ y, ENNReal.ofReal (S' y) :=
          lintegral_congr fun y => Real.enorm_eq_ofReal (hS'0 y)
      _ ≤ ENNReal.ofReal C := hlint
      _ < ⊤ := ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hS'0) hmeas]
    exact ENNReal.toReal_le_of_le_ofReal hC hlint

end SliceLevelSet

theorem SliceLevelSet.proof (h₁ : SliceLevelSetSmooth.Statement) : SliceLevelSet.Statement := by
  intro n e h W g ℓ A ψ hW hg hℓ hA hψ hψs
  set a : ℝ → ℝ := fun r => |ψ r| with ha_def
  have ha : Continuous a := hψ.abs
  have has : HasCompactSupport a := hψs.comp_left (g := fun r : ℝ => |r|) abs_zero
  have ha0 : ∀ r, 0 ≤ a r := fun r => abs_nonneg _
  have hM0 : 0 ≤ ∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
      (fun _ x => Real.log (h.dualNorm x)) y :=
    integral_nonneg fun y => SliceLevelSet.sheetSum_abs_nonneg _ y
  have hC : 0 ≤ (∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
      (fun _ x => Real.log (h.dualNorm x)) y) * ∫ r, a r :=
    mul_nonneg hM0 (integral_nonneg ha0)
  have hk := fun k => h₁ n e h W g ℓ A (SliceLevelSet.smooth a k) hW hg hℓ hA
    (SliceLevelSet.contDiff_smooth ha k) (SliceLevelSet.hasCompactSupport_smooth has k)
    (SliceLevelSet.smooth_nonneg ha0 k)
  have habs : ∀ k, ∫ r, |SliceLevelSet.smooth a k r| = ∫ r, a r := fun k => by
    rw [← SliceLevelSet.integral_smooth ha has k]
    exact integral_congr_ae (ae_of_all _ fun r => abs_of_nonneg (SliceLevelSet.smooth_nonneg ha0 k r))
  have key := SliceLevelSet.fatou (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA)
    (fun x s y => gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s)
      ((fun x => Real.log (h.dualNorm x)) ∘ s) ((fun x => Real.log (h.dualNorm x)) ∘ s) y)
    (fun x => Real.log (h.dualNorm x)) (SliceLevelSet.smooth a) a (SliceLevelSet.tendsto_smooth ha) hC
    (fun k => (hk k).1) (fun k => (habs k) ▸ (hk k).2)
  have hfun : ∀ (x : Fin n → ℂ) (c : ℝ), |a (Real.log (h.dualNorm x)) * c| = |ψ (Real.log (h.dualNorm x)) * c| :=
    fun x c => by simp only [ha_def, abs_mul, abs_abs]
  simp only [hfun] at key
  exact key

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarLelongMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

namespace LelongNumberMonotone

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem maDens_logDistSq_nonneg (x z : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (hzx : z ≠ x)
    (hs : IsSheetAt J A z s) :
    0 ≤ ReciprocityTheory.AnForm.maDens (fun _ : Fin (d + 1) => logDistSq x ∘ s) (A *ᵥ z) := by
  have han : AnalyticAt ℂ s (A *ᵥ z) := FormIntegralPositivity.analyticAt_sheet hs
  have hsz : s (A *ᵥ z) = z := by
    obtain ⟨U, -, -, -, h, -⟩ := hs
    exact h
  exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ =>
    RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)

theorem chartDens_annulus_nonneg (x : Fin n → ℂ) {r s : ℝ} (hr : 0 < r) (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1) (fun _ => logDistSq x) y := by
  unfold chartDens sheetSum
  refine finsum_nonneg fun z => finsum_nonneg fun hz => ?_
  split_ifs with h
  · beta_reduce
    by_cases hza : z ∈ euclBall x s \ euclBall x r
    · rw [Set.indicator_of_mem hza, one_mul]
      have := maDens_logDistSq_nonneg x z h.choose (ne_of_mem_euclBall_diff hr hza) h.choose_spec
      rwa [hz.2] at this
    · rw [Set.indicator_of_notMem hza, zero_mul]
  · exact le_rfl

end LelongNumberMonotone

open LelongNumberMonotone in

theorem VarLelongMono.proof (hA : VarLelongAnnulus.Statement) : VarLelongMono.Statement := by
  intro n d J A x r s hJ hdim hAf hr hrs
  have heq := hA n d J A x r s hJ hdim hAf hr hrs
  have hτ : 0 ≤ ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (fun _ => logDistSq x) y :=
    integral_nonneg fun y => chartDens_annulus_nonneg x hr y
  have hrs0 : 0 ≤ r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) :=
    mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (hr.le.trans hrs) _)
  have := mul_nonneg hrs0 hτ
  linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StReducedNormalisationPlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def ReducedNormalisationPlace.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (P : MaximalSpectrum (integralClosure R (FractionRing R))),
    ∃ p ∈ minimalPrimes R, ∀ (S : Type) [CommRing S] (φ : R →+* S),
      Function.Surjective φ → RingHom.ker φ = p →
        ∃ P' : MaximalSpectrum (integralClosure S (FractionRing S)), ∀ x : R,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (integralClosure R (FractionRing R)) (Localization.AtPrime P.asIdeal)
                (algebraMap R (integralClosure R (FractionRing R)) x)) =
            Ring.ord (Localization.AtPrime P'.asIdeal)
              (algebraMap (integralClosure S (FractionRing S)) (Localization.AtPrime P'.asIdeal)
                (algebraMap S (integralClosure S (FractionRing S)) (φ x)))

end

end GroundTheory.Heights₂.Heights
end

