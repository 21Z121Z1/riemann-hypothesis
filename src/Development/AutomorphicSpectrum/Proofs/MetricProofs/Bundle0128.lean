import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0027
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0124
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagMinorTrdeg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0119
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsNormFnLogNormSecDiagSec
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isNormFn_logNormSec_diagSec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ (b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsNormFn M τ a k₀ ca cb RW fun x => logNormSec (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) x + c := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL b hb hab hk hca hcb hW c
    x z₀ z₁ F h t h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hd : IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hno := GlobalTheory.T.flag_adjacent_twisted_resolution K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hd
  obtain ⟨-, -, hx, -, -, -, hu, hiff, hnorm⟩ := hL x
  have hψ : ψ x x (i₀ x) ≠ 0 := fun h0 => hno ((hiff x hx).1 h0)
  have hn := hnorm x hx hψ z₀ z₁ F h t hd
  have hne : ‖u x x * ψ x x (i₀ x)‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero (hu x hx) hψ)
  show Real.log (‖u x x * ψ x x (i₀ x)‖ *
    Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x x)) + c))) + c = _
  rw [Real.log_mul hne (Real.exp_ne_zero _), Real.log_exp, ← hn]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsWeightedHomogeneousOfIsMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open GoodChartModel Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (blkW weight_blkW segMono eval_segMono segMono_homog psiPoly eval_psiPoly psiPoly_homog
  comp_mul_homog diag_of_homog)

section Rel

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isWeightedHomogeneous_of_isMultiHomog [DecidableEq K] {s : MRingOver ℂ ι} {a : K → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : IsWeightedHomogeneous (blkW ι) s a := by
  intro d hd
  funext k
  rw [weight_blkW]
  exact hs d (mem_support_iff.2 hd) k

theorem cone_homog [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) :
    Q.IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  refine Ideal.homogeneous_span _ _ ?_
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_of_isMultiHomog ha)⟩

theorem cone_segre_rel {e : ℕ} {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    (i : (k : K) → ι k) :
    ∃ r : ℕ, 0 < r ∧ ∃ G : Fin (e + 1) → MvPolynomial ((k : K) → ι k) ℂ,
      (∀ j, (G j).totalDegree ≤ r - 1) ∧
      ∀ z ∈ conePts Q, segre z i ^ r = ∑ j, Ψ (segre z) j * eval (segre z) (G j) := by
  classical
  set I := Q ⊔ Ideal.span (Set.range (psiPoly Ψ)) with hI
  have hrad : segMono ι i ∈ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p :=
      fun _ => rfl
    rw [hae]
    by_contra h
    rw [eval_segMono, ReciprocityTheory.ChartRestriction.G.Geo.segre, ← ne_eq, Finset.prod_ne_zero_iff] at h
    have hxm : x ∈ conePts Q := ⟨fun k => ⟨i k, h k (Finset.mem_univ _)⟩, fun f hf => by
      have := hx _ (Ideal.mem_sup_left hf : f ∈ I)
      rwa [hae] at this⟩
    refine hΨ x hxm (funext fun j => ?_)
    have := hx _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩) : psiPoly Ψ j ∈ I)
    rwa [hae, eval_psiPoly] at this
  obtain ⟨r0, hr0⟩ := hrad
  have hmem : segMono ι i ^ (r0 + 1) ∈ I := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hr0
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hb
  let D : K → ℕ := fun _ => r0
  let comp := weightedHomogeneousComponent (R := ℂ) (blkW ι) (D + fun _ => 1)
  have hpow : IsWeightedHomogeneous (blkW ι) (segMono ι i ^ (r0 + 1)) (D + fun _ => 1) := by
    have := (segMono_homog (ι := ι) i).pow (r0 + 1)
    convert this using 1
    funext k; simp [D]
  have hcomp := congrArg comp hab
  rw [map_add, map_sum, weightedHomogeneousComponent_eq_self hpow] at hcomp
  simp only [comp, comp_mul_homog (psiPoly_homog Ψ _)] at hcomp
  have hcd : ∀ j, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ r0 ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z (weightedHomogeneousComponent (blkW ι) D (c j)) =
        eval (segre z) G :=
    fun j => diag_of_homog r0 (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose G hG hGz using hcd
  refine ⟨r0 + 1, Nat.succ_pos _, G, fun j => by simpa using hG j, fun z hz => ?_⟩
  have h0 := congrArg (eval z) hcomp
  rw [map_add, hz.2 _ (weightedHomogeneousComponent_mem_of_mem _ _ (cone_homog hP) ha _),
    zero_add, map_sum, map_pow, eval_segMono] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hGz, eval_psiPoly, mul_comm]

theorem cone_pow_mem {Q : Ideal (MRingOver ℂ ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : setChartIdeal (conePts Q) σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := cone_segre_rel hP Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine hJ ?_
    rw [setChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hz1, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    simp only [f, Gx, map_sub, map_add, map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      eval_linPoly, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    simp only [f, map_sub, map_add, map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

theorem cxChartModel {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} (hQ : CxInt.IsCxVar Q e) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ ∧
      ∀ J ∈ (setChartIdeal (conePts Q) σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) ∧ IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  obtain ⟨hK, ⟨hQp, hQh, -⟩, hdimQ⟩ := hQ
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQh
  refine ⟨chart_zeroSet hR σ Ψ, fun J hJ => ?_⟩
  have hdim := chart_dim hQp hR hdimQ σ Ψ hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := cone_pow_mem hR hΨ hJ.1.2 a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩

end Rel

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableFibreCountOfLocalDiffeo
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

section FibreMeas

variable {e : ℕ}

theorem fibSum_eq_sub_of_finite {O : Set (Fin e → ℂ)} {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (h : (Fin e → ℂ) → ℝ) (y : Fin e → ℂ) (hy : (O ∩ Q ⁻¹' {y}).Finite) :
    fibSum O Q (fun u => max (h u) 0) y - fibSum O Q (fun u => max (-h u) 0) y = fibSum O Q h y := by
  unfold fibSum
  rw [← finsum_mem_sub_distrib _ _ hy]
  refine finsum_mem_congr rfl fun u _ => ?_
  rw [← sub_div, max_zero_sub_max_neg_zero_eq_self]

theorem aemeasurable_fibSum_of_nonneg {O : Set (Fin e → ℂ)} (hO : IsOpen O)
    {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hh : ∀ u, 0 ≤ h u) (hm : Measurable h)
    (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) : AEMeasurable (fibSum O Q h) := by
  have h1 := (LintegralFibSum.lintegral_fibSum_open hO hQ hh
    (hm.comp measurable_subtype_coe) hfin).1
  refine h1.ennreal_toReal.congr (Eventually.of_forall fun y => ?_)
  exact ENNReal.toReal_ofReal (LintegralFibSum.fibSum_nonneg _ _ hh y)

theorem aestronglyMeasurable_fibSum {O : Set (Fin e → ℂ)} (hO : IsOpen O)
    {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hm : AEStronglyMeasurable h (volume.restrict O))
    (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) : AEStronglyMeasurable (fibSum O Q h) volume := by
  have hmm : Measurable (hm.mk h) := hm.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ u, u ∈ O → h u = hm.mk h u :=
    (ae_restrict_iff' hO.measurableSet).mp hm.ae_eq_mk
  have hnull : volume (O ∩ {u | h u ≠ hm.mk h u}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae)
    rintro u ⟨huO, hne⟩ hu
    exact hne (hu huO)
  have himg : volume (Q '' (O ∩ {u | h u ≠ hm.mk h u})) = 0 := by
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hnull
    intro u hu
    exact ((hQ u hu.1).1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  have hp : AEMeasurable (fibSum O Q fun u => max (hm.mk h u) 0) :=
    aemeasurable_fibSum_of_nonneg hO hQ (fun u => le_max_right _ _) (hmm.max measurable_const) hfin
  have hn : AEMeasurable (fibSum O Q fun u => max (-hm.mk h u) 0) :=
    aemeasurable_fibSum_of_nonneg hO hQ (fun u => le_max_right _ _) (hmm.neg.max measurable_const) hfin
  refine (hp.sub hn).aestronglyMeasurable.congr ?_
  filter_upwards [hfin, measure_eq_zero_iff_ae_notMem.mp himg] with y hy hyn
  show fibSum O Q (fun u => max (hm.mk h u) 0) y - fibSum O Q (fun u => max (-hm.mk h u) 0) y = _
  rw [fibSum_eq_sub_of_finite _ y hy]
  unfold fibSum
  refine finsum_mem_congr rfl fun u hu => ?_
  have : h u = hm.mk h u := by
    by_contra hne
    exact hyn ⟨u, ⟨hu.1, hne⟩, hu.2⟩
  rw [this]

end FibreMeas

theorem aestronglyMeasurable_fibreSum_pushDens : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → (∀ j, AEStronglyMeasurable (fun u => G ((A.chart j).symm u) * locDens A Φ j u) (volume.restrict (A.chart j).target)) → AEStronglyMeasurable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) volume := by
  intro e X _ _ _ A Φ q S G hS hq hfin hsm hG
  classical
  obtain ⟨Pt⟩ := existsPartition A
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    Pt.χ j ((A.chart j).symm u) * (G ((A.chart j).symm u) * locDens A Φ j u) with hhj
  have hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null
        (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1) (hS j)
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have hχc : ∀ j, ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
    intro j
    have := (Pt.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have hjm : ∀ j, AEStronglyMeasurable (hj j) (volume.restrict (goodT A q j)) := fun j =>
    (((hχc j).aestronglyMeasurable (A.chart j).open_target.measurableSet).mul (hG j)).mono_measure
      (Measure.restrict_mono (fun u hu => hu.1) le_rfl)
  have hsum := sum_fibSum_ae A q S hN hq hfin Pt hj (fun x => G x * pushDens A Φ q x) (by
    intro j x hx hxS
    have hd := locDens_div_jacN A Φ q S hq hsm j hx hxS
    simp only [hhj, (A.chart j).left_inv hx]
    rw [← hd]
    ring)
  exact (Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
    aestronglyMeasurable_fibSum (isOpen_goodT A q j) (fun u hu => hu.2) (hjm j) (hfinj j)).congr hsum

end GlobalTheory.CompanionTheory.Ar.Giv.Push
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshAddPshPotentialOnOpenStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_add_psh_potential_on_open : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : LocPot X) (f : X → ℝ) (Θ : LocPot X), IsOpen U → IsPotential A P → IsPotential A Θ → A.SmoothOn U f → IsPshOn A U (P + LocPot.ofFun f) → IsPsh A Θ → IsPshOn A U (P + LocPot.ofFun f + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | exact GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | (intros; apply GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.LowerBoundFree in

theorem hodgeFlagArith : HodgeFlagArith.Statement :=
  HodgeFlagArith.proof HodgeFlagNeZero.proof
    (HodgeFlagRatioTrdeg.proof HodgeFlagRatioFieldEq.full HodgeFlagMinorTrdeg.proof)

theorem pushDown :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
      GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := fun h =>
  GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.proof (GlobalTheory.T.generic_degree_of_arith_system h) GlobalTheory.CompanionTheory.Ar.Giv.ProjF.pfStep hodgeFlagArith

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyEventuallySmoothPshStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_family_eventually_smooth_psh : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A Θ → IsPosPot A Θ → IsPotential A th → IsRegFamily A Θ L s th ph phT C t₀ → ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.EvPsh.eventually_isPsh_add_pot | exact GlobalTheory.CompanionTheory.Ar.Giv.EvPsh.eventually_isPsh_add_pot | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.EvPsh.eventually_isPsh_add_pot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open MuRegSmooth TopNPoly in

theorem muReg_smooth_log : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ), S.IsTied → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg Hd S B t) ∧ (muReg Hd S B t).a = muTwDeg Hd B ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muReg Hd S B t).h z) = Real.log (S.ref.h z) + S.regWeight t (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B hS
  have hP : ProjSmoothAlong.Statement := ProjSmoothAlong.proof HoloInjDerivInj.proof GlobalTheory.T.local_orbit_chart_statement_holds
  have hVS : VertFactorSmooth.Statement := VertFactorSmooth.proof VertFactorPos.proof
  have hSB : ∀ p ∈ D.SB B, p ∈ D.S := fun p hp => (Finset.mem_filter.1 hp).1
  filter_upwards [regWeight_smooth S hS] with t ht
  have hPm : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  set F : ((Σ k, J k) → ℂ) → ℝ := fun z =>
    S.ref.h z * Real.exp (S.regWeight t (M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z with hFdef
  have hvpos : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ p ∈ D.SB B, 0 < D.vertFactor p z := fun z hz p hp =>
    VertFactorPos.proof II Ψ K J Ω W D p (hSB p hp) z hz
  have hpos : ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < F z := fun z hz =>
    mul_pos (mul_pos (S.ref.pos z hz.1) (Real.exp_pos _)) (Finset.prod_pos (hvpos z hz))
  have hhom : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ muTwDeg Hd B k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts (mCoordIdeal D.y) := mcPts_smul hPm c hc hz
    have hproj : M.proj (torusSmul c z) = M.proj z := ((M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ Hd.aMu k) * S.ref.h z := by
      rw [show torusSmul c z = fun p => c p.1 * z p from rfl, S.ref.smul c z hc, S.ref_deg]
      rfl
    have hvf : ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
        (∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k) * ∏ p ∈ D.SB B, D.vertFactor p z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp => (hVS II Ψ K J Ω W D p (hSB p hp)).1 z hz c hc
    simp only [hFdef]
    rw [href, hproj, hvf, muTwDeg, prod_norm_zpow_add_sum hc]
    ring
  have hsm : SmoothAlong (mcPts (mCoordIdeal D.y)) F :=
    smoothAlong_mul (smoothAlong_mul (smoothAlong_of_contDiffOn S.ref_smooth)
      (smoothAlong_exp (hP II Ψ K J Ω W D M _ ht)))
      (smoothAlong_prod _ fun p hp => (hVS II Ψ K J Ω W D p (hSB p hp)).2)
  obtain ⟨Z, hZa, hZs, hZh⟩ := HermExtend.proof K J (mCoordIdeal D.y) (muTwDeg Hd B) F hPm hpos hhom hsm
  have hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z =
      (hermOfFun J (muTwDeg Hd B) fun z => (S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z).h z := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
    have hw0 := orbitRep_blocks hz.1
    have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
      have h := mcPts_smul hPm (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
      convert h using 1
      funext p
      have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
      rw [hp, ← _root_.mul_assoc, inv_mul_cancel₀ (hc _), _root_.one_mul]
    have hG0 : 0 < S.ref.h (orbitRep z) * Real.exp (S.regWeight t (M.proj (orbitRep z))) :=
      mul_pos (S.ref.pos _ hw0) (Real.exp_pos _)
    have hreg : (S.regLine t).h (orbitRep z) =
        S.ref.h (orbitRep z) * Real.exp (S.regWeight t (M.proj (orbitRep z))) :=
      hermOfFun_h_orbitRep hz.1 hG0
    have hFw : (S.regLine t).h (orbitRep z) * ∏ p ∈ D.SB B, D.vertFactor p (orbitRep z) = F (orbitRep z) := by
      rw [hreg]
    rw [hZh z hz, hermOfFun_h_smul hc hzc hz.1 (by rw [hFw]; exact hpos _ hwP), hFw]
    conv_lhs => rw [hzc]
    exact hhom _ hwP c hc
  refine ⟨?_, smoothRep_a _ _, fun z hz => ?_⟩
  · unfold muReg
    exact smoothRep_smooth_of (Z := Z) hZa hZs hagree
  · have hmu : (muReg Hd S B t).h z = F z := by
      unfold muReg
      rw [smoothRep_h _ hz, ← hagree z hz, hZh z hz]
    have h1 : S.ref.h z ≠ 0 := (S.ref.pos z hz.1).ne'
    have h2 : ∏ p ∈ D.SB B, D.vertFactor p z ≠ 0 := (Finset.prod_pos (hvpos z hz)).ne'
    rw [hmu]
    simp only [hFdef]
    rw [Real.log_mul (mul_ne_zero h1 (Real.exp_pos _).ne') h2, Real.log_mul h1 (Real.exp_pos _).ne',
      Real.log_exp, Real.log_prod fun p hp => (hvpos z hz p hp).ne']

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformIntegrabilityStatementHoldsStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_integrability_statement_holds : UnifIntStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds <;> assumption)
end

