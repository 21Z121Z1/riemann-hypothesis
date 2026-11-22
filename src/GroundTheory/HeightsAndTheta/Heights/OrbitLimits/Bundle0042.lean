import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0039

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveChartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

def chartUnit (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * a k)

def chartIndexLog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : ℝ :=
  Real.log (genIndex (chartLat y a τ) (curveMul y (chartUnit y c a τ)))

def chartRadius (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (t : (Σ k, ι k) → ℂ) : ℝ :=
  A.h t / ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k

end Objects

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in
open Classical in

theorem sum_single_chart_apply (k' : K) (j : ι k') (b : ℕ) (k : K) :
    ∑ i, (Finsupp.single (⟨k', j⟩ : Σ k, ι k) b) ⟨k, i⟩ = if k' = k then b else 0 := by
  classical
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro he
    exact h (Sigma.mk.inj_iff.mp he).1

theorem isMultiHomog_curveChartMono (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (curveChartMono c d) d := by
  classical
  have h : curveChartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
    rw [curveChartMono, monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
  have hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d := by
    funext k
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_chart_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  have hm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial (ι := ι)
    (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)
  rw [hd] at hm
  exact hm

omit [∀ k, Fintype (ι k)] in

theorem aeval_curveChartMono (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (curveChartMono c d) = chartUnit y c (fun k => (d k : ℤ)) 1 := by
  simp [curveChartMono, chartUnit, map_prod]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ne_zero_of_X_notMem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  show X p ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

omit [∀ k, Fintype (ι k)] in

theorem curveChartMono_notMem {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    curveChartMono c d ∉ mCoordIdeal y := by
  intro h
  have h' : mConeMap y (curveChartMono c d) = 0 := h
  rw [curveChartMono, map_prod] at h'
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h'
  rw [map_pow, mConeMap, aeval_X] at hk
  exact mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _) (pow_eq_zero_iff'.mp hk).1

theorem exists_chart {y : (Σ k, ι k) → Ω} {n : ℕ} (hP : IsArithVar (mCoordIdeal y) n) :
    ∃ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal y) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hP.2.1.2.2
  exact ⟨c, hc, fun k => ne_zero_of_X_notMem (hc k)⟩

end Lemmas

section Examples

example (a : Unit → ℤ) (τ : ℕ) :
    chartUnit (fun _ : (Σ _ : Unit, Fin 1) => (1 : ℚ)) (fun _ => 0) a τ = 1 := by
  simp [chartUnit]

example : chartRadius (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine (ι := fun _ : Unit => Fin 1) (-1)) (fun _ => 0)
    (fun _ => 1) = Real.exp 1 := by
  simp [chartRadius, ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight]

example : curveChartMono (ι := fun _ : Unit => Fin 1) (fun _ => 0) (fun _ => 2) ≠ 0 := by
  simp [curveChartMono, X_ne_zero]

end Examples

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

theorem PF.of_found
    (hInt : PtsIntegrableStatement) (hIm : ImageArithStatement) (hFD : FibreDimStatement)
    (hCM : ContractMixedStatement) (hCMF : ContractMixedFieldStatement)
    (hRes : ResExistsStatement)
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι')
    (hPD : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjDegStatement F ι ι')
    (hMult : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι)
    (hDivPush : ArithmeticIntersectionDivisorPushforward.Statement) (hPullPush : pullbackPushforward_holds.Statement)
    (hPullCount : PullbackDegreeCount.Statement) (hFDZ : FibreDimensionZero.Statement)
    (hVDA : VerticalDegreeAfterAdjoining.Statement) (hFM : PFFibreMult.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFStatement := by
  have hRank : pointFormRank_holds.Statement := pointFormRank_holds.proof RatioAlgDep.proof
  have hP0 : PushforwardProjectivePoint.Statement :=
    PushforwardProjectivePoint.proof hIm (pointForm_holds.proof hRank pointFormEuler_holds.proof) (ProjectivePointVertical.proof hGeo hEU hPC)
  have hCyc : ArithmeticIntersectionCycle.Statement :=
    ArithmeticIntersectionCycle.proof (ArithmeticIntersectionHorizontal.proof divSuppArith hIm hP0)
      (ArithmeticIntersectionVertical.proof hGeo hEU hPC hPD (VerticalDegree.proof hFDZ ChartRankAdjoin.proof hVDA))
      hDivPush GenericPointExists.proof hEU
  have hAI3 : PushforwardArithIntersection.Statement :=
    PushforwardArithIntersection.proof arithVarZero (RatR.proof hInt) hCyc
      (ArithmeticIntersectionIntegral.proof hInt (IntersectionWithSection.proof hRes hPullPush hPullCount pullbackDensity_holds.proof))
  have hStep : PFStep.Statement :=
    PFStep.proof (PFSecRed.proof hMult hFD) (PFVert.proof hGeo hEU hCMF) (PFIntZero.proof hRank)
      PFHoriz.proof (PFFibreSum.proof hFD PFFibreBij.proof hFM) hIm hCM
  exact PushforwardProjLineFlag.proof hAI3 hStep

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftGraphPoints

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_scale {S : Type} [CommRing S] {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a)
    (t : K → S) (x z : (Σ k, ι k) → S) (hz : ∀ p, z p = t p.1 * x p) :
    aeval z g = (∏ k, t k ^ a k) * aeval x g := by
  obtain rfl : z = fun p => t p.1 * x p := funext hz
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (t p.1 * x p) ^ m p = (∏ k, t k ^ a k) * ∏ p, x p ^ m p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem eval_map_int {σ : Type} (z : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

def homogAt (c : ∀ k, ι k) (M : ℕ) (F : MRing ι) : MRing ι :=
  ∑ m ∈ F.support, monomial m (coeff m F) * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (M - ∑ i, m ⟨k, i⟩)

theorem homogAt_isMultiHomog (c : ∀ k, ι k) (M : ℕ) (F : MRing ι)
    (hM : ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M) : IsMultiHomog (homogAt c M F) (fun _ => M) := by
  classical
  intro m' hm' k
  obtain ⟨m, hm, hm'⟩ := Finset.mem_biUnion.mp (support_sum hm')
  have h := Inter.ThmIUnique.isMultiHomog_mul' (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial m (coeff m F))
    (Inter.ThmIUnique.isMultiHomog_coordMonomial c (fun k => M - ∑ i, m ⟨k, i⟩)) m' hm' k
  simp only [Pi.add_apply] at h
  have := hM m hm k
  show _ = M
  omega

theorem aeval_homogAt {S : Type} [CommRing S] (c : ∀ k, ι k) (M : ℕ) (F : MRing ι)
    (x : (Σ k, ι k) → S) (hx : ∀ k, x ⟨k, c k⟩ = 1) : aeval x (homogAt c M F) = aeval x F := by
  conv_rhs => rw [F.as_sum]
  simp only [homogAt, map_sum, map_mul, map_prod, map_pow, aeval_X, hx, one_pow, Finset.prod_const_one, mul_one]

theorem aeval_ratio_eq_zero {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ}
    (hw : w ∈ mcPts (mCoordIdeal y)) (c : ∀ k, ι k) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) {F : MRing ι} (hF : aeval (fun p => y p / y ⟨p.1, c p.1⟩) F = 0) :
    aeval (fun p => w p / w ⟨p.1, c p.1⟩) F = 0 := by
  classical
  set M := ∑ m ∈ F.support, ∑ p, m p
  have hM : ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M := by
    intro m hm k
    calc ∑ i, m ⟨k, i⟩ ≤ ∑ k, ∑ i, m ⟨k, i⟩ :=
          Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      _ = ∑ p, m p := (Fintype.sum_sigma _).symm
      _ ≤ M := Finset.single_le_sum (f := fun m : (Σ k, ι k) →₀ ℕ => ∑ p, m p) (fun _ _ => Nat.zero_le _) hm
  have hG := homogAt_isMultiHomog c M F hM
  have hyG : aeval y (homogAt c M F) = 0 := by
    rw [aeval_scale hG (fun k => y ⟨k, c k⟩) (fun p => y p / y ⟨p.1, c p.1⟩) y
      (fun p => by field_simp [hyc p.1]), aeval_homogAt c M F _ (fun k => div_self (hyc k)), hF, mul_zero]
  have hmem : homogAt c M F ∈ mCoordIdeal y := (BlockImageInverse.mem_mCoordIdeal_iff y hG).mpr hyG
  have hwG := hw.2 _ hmem
  rw [eval_map_int, aeval_scale hG (fun k => w ⟨k, c k⟩) (fun p => w p / w ⟨p.1, c p.1⟩) w
    (fun p => by field_simp [hwc p.1]), aeval_homogAt c M F _ (fun k => div_self (hwc k))] at hwG
  exact (mul_eq_zero.mp hwG).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hwc k))

end LiftGraphPoints

open LiftGraphPoints in

theorem LiftGraphPoints.proof : LiftGraphPoints.Statement := by
  classical
  intro K _ ι _ Ω _ y n r v hv hgen w hw
  choose c hwc using hw.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hwc k
    have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]
    simpa using hw.2 _ hX
  have hrange : chartRingZ y c = (aeval fun p => y p / y ⟨p.1, c p.1⟩).range := by
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  have hQ : ∀ j, ∃ Q : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) Q = v j * ∏ k, y ⟨k, c k⟩ ^ (-n k) := by
    intro j
    have h := hv j c hyc
    simp only [Nat.cast_one, one_mul] at h
    rw [hrange] at h
    exact (AlgHom.mem_range _).mp h
  choose Q hQ using hQ
  set σ : Fin r → ℂ := fun j => aeval (fun p => w p / w ⟨p.1, c p.1⟩) (Q j) with hσ
  refine ⟨addBlock w σ, ⟨fun k => ?_, fun f hf => ?_⟩, rfl⟩
  · cases k with
    | some k => exact ⟨c k, hwc k⟩
    | none =>
      obtain ⟨u, hu, hsum⟩ := hgen c hyc
      have hU : ∀ j, ∃ U : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) U = u j := fun j =>
        (AlgHom.mem_range _).mp (hrange ▸ hu j)
      choose U hU using hU
      by_contra hcon
      push Not at hcon
      have hF : aeval (fun p => y p / y ⟨p.1, c p.1⟩) (∑ j, U j * Q j - 1) = 0 := by
        simp only [map_sub, map_sum, map_mul, hU, hQ, map_one, hsum, sub_self]
      have h1 := aeval_ratio_eq_zero hw c hyc hwc hF
      have hσ0 : ∀ j, aeval (fun p => w p / w ⟨p.1, c p.1⟩) (Q j) = 0 := fun j => hcon j
      simp [hσ0] at h1
  · obtain ⟨S, hS, hspan⟩ := CoordinateConeArithVar.isMultiHomogIdeal (addBlock y v)
    rw [hspan] at hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha⟩ := hS g hg
      have hg0 : aeval (addBlock y v) g = 0 :=
        (BlockImageInverse.mem_mCoordIdeal_iff _ ha).mp (hspan ▸ Ideal.subset_span hg)
      have hP : (∏ k, y ⟨k, c k⟩ ^ (-n k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hyc k)
      have hY : ∀ o : Option K, (o.elim (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ fun k => y ⟨k, c k⟩) ≠ 0 := by
        intro o
        cases o with
        | none => exact inv_ne_zero hP
        | some k => exact hyc k
      rw [aeval_scale ha (fun o => o.elim (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ fun k => y ⟨k, c k⟩)
        (addBlock (fun p => y p / y ⟨p.1, c p.1⟩) fun j => aeval (fun p => y p / y ⟨p.1, c p.1⟩) (Q j)) _
        (by
          rintro ⟨o, i⟩
          cases o with
          | none =>
            exact (show ∀ j : Fin r, v j = (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ *
                aeval (fun p => y p / y ⟨p.1, c p.1⟩) (Q j) from fun j => by rw [hQ]; field_simp) i
          | some k =>
            show y ⟨k, i⟩ = y ⟨k, c k⟩ * (y ⟨k, i⟩ / y ⟨k, c k⟩)
            field_simp [hyc k])] at hg0
      have hg1 := (mul_eq_zero.mp hg0).resolve_left (Finset.prod_ne_zero_iff.mpr fun o _ => pow_ne_zero _ (hY o))
      have hsub : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (x : (Σ k, ι k) → T),
          aeval x (aeval (addBlock (fun p => (X p : MRing ι)) Q) g) =
            aeval (addBlock x fun j => aeval x (Q j)) g := by
        intro T _ _ x
        rw [comp_aeval_apply]
        have hfun : (fun q => aeval x (addBlock (fun p => (X p : MRing ι)) Q q)) =
            addBlock x fun j => aeval x (Q j) := by
          funext q
          obtain ⟨o, i⟩ := q
          cases o with
          | none => rfl
          | some k => exact aeval_X _ _
        rw [hfun]
      rw [← hsub] at hg1
      have h2 := aeval_ratio_eq_zero hw c hyc hwc hg1
      rw [hsub] at h2
      rw [eval_map_int, aeval_scale ha (fun o => o.elim 1 fun k => w ⟨k, c k⟩)
        (addBlock (fun p => w p / w ⟨p.1, c p.1⟩) σ) _
        (by
          rintro ⟨o, i⟩
          cases o with
          | none => exact (one_mul _).symm
          | some k =>
            show w ⟨k, i⟩ = w ⟨k, c k⟩ * (w ⟨k, i⟩ / w ⟨k, c k⟩)
            field_simp [hwc k]), h2, mul_zero]
    | zero => simp
    | add x₁ x₂ _ _ h₁ h₂ => simp [map_add, h₁, h₂]
    | smul a x _ hx => simp [smul_eq_mul, map_mul, hx]

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjPotDensVanish
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

theorem ProjPotDensVanish.proof : ProjPotDensVanish.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB hΨ j u hu hmax
  set x : V := (BV.chart j).symm u with hxdef
  have hx : x ∈ (BV.chart j).source := (BV.chart j).map_target hu
  have hxu : BV.chart j x = u := (BV.chart j).right_inv hu
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (hΨ x.1 x.2)
  set G : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun y => Ψ (segre (R.lift x.1 ((BV.chart j).symm y).1))
    with hG
  set τ : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun y l => G y l / G y i with hτ
  have hGa : AnalyticAt ℂ G u := by
    have h := ProjRegular.proj_analyticAt Ψ hB x hx
    rwa [hxu] at h
  have hc : ∀ l, AnalyticAt ℂ (fun y => G y l) u := fun l => analyticAt_pi_iff.1 hGa l
  have hGi : G u i ≠ 0 := hi
  have hτa : AnalyticAt ℂ τ u := AnalyticAt.pi fun l => (hc l).div (hc i) hGi
  have hrk : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ u).toLinearMap) < n := by
    refine lt_of_le_of_ne ((LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun ℂ).le) ?_
    intro h
    apply hmax
    refine ⟨i, hi, j, hx, ?_⟩
    rw [hxu]
    exact h

  let φ' : (Fin (n + 1) → ℂ) → ℝ := fun w => Real.log (∑ l, ‖w l‖ ^ 2)
  have hsum_pos : ∀ w : Fin (n + 1) → ℂ, w i = 1 → 0 < ∑ l, ‖w l‖ ^ 2 := fun w hw =>
    lt_of_lt_of_le (by rw [hw]; norm_num)
      (Finset.single_le_sum (f := fun l => ‖w l‖ ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i))
  have hτ1 : ∀ y, G y i ≠ 0 → τ y i = 1 := fun y hy => div_self hy
  have hφ' : ContDiffAt ℝ 2 φ' (τ u) :=
    ((ContDiff.sum fun l _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ l)).contDiffAt.log
      (hsum_pos _ (hτ1 u hGi)).ne')

  let g : (Fin n → ℂ) → ℂ := fun y => G y i ^ 2
  have hga : AnalyticAt ℂ g u := (hc i).pow 2
  have hg0 : g u ≠ 0 := pow_ne_zero 2 hGi
  have hev : ∀ᶠ y in 𝓝 u, G y i ≠ 0 := (hc i).continuousAt.eventually_ne hGi
  have hgerm : (fun y' => (projPot R Ψ V).φ ((BV.chart j).symm u) ((BV.chart j).symm y')) =ᶠ[𝓝 u]
      fun y => (φ' ∘ τ) y + Real.log ‖g y‖ := by
    filter_upwards [hev] with y hy
    show Real.log (∑ l, ‖G y l‖ ^ 2) = Real.log (∑ l, ‖τ y l‖ ^ 2) + Real.log ‖G y i ^ 2‖
    have hn : ‖G y i‖ ≠ 0 := norm_ne_zero_iff.2 hy
    have hs : ∑ l, ‖G y l‖ ^ 2 = ‖G y i‖ ^ 2 * ∑ l, ‖τ y l‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [τ, norm_div, div_pow]
      field_simp
    rw [hs, norm_pow, Real.log_mul (pow_ne_zero 2 hn) (hsum_pos _ (hτ1 y hy)).ne', add_comm]
  unfold locDens
  refine (maDens_congr_hessC _ (fun _ => φ' ∘ τ) u fun _ => ?_).trans
    (ReciprocityTheory.AnForm.maDens_comp_eq_zero_of_rank_lt (fun _ => φ') τ u hτa (fun _ => hφ') hrk)
  refine (hessC_congr_of_eventuallyEq hgerm).trans ?_
  exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ g u
    (hφ'.comp u (hτa.contDiffAt.restrict_scalars ℝ)) hga hg0

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRankTransfer
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ProjRankTransfer.locallyConnectedSpace {e : ℕ} {X : Type*} [TopologicalSpace X]
    (A : FinHolAtlas e X) : LocallyConnectedSpace X := by
  let _ : ChartedSpace (Fin e → ℂ) X :=
    { atlas := Set.range A.chart
      chartAt := fun x => A.chart (chartIdx A x)
      mem_chart_source := fun x => Classical.choose_spec (A.cover x)
      chart_mem_atlas := fun x => ⟨_, rfl⟩ }
  exact ChartedSpace.locallyConnectedSpace (Fin e → ℂ) X

theorem ProjRankTransfer.of_found (hEq : ProjPotMassEq.Statement) (hPos : ProjPotMassPos.Statement)
    (hVan : ProjPotDensVanish.Statement) : ProjRankTransfer.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  by_contra hno
  push Not at hno
  have := ProjRankTransfer.locallyConnectedSpace BV
  have hCo : IsOpen (connectedComponent x) := isOpen_connectedComponent
  have h1 := hEq K ι P J n R Ψ V BV hH hC hΨ _ ⟨isClosed_connectedComponent, hCo⟩
  have h2 := hPos K ι P J n R V BV hH hC _ hCo ⟨x, mem_connectedComponent, hx⟩
  have h3 : mInt BV (fun _ => projPot R Ψ V)
      ((connectedComponent x).indicator fun _ => (1 : ℝ)) = 0 := by
    unfold mInt
    split_ifs with hP
    · unfold integralWith
      refine Finset.sum_eq_zero fun j _ => setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      by_cases hm : (BV.chart j).symm u ∈ connectedComponent x
      · rw [hVan K ι P J n R Ψ V BV hH hΨ j u hu (hno _ hm), mul_zero]
      · rw [Set.indicator_of_notMem hm, mul_zero, zero_mul]
    · rfl
  linarith

end GroundTheory.Heights₂.Heights.Targets
end
end

