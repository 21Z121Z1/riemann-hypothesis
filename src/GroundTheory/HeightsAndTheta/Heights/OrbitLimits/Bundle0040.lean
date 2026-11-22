import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphMetric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockMetric
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImportsAlt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ProjMaxRankMeetsPsi0.proof : ProjMaxRankMeetsPsi0.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB y hy
  obtain ⟨i, hi, j, hj, hrank⟩ := hy
  by_cases h0 : Ψ (segre (R.lift y.1 y.1)) 0 ≠ 0
  · exact ⟨y, mem_connectedComponent, ⟨i, hi, j, hj, hrank⟩, h0⟩
  rw [not_not] at h0
  have hi0 : i ≠ 0 := by rintro rfl; exact hi h0
  have hsx : (BV.chart j).symm (BV.chart j y) = y := (BV.chart j).left_inv hj
  have hu0 : BV.chart j y ∈ (BV.chart j).target := (BV.chart j).map_source hj
  have hc : ∀ l, AnalyticAt ℂ (fun u => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l)
      (BV.chart j y) := fun l => analyticAt_pi_iff.1 (ProjRegular.proj_analyticAt Ψ hB y hj) l
  have hiu : Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1)) i ≠ 0 := by rwa [hsx]
  set A : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun u l =>
    Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
      Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i with hAdef
  have hA : AnalyticAt ℂ A (BV.chart j y) := analyticAt_pi_iff.2 fun l => (hc l).div (hc i) hiu
  have hDi : ∀ᶠ u in 𝓝 (BV.chart j y), Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i ≠ 0 :=
    (hc i).continuousAt.eventually_ne hiu

  have hrk : ∀ᶠ u in 𝓝 (BV.chart j y),
      (n : Cardinal) ≤ (fderiv ℂ A u : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)).rank := by
    refine hA.fderiv.continuousAt.preimage_mem_nhds
      ((isOpen_setOfPred_nat_le_rank (𝕜 := ℂ) n).mem_nhds ?_)
    show (n : Cardinal) ≤ _
    rw [LinearMap.rank, ← Module.finrank_eq_rank, hrank]

  have hfr : ∃ᶠ u in 𝓝 (BV.chart j y), Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0 ≠ 0 := by
    intro hz
    have hz' : ∀ᶠ u in 𝓝 (BV.chart j y), Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0 = 0 :=
      hz.mono fun u hu => not_not.1 hu
    have hD := hA.differentiableAt.hasFDerivAt
    have hD0 : (ContinuousLinearMap.proj 0).comp (fderiv ℂ A (BV.chart j y)) = 0 :=
      (hasFDerivAt_pi'.1 hD 0).unique ((hasFDerivAt_const (0 : ℂ) _).congr_of_eventuallyEq
        (by filter_upwards [hz'] with u hu; simp [hAdef, hu]))
    have hDi' : (ContinuousLinearMap.proj i).comp (fderiv ℂ A (BV.chart j y)) = 0 :=
      (hasFDerivAt_pi'.1 hD i).unique ((hasFDerivAt_const (1 : ℂ) _).congr_of_eventuallyEq
        (by filter_upwards [hDi] with u hu; simp [hAdef, div_self hu]))
    let π : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := LinearMap.pi fun t => LinearMap.proj (![0, i] t)
    have hπ : LinearMap.range π = ⊤ := by
      refine LinearMap.range_eq_top.2 fun w => ⟨Pi.single 0 (w 0) + Pi.single i (w 1), ?_⟩
      funext t
      fin_cases t <;> simp [π, hi0, Ne.symm hi0]
    have hker := LinearMap.finrank_range_add_finrank_ker π
    rw [hπ, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hker
    have hle : LinearMap.range (fderiv ℂ A (BV.chart j y) : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) ≤
        LinearMap.ker π := by
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      funext t
      have e0 := DFunLike.congr_fun hD0 v
      have ei := DFunLike.congr_fun hDi' v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        zero_apply] at e0 ei
      fin_cases t <;> simp [π, e0, ei]
    have hmono := Submodule.finrank_mono hle
    rw [hrank] at hmono
    have : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
    have := i.isLt
    omega
  have hev : ∀ᶠ u in 𝓝 (BV.chart j y), u ∈ (BV.chart j).target ∧
      ((BV.chart j).symm u).1 ∈ R.U y.1 ∧
      Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i ≠ 0 ∧
      (n : Cardinal) ≤ (fderiv ℂ A u : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)).rank := by
    filter_upwards [(BV.chart j).open_target.mem_nhds hu0, (ProjRegular.lift_analyticAt hB y hj).2,
      hDi, hrk] with u h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨u, hu0', hub⟩ := (hfr.and_eventually (Metric.ball_mem_nhds _ hε)).exists
  obtain ⟨hut, huU, hui, hurk⟩ := hball u hub
  refine ⟨(BV.chart j).symm u, ?_, ⟨i, ?_, j, (BV.chart j).map_target hut, ?_⟩,
    (ProjRegular.proj_ne_zero_iff Ψ huU).2 hu0'⟩
  ·
    refine ((convex_ball _ _).isPreconnected.image _
      ((BV.chart j).continuousOn_symm.mono fun w hw => (hball w hw).1)).subset_connectedComponent
      ⟨_, Metric.mem_ball_self hε, hsx⟩ ⟨u, hub, rfl⟩
  · obtain ⟨c, hc0, hcq⟩ := ProjRegular.proj_segre_lift_eq Ψ huU
    rw [hcq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hc0 hui
  ·
    have hU' : ∀ᶠ w in 𝓝 u, ((BV.chart j).symm w).1 ∈ R.U ((BV.chart j).symm u).1 :=
      (continuous_subtype_val.continuousAt.comp ((BV.chart j).continuousAt_symm hut)).preimage_mem_nhds
        ((R.isOpen_U _).mem_nhds (R.mem_U _))
    have heq : (fun w l => Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm w).1)) l /
        Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm w).1)) i) =ᶠ[𝓝 u] A := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hub, hU'] with w hw hwU
      obtain ⟨c1, hc1, h1⟩ := ProjRegular.proj_segre_lift_eq Ψ (hball w hw).2.1
      obtain ⟨c2, hc2, h2⟩ := ProjRegular.proj_segre_lift_eq Ψ hwU
      have hb : Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm w).1)) =
          (c2⁻¹ * c1) • Ψ (segre (R.lift y.1 ((BV.chart j).symm w).1)) := by
        rw [mul_smul, ← h1, h2, smul_smul, inv_mul_cancel₀ hc2, one_smul]
      funext l
      simp only [hAdef, hb, Pi.smul_apply, smul_eq_mul]
      exact mul_div_mul_left _ _ (mul_ne_zero (inv_ne_zero hc2) hc1)
    rw [(BV.chart j).right_inv hut, heq.fderiv_eq]
    rw [LinearMap.rank, ← Module.finrank_eq_rank] at hurk
    exact le_antisymm ((LinearMap.finrank_range_le _).trans (by simp)) (by exact_mod_cast hurk)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphFactor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

set_option linter.unusedSectionVars false

namespace LiftGraphFactor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkNorm (w : (Σ k, ι k) → ℂ) (k : K) : ℝ := Real.sqrt (∑ i, ‖w ⟨k, i⟩‖ ^ 2)

theorem blkSq_pos {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (k : K) :
    0 < ∑ i, ‖w ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hw k
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
    (Finset.single_le_sum (f := fun i => ‖w ⟨k, i⟩‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))

theorem blkNorm_pos {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (k : K) : 0 < blkNorm w k :=
  Real.sqrt_pos.2 (blkSq_pos hw k)

theorem blkNorm_smul (c : K → ℂ) (w : (Σ k, ι k) → ℂ) (k : K) :
    blkNorm (fun p => c p.1 * w p) k = ‖c k‖ * blkNorm w k := by
  unfold blkNorm
  have : ∑ i, ‖c k * w ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖w ⟨k, i⟩‖ ^ 2 := by
    simp only [norm_mul, mul_pow, Finset.mul_sum]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem blkNorm_conj (w : (Σ k, ι k) → ℂ) (k : K) :
    blkNorm (fun p => (starRingEnd ℂ) (w p)) k = blkNorm w k := by
  simp [blkNorm]

def fsLineZ (n : K → ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι where
  a := n
  h w := ∏ k, blkNorm w k ^ n k
  pos w hw := Finset.prod_pos fun k _ => zpow_pos (blkNorm_pos hw k) _
  smul c w hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [blkNorm_smul, mul_zpow]

theorem contDiffAt_zpow_of_ne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    {N : WithTop ℕ∞} (hf : ContDiffAt ℝ N f x) (hx : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ N (fun y => f y ^ m) x := by
  cases m with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hx)

theorem isSmoothHerm_fsLineZ (n : K → ℤ) : IsSmoothHerm (fsLineZ (ι := ι) n) := by
  intro w hw
  refine ContDiffAt.contDiffWithinAt ?_
  show ContDiffAt ℝ _ (fun x => ∏ k, blkNorm x k ^ n k) w
  refine contDiffAt_prod (t := Finset.univ) (f := fun k x => blkNorm x k ^ n k) fun k _ => ?_
  refine contDiffAt_zpow_of_ne (f := fun x => blkNorm x k) ?_ (blkNorm_pos hw k).ne' (n k)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Σ k, ι k) → ℂ => ∑ i, ‖x ⟨k, i⟩‖ ^ 2) :=
    ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ _)
  exact hs.contDiffAt.sqrt (blkSq_pos hw k).ne'

theorem conj_fsLineZ (n : K → ℤ) : IsConjInvariantH (fsLineZ (ι := ι) n) := by
  intro w
  show ∏ k, blkNorm _ k ^ n k = ∏ k, blkNorm w k ^ n k
  simp only [blkNorm_conj]

end LiftGraphFactor

open LiftGraphFactor in

theorem LiftGraphFactor.proof (hExt : SectionNormSqExtension.Statement) : LiftGraphFactor.Statement := by
  intro K _ _ ι _ Ω _ y N a r v hv hgen
  classical
  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fsLineZ (a • N.a)
  have hA1 : ∀ j, v j ∈ chartLat y A.a 1 := hv
  have hgen' : KH.GeneratesOn y (fun k => ((1 : ℕ) : ℤ) * A.a k) v := by
    have e : (fun k => ((1 : ℕ) : ℤ) * A.a k) = a • N.a := by
      funext k
      simp [A, fsLineZ]
    rw [e]
    exact hgen
  obtain ⟨S, hSs, hSp, hSt, hSc, hSv, hSl⟩ :=
    hExt K ι Ω y A 1 r v (isSmoothHerm_fsLineZ _) (conj_fsLineZ _) hA1 hgen'
  let U0 : Set ((Σ k, ι k) → ℂ) := {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0}
  have hAs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h U0 := isSmoothHerm_fsLineZ _
  refine ⟨fun w => S w * A.h w ^ 2, hSs.mul (hAs.pow 2), fun w hw => mul_pos (hSp w hw) (pow_pos (A.pos w hw) 2),
    ?_, ?_, ?_, ?_⟩
  ·
    intro c w hc hw
    show S _ * A.h _ ^ 2 = _ * (S w * A.h w ^ 2)
    rw [hSt c w hc, A.smul c w hc]
    have hAa : A.a = a • N.a := rfl
    rw [hAa]
    ring
  ·
    intro w
    show S _ * A.h _ ^ 2 = S w * A.h w ^ 2
    rw [hSc w, conj_fsLineZ _ w]
  ·
    intro z hz j
    have hx := PowerBlockMetric.oldPart_mem hz
    obtain ⟨c, hc⟩ := PowerBlockMetric.graph_prop (A := A) (m := 1) hA1 hgen' hz
    have hvN : ∀ j, v j ∈ chartLat y N.a a := by
      intro j c' hc'
      have h := hv j c' hc'
      have e : ∀ k, -(((1 : ℕ) : ℤ) * (a • N.a) k) = -((a : ℤ) * N.a k) := fun k => by
        simp [Pi.smul_apply]
      simp only [e] at h
      exact h

    have key : ∀ j, secNormAt y N a (v j) (basePart₂ z) * N.h (basePart₂ z) ^ a =
        ‖PowerBlockMetric.val y A 1 (v j) (basePart₂ z)‖ * A.h (basePart₂ z) := by
      intro j
      obtain ⟨⟨g, h⟩, hr, hne⟩ := PowerBlockMetric.exists_rep_at (hA1 j) hx
      have hrN : PowerBlockMetric.IsRep y N.a a (v j) g h := by
        obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
        refine ⟨dg, dh, hg, hh, fun k => ?_, hy⟩
        rw [hd k]
        simp [A, fsLineZ, Pi.smul_apply]
      have eA := PowerBlockMetric.val_spec (hA1 j) hx hr
      have eN := PowerBlockMetric.val_spec (hvN j) hx hrN
      have hNp : 0 < N.h (basePart₂ z) := N.pos _ hx.1
      have hAp : 0 < A.h (basePart₂ z) := A.pos _ hx.1
      have e2 : PowerBlockMetric.val y N a (v j) (basePart₂ z) * (N.h (basePart₂ z) : ℂ) ^ a =
          PowerBlockMetric.val y A 1 (v j) (basePart₂ z) * (A.h (basePart₂ z) : ℂ) := by
        apply mul_right_cancel₀ hne
        have := eN.symm.trans eA
        simp only [pow_one] at this
        linear_combination this
      rw [PowerBlockMetric.secNormAt_eq (hvN j) hx]
      have := congrArg norm e2
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hNp.le,
        Real.norm_of_nonneg hAp.le] at this
      exact this
    have hS : S (basePart₂ z) = ∑ i, ‖PowerBlockMetric.val y A 1 (v i) (basePart₂ z)‖ ^ 2 := by
      rw [hSv _ hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PowerBlockMetric.secNormAt_eq (hA1 i) hx]
    have hN : ∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2 = ‖c‖ ^ 2 * S (basePart₂ z) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, norm_mul, mul_pow]
    have hSp' : 0 ≤ S (basePart₂ z) := (hSp _ hx.1).le
    have hAp : 0 < A.h (basePart₂ z) := A.pos _ hx.1
    rw [key j, hN, hc j, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul hSp', Real.sqrt_sq hAp.le, norm_mul]
    ring
  ·
    intro z hz ξ hξ
    have hx := PowerBlockMetric.oldPart_mem hz
    have hw : basePart₂ z ∈ U0 := hx.1
    have hU0o : IsOpen U0 := LiftGraphMetric.isOpen_allNZ
    have hUo : IsOpen {z : (Σ k, addIdx ι r k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := LiftGraphMetric.isOpen_allNZ
    have h2le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    have hoR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, addIdx ι r k) → ℂ => basePart₂ z) :=
      ((LiftGraphMetric.oldCLM (ι := ι) r).restrictScalars ℝ).contDiff
    have hSlog : ContDiffAt ℝ 2 (fun w => Real.log (S w)) (basePart₂ z) :=
      ((hSs.contDiffAt (hU0o.mem_nhds hw)).of_le h2le).log (hSp _ hw).ne'
    have hAlog : ContDiffAt ℝ 2 (fun w => Real.log (A.h w)) (basePart₂ z) :=
      ((hAs.contDiffAt (hU0o.mem_nhds hw)).of_le h2le).log (A.pos _ hw).ne'
    have hL1 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (∑ i : Fin r, ‖x ⟨none, i⟩‖ ^ 2)) z :=
      (PowerBlockMetric.contDiff_newSq.contDiffAt).log (PowerBlockMetric.newSq_pos hz.1).ne'
    have hL2 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (S (basePart₂ x))) z :=
      hSlog.comp z (hoR.contDiffAt.of_le h2le)
    have hL3 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (A.h (basePart₂ x))) z :=
      hAlog.comp z (hoR.contDiffAt.of_le h2le)
    have hcomp : ReciprocityTheory.AnForm.levi (fun x => Real.log (A.h (basePart₂ x))) z ξ =
        ReciprocityTheory.AnForm.levi (fun w => Real.log (A.h w)) (basePart₂ z) (basePart₂ ξ) := by
      have h := ReciprocityTheory.AnForm.levi_comp (φ := fun w => Real.log (A.h w))
        (τ := ⇑(LiftGraphMetric.oldCLM (ι := ι) r)) (z := z) ξ
        ((LiftGraphMetric.oldCLM (ι := ι) r).analyticAt z) hAlog
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hev : (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (S (basePart₂ x) * A.h (basePart₂ x) ^ 2)) =ᶠ[𝓝 z]
        fun x => Real.log (S (basePart₂ x)) + (2 : ℝ) * Real.log (A.h (basePart₂ x)) := by
      filter_upwards [hUo.mem_nhds hz.1] with x hx'
      have hw' : basePart₂ x ∈ U0 := fun k => hx' (some k)
      rw [Real.log_mul (hSp _ hw').ne' (pow_pos (A.pos _ hw') 2).ne', Real.log_pow]
      norm_num
    have hgraph := hSl z hz ξ hξ
    have hsplit : (fun z' : (Σ k, addIdx ι r k) → ℂ =>
        Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) =
        fun z' => (1 / 2 : ℝ) * Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) +
          (-1 / 2 : ℝ) * Real.log (S (basePart₂ z')) := by
      funext z'
      ring
    show ReciprocityTheory.AnForm.levi _ z ξ = ReciprocityTheory.AnForm.levi _ z ξ
    change ReciprocityTheory.AnForm.levi _ z ξ = (1 : ℕ) * ReciprocityTheory.AnForm.levi _ (basePart₂ z) (basePart₂ ξ) at hgraph
    rw [hsplit, ReciprocityTheory.AnForm.levi_add_smul (f := fun x : (Σ k, addIdx ι r k) → ℂ =>
        (1 / 2 : ℝ) * Real.log (∑ j, ‖x ⟨none, j⟩‖ ^ 2)) (-1 / 2 : ℝ) (contDiffAt_const.mul hL1) hL2 ξ,
      ] at hgraph
    have hhalf := LiftGraphMetric.levi_const_mul (1 / 2 : ℝ) hL1 ξ
    erw [hhalf] at hgraph
    rw [← hcomp] at hgraph
    rw [ReciprocityTheory.AnForm.levi_congr hev, ReciprocityTheory.AnForm.levi_add_smul (2 : ℝ) hL2 hL3 ξ]
    push_cast at hgraph
    linarith

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjFullRankMeetsRegular
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ProjFullRankMeetsRegular.of_found (hT : ProjRankTransfer.Statement)
    (hM : ProjMaxRankMeetsPsi0.Statement) (hR : ProjMaxRankRegular.Statement) :
    ProjFullRankMeetsRegular.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y, hyc, hy⟩ := hT K ι P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y', hyc', hy', h0⟩ := hM K ι P J n R Ψ V BV hH y hy
  refine ⟨y', ?_, hR K ι P J n R Ψ V BV hH y' hy' h0⟩
  rw [connectedComponent_eq hyc]
  exact hyc'

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjMaxRankRegular
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace ProjMaxRankRegular

theorem fderiv_ratios_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {κ τ : Type*}
    [Fintype κ] [Fintype τ] {F : E → κ → ℂ} {u : E} (hF : DifferentiableAt ℂ F u) (a : τ → κ)
    (b : κ) (hb : F u b ≠ 0) (v : E) (t : τ) :
    fderiv ℂ (fun w t => F w (a t) / F w b) u v t =
      (F u b * fderiv ℂ F u v (a t) - F u (a t) * fderiv ℂ F u v b) / F u b ^ 2 := by
  have hc : ∀ k, HasFDerivAt (fun w => F w k)
      ((ContinuousLinearMap.proj k).comp (fderiv ℂ F u)) u :=
    fun k => hasFDerivAt_pi'.1 hF.hasFDerivAt k
  have hq : ∀ t, HasFDerivAt (fun w => F w (a t) / F w b)
      (F u (a t) • (ContinuousLinearMap.toSpanSingleton ℂ (-(F u b ^ 2)⁻¹)).comp
          ((ContinuousLinearMap.proj b).comp (fderiv ℂ F u)) +
        (F u b)⁻¹ • (ContinuousLinearMap.proj (a t)).comp (fderiv ℂ F u)) u := by
    intro t
    have h := (hc (a t)).fun_mul ((hasFDerivAt_inv hb).comp u (hc b))
    simp only [Function.comp_def] at h
    simpa only [div_eq_mul_inv] using h
  rw [(hasFDerivAt_pi.2 hq).fderiv]
  simp
  field_simp
  ring

theorem proof : ProjMaxRankRegular.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB y hy h0
  obtain ⟨i, hi, j, hj, hrank⟩ := hy
  have hsx : (BV.chart j).symm (BV.chart j y) = y := (BV.chart j).left_inv hj
  have hFd : DifferentiableAt ℂ (fun u => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)))
      (BV.chart j y) := (ProjRegular.proj_analyticAt Ψ hB y hj).differentiableAt
  have hF0 : Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1)) 0 ≠ 0 := by
    rw [hsx]; exact h0
  have hFi : Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1)) i ≠ 0 := by
    rw [hsx]; exact hi

  have hkerA : LinearMap.ker (fderiv ℂ
      (fun u (l : Fin (n + 1)) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i) (BV.chart j y) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) = ⊥ := by
    have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℂ
      (fun u (l : Fin (n + 1)) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i) (BV.chart j y) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    rw [hrank, Module.finrank_fin_fun] at h
    exact Submodule.finrank_eq_zero.mp (by omega)

  have hG : (projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm =ᶠ[𝓝 (BV.chart j y)]
      fun u (l : Fin n) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) (Fin.succ l) /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0 := by
    filter_upwards [(ProjRegular.lift_analyticAt hB y hj).2] with u hu
    exact ProjRegular.projCoord_eq Ψ hu
  refine ⟨h0, fun k hk => ProjRegular.det_ne_zero_of_chart Ψ hB y h0 hk hj ?_⟩
  rw [hG.fderiv_eq]
  set F' := fderiv ℂ (fun u => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1))) (BV.chart j y)
  set Fu := Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1))
  have hker : LinearMap.ker (fderiv ℂ (fun u (l : Fin n) =>
      Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) (Fin.succ l) /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0) (BV.chart j y) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hv' : ∀ l : Fin n, Fu 0 * F' v l.succ = Fu l.succ * F' v 0 := by
      intro l
      have h := congrFun hv l
      simp only [ContinuousLinearMap.coe_coe, Pi.zero_apply] at h
      rw [fderiv_ratios_apply hFd Fin.succ 0 hF0] at h
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · linear_combination h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hF0
    have hall : ∀ m : Fin (n + 1), Fu 0 * F' v m = Fu m * F' v 0 :=
      Fin.cases (by ring) hv'
    have hA : v ∈ LinearMap.ker (fderiv ℂ
        (fun u (l : Fin (n + 1)) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
          Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i) (BV.chart j y) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) := by
      rw [LinearMap.mem_ker]
      funext m
      simp only [ContinuousLinearMap.coe_coe, Pi.zero_apply]
      rw [fderiv_ratios_apply hFd (fun l => l) i hFi]
      have h1 : Fu i * F' v m - Fu m * F' v i = 0 := by
        apply mul_left_cancel₀ hF0
        linear_combination Fu i * hall m - Fu m * hall i
      rw [h1, zero_div]
    rw [hkerA] at hA
    exact hA
  exact ((LinearMap.isUnit_iff_isUnit_det _).1
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 hker)).ne_zero

end ProjMaxRankRegular

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSemiPosMassFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot PBlk fsLine)

def PtsSemiPosMassFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (N j)) → (∀ j, Inter.IsSemiPosHerm (N j)) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) < ⊤

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotDens
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjPotDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → ∀ j, ∀ y ∈ (BV.chart j).target,
      0 ≤ locDens BV (fun _ => multiprojPot R V) j y ∧
        ((BV.chart j).symm y ∈ projFullRank R BV →
          0 < locDens BV (fun _ => multiprojPot R V) j y)

end GroundTheory.Heights₂.Heights.Targets
end
end

