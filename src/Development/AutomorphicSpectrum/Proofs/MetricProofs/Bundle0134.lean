import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0130
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0027
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem eval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {w : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : f ∈ mCoordIdeal w) : eval w (map (Int.castRingHom ℂ) f) = 0 := by
  have h : (mConeMap w : MRing ι →+* MvPolynomial K ℂ) f = 0 := RingHom.mem_ker.mp hf
  have key : ((MvPolynomial.eval (fun _ : K => (1 : ℂ))).comp (mConeMap w : MRing ι →+* MvPolynomial K ℂ) : MRing ι →+* ℂ)
      = (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMap]
    · intro p
      simp [mConeMap]
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at this
  rw [← this, h, map_zero]

theorem bvec_good : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt (BM.F l) (mCoordIdeal (FC.bvec BM l b)) ∧ (∀ k, FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1) ∧ SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift b b)) := BM.good l b hb
  have hne : ∀ k, BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k =>
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.chart_ne (hgood.1 k)
  have hbv : ∀ q, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b q
      = (BM.Rb.lift b b ⟨q.1, (BM.F l).c q.1⟩)⁻¹ * BM.Rb.lift b b q := fun q => by
    simp only [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec, div_eq_inv_mul]
  have horb : SameOrbit (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) (BM.Rb.lift b b) := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit
    exact ⟨fun k => (BM.Rb.lift b b ⟨k, (BM.F l).c k⟩)⁻¹, fun k => inv_ne_zero (hne k), funext hbv⟩
  have hideal : mCoordIdeal (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) = mCoordIdeal (BM.Rb.lift b b) :=
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit horb
  have hone : ∀ k, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbv]; exact inv_mul_cancel₀ (hne k)
  have hmem : BM.Rb.lift b b ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem b b (BM.Rb.mem_U b)
  have hpt : GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) := by
    simp only [mcPts, Set.mem_ofPred_eq]
    refine ⟨fun k => ⟨(BM.F l).c k, by rw [hone k]; exact one_ne_zero⟩, fun f hf => ?_⟩
    apply eval_eq_zero_of_mem_mCoordIdeal
    rw [hideal]
    exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hmem hf
  refine ⟨hpt, ?_, hone, horb⟩
  rw [hideal]
  exact hgood

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorizationStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_LU_factorization : ∀ (N j : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ G = L * U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartComponentsFiniteProjectionStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartComponents_finite_projection : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    ∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSheetSimpleNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open MeasureTheory CxInt CxComp

theorem cxSheetSimpleNull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) ∧
      ¬ cxSimple (conePts Q) Ψ w} = 0 := by
  intro K _ ι _ Q e Ψ hQ hΨ
  obtain ⟨d, hbd, hnull⟩ := cxGenericCount hQ Ψ hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (cxSimple_of_count hbd hgood.1 hgood.2 hw)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeight
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover

open GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isValueAt_of_orbit {y : (Σ k, ι k) → Ω} {s : Ω} {z z' : (Σ k, ι k) → ℂ} {v : ℂ}
    (ho : SameOrbit z' z) (hv : IsValueAt y s z v) : IsValueAt y s z' v := by
  obtain ⟨c, hc, rfl⟩ := ho
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  have hne : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, heq, ?_, ?_⟩
  · rw [eval_smul_homog h d hh c z]
    exact mul_ne_zero hne hz0
  · rw [eval_smul_homog h d hh c z, eval_smul_homog g d hg c z, mul_div_mul_left _ _ hne]

theorem valAt_eq_of_orbit {y : (Σ k, ι k) → Ω} {s : Ω} {z z' : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (hz' : z' ∈ mcPts (mCoordIdeal y)) (ho : SameOrbit z' z)
    (hs : ∃ v, IsValueAt y s z v) : valAt y s z' = valAt y s z := by
  obtain ⟨v, hv⟩ := hs
  rw [valAt_eq hz hv, valAt_eq hz' (isValueAt_of_orbit ho hv)]

end Val

section Points

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fstPt_mem {k₀ : K} {P' : Ideal (MRing fun o : Option K => ι (o.getD k₀))} {Q : Ideal (MRing ι)}
    (hI : imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) P' = Q)
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts P') : fstPt k₀ z ∈ mcPts Q := by
  subst hI
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (some k)
    exact ⟨i, hi⟩
  · have := hz.2 _ hf
    exact (CPts.eval_rename_block _ z f).symm.trans this

end Points

section Minors

variable {N j : ℕ}

theorem minorIJ_shear {C : Finset (Fin N)} {ca cb : Fin N} (t : ℂ) (h : cb ∉ C) :
    minorIJ (1 + Matrix.single cb ca t) C C = 1 := by
  have e : (1 + Matrix.single cb ca t).submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl) =
      (1 : Matrix (Fin N) (Fin N) ℂ).submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl) := by
    ext x y
    have hx : cb ≠ C.orderEmbOfFin rfl x := fun e => h (e ▸ Finset.orderEmbOfFin_mem _ _ _)
    simp [Matrix.add_apply, Matrix.single_apply, hx]
  have h1 := CPts.minorIJ_one (R := ℂ) C
  unfold minorIJ at h1 ⊢
  rw [dif_pos rfl] at h1 ⊢
  rw [e, h1]

theorem cb_notMem {a ca cb : Fin N} (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    cb ∉ stepCols N j a := by
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : (a : ℕ) + 1 ≤ j
  · simp only [lastCol, if_pos h] at hca
    rw [if_pos h]
    omega
  · simp only [lastCol, if_neg h] at hca
    rw [if_neg h]
    omega

end Minors

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem pluck_of_flag (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F)
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb))
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) {w : (Σ k, ι k) → ℂ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : IsBlockDiag j H) {A : ℂ}
    (hw : ∀ m : ι k, w ⟨k, m⟩ = A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ H I (stepCols N j p.2))
    {I : Finset (Fin N)} (hI : IsStepRows N j p.2 I) :
    pluck M F zb k w I = A * minorIJ H I (stepCols N j p.2) := by
  let val := CPts.regVal hzb
  let uA : (Σ k, ι k) → Finset (Fin N) → CPts.regRing M.x zb :=
    fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → CPts.regRing M.x zb :=
    fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * valAt M.x (F.u ⟨k, m⟩ I') zb = if I = I' then 1 else 0 :=
    fun I' hI' => by
      have e : ∑ m : ι k, vA I ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
        apply Subtype.ext
        have := hF.2.2.1 p k hp I I' hI hI'
        split_ifs at this ⊢ <;> simpa [uA, vA] using this
      have e' := congrArg val e
      rw [map_sum] at e'
      simp only [map_mul] at e'
      refine e'.trans ?_
      split_ifs <;> simp
  unfold pluck
  simp only [hw]
  calc ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb *
        (A * ∑ I', valAt M.x (F.u ⟨k, m⟩ I') zb * minorIJ H I' (stepCols N j p.2))
      = A * ∑ I', (∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * valAt M.x (F.u ⟨k, m⟩ I') zb) *
          minorIJ H I' (stepCols N j p.2) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => by ring
    _ = A * minorIJ H I (stepCols N j p.2) := by
        congr 1
        rw [Finset.sum_eq_single I]
        · rw [rel I hI, if_pos rfl, one_mul]
        · intro I' _ hne
          by_cases hs : IsStepRows N j p.2 I'
          · rw [rel I' hs, if_neg (Ne.symm hne), zero_mul]
          · rw [minorIJ_block_zero hH hs, mul_zero]
        · simp

theorem twMinor_of_flag (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F)
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb))
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) {w : (Σ k, ι k) → ℂ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : IsBlockDiag j H) {A : ℂ}
    (hw : ∀ m : ι k, w ⟨k, m⟩ = A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ H I (stepCols N j p.2))
    (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) :
    twMinor M F zb p.2 k g w J = A * minorIJ (g * H) J (stepCols N j p.2) := by
  unfold twMinor
  rw [minorIJ_mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun I hI => by
    rw [pluck_of_flag M hF hzb hG hp hH hw (Finset.mem_filter.1 hI).2]]
  refine (Finset.sum_congr rfl fun I _ => by ring).trans (Finset.sum_subset (Finset.filter_subset _ _) fun I _ hI => ?_)
  have hs : ¬ IsStepRows N j p.2 I := fun h => hI (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  rw [minorIJ_block_zero hH hs, mul_zero, mul_zero]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ z ∈ mcPts (wP M τ a k₀ ca cb), ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ z ∈ wO M Rb τ a k₀ ca cb F kb V r h := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb hb hba hblk hca hcb hA z hz
  obtain ⟨hW, -, -, hImg, -⟩ := GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hblk hca hcb hA
  obtain ⟨bs, fr, -⟩ := CPts.main K ι Φ y Ψ N j M
  have hz1 : fstPt k₀ z ∈ mcPts (mCoordIdeal y) := fstPt_mem hImg hz
  have hzb : baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) := bs _ hz1
  obtain ⟨F, hF, hG⟩ := fr _ hzb
  have hnon : Nonempty Rb.X := by
    obtain ⟨x, -⟩ := Rb.surj _ hzb fun h => by
      have := h.2 1 Submodule.mem_top
      simp at this
    exact ⟨x⟩
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.T.exists_continuous_orbit_section _ _ _ n Rb hnon
  have hx0 := hr1 _ hzb
  obtain ⟨kb, V, bl, hsrc, hV, hBC⟩ := GlobalTheory.T.exists_base_chart_at_good_point K ι Φ y Ψ N j M n Rb F (r (baseOf M k₀ z))
    (by rw [CovMap.mCoordIdeal_eq_of_sameOrbit hx0]; exact hG)
  obtain ⟨hblm, hblnorm, hblgood, hblorb⟩ := hBC.2.2.2.2 _ hV
  rw [(Rb.A.chart kb).left_inv hsrc] at hblorb
  generalize hzc : bl (Rb.A.chart kb (r (baseOf M k₀ z))) = zc at hblm hblnorm hblgood hblorb
  have horb : SameOrbit zc (baseOf M k₀ z) := orbit_trans (orbit_symm hblorb) hx0
  have hval : ∀ s, (∃ v, IsValueAt M.x s zc v) → valAt M.x s (baseOf M k₀ z) = valAt M.x s zc :=
    fun s hs => valAt_eq_of_orbit hblm hzb (orbit_symm horb) hs
  obtain ⟨c₀, hc₀, he⟩ := horb
  let c : Option K → ℂ := fun o => o.elim 1 fun k => if h : ∀ p, M.blk p ≠ some k then c₀ ⟨k, h⟩ else 1
  have hc : ∀ o, c o ≠ 0 := fun o => by
    rcases o with _ | k
    · exact one_ne_zero
    · by_cases h : ∀ p, M.blk p ≠ some k
      · simp only [c, Option.elim_some, dif_pos h]
        exact hc₀ _
      · simp only [c, Option.elim_some, dif_neg h]
        exact one_ne_zero
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => c p.1 * z p
  have hz' : z' ∈ mcPts (wP M τ a k₀ ca cb) := mcPts_smul hW.2.1.2.1 c hc hz
  have hbp : basePart M.blk (fstPt k₀ z') = zc := by
    rw [he]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    show c (some k) * z ⟨some k, m⟩ = c₀ ⟨k, hk⟩ * z ⟨some k, m⟩
    simp only [c, Option.elim_some, dif_pos hk]
  have hbp2 : basePart M.blk (sndPt k₀ z') = zc := by
    rw [← hbp]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have hne : k ≠ k₀ := fun e => hk (τ, a) (e ▸ hblk)
    show z' (v₁ k₀ ⟨k, m⟩) = z' (v₀ k₀ ⟨k, m⟩)
    rw [v₁_ne hne]
    rfl
  obtain ⟨h, t, H1, H2⟩ := (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hblk hca hcb hA F z' hF
    (hbp ▸ hblm) (hbp ▸ hblgood) (hbp ▸ hblnorm)).1 hz'
  have hh := H1.2.1
  refine ⟨F, kb, V, bl, r, h, ⟨hb, hba, hblk, hca, hcb, hA, hF, hBC, hr1, hr2, hh⟩, hz, hsrc, ?_, ?_, ?_⟩
  · rw [hzc] at *
    exact hV
  · intro p k hp
    obtain ⟨A, hA0, hA'⟩ := H1.2.2 p k hp
    have hk : c (some k) = 1 := by
      simp only [c, Option.elim_some]
      exact dif_neg fun e => e p hp
    have hw : ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ =
        A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h p.1) I (stepCols N j p.2) := fun m => by
      have e : fstPt k₀ z' ⟨k, m⟩ = fstPt k₀ z ⟨k, m⟩ := by
        show c (some k) * z ⟨some k, m⟩ = z ⟨some k, m⟩
        rw [hk, one_mul]
      rw [← e, hA' m, hbp]
      congr 1
      exact Finset.sum_congr rfl fun I _ => by
        rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    rw [twMinor_of_flag M hF hzb hG hp (hh p.1).1 hw, Matrix.nonsing_inv_mul _ (hh p.1).2.isUnit, CPts.minorIJ_one,
      mul_one]
    exact hA0
  · obtain ⟨A, hA0, hA'⟩ := H2.2.2 (τ, a) k₀ hblk
    have hbd := (H2.2.1 τ).1
    rw [Function.update_self] at hbd
    have hw : ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = A * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
        minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) := fun m => by
      have e : sndPt k₀ z' ⟨k₀, m⟩ = sndPt k₀ z ⟨k₀, m⟩ := by
        show z' (v₁ k₀ ⟨k₀, m⟩) = z (v₁ k₀ ⟨k₀, m⟩)
        rw [v₁_self]
        exact one_mul _
      rw [← e, hA' m, hbp2, show (τ, a).1 = τ from rfl, Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun I _ => by
        rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    have := twMinor_of_flag M hF hzb hG (p := (τ, a)) hblk hbd hw (h τ)⁻¹ (stepCols N j a)
    refine fun e0 => hA0 ?_
    rw [show (τ, a).2 = a from rfl] at this
    rw [this, Matrix.nonsing_inv_mul_cancel_left _ _ (hh τ).2.isUnit, minorIJ_shear t (cb_notMem hca hcb), mul_one] at e0
    exact e0

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartEighthStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_eighth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ContinuousOn (wRho M Rb τ k₀ ca cb F kb r h ε) (wO M Rb τ a k₀ ca cb F kb V r h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartThird
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem

theorem blockDiag_transvection {N j : ℕ} {ca cb : Fin N} (hc : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := fun x y hxy => by
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) x y = 0 := Matrix.one_apply_ne fun e => hxy (by rw [e])
  have h2 : Matrix.single cb ca t x y = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hxy hc.symm
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem det_transvection' {N : ℕ} {ca cb : Fin N} (hc : ca ≠ cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 :=
  Matrix.det_transvection_of_ne cb ca hc.symm t

theorem cols_same_block {N j : ℕ} {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hbj : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
  have := b.2
  have := cb.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, wPhi M F bl h ε k₀ τ ca cb w ∈ mcPts (wP M τ a k₀ ca cb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW w hw
  obtain ⟨-, hE⟩ := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW
  obtain ⟨hHB, hbase, hX⟩ := hE w hw
  obtain ⟨hb, hbj, hblk, hca, hcb, hvar, hF, hBC, -, -, -⟩ := hW
  obtain ⟨hmc, hnorm, hgood, -⟩ := hBC.2.2.2.2 (wB ε w) hw
  have hbase' : basePart M.blk (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) = bl (wB ε w) := hbase
  have hc : ca ≠ cb := fun e => by rw [e] at hcb; omega
  refine (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hbj hblk hca hcb hvar F
    (wPhi M F bl h ε k₀ τ ca cb w) hF (by rw [hbase']; exact hmc) (by rw [hbase']; exact hgood)
    (by rw [hbase']; exact hnorm)).2 ⟨fun τ' => wH h ε τ' w, wT ε w, ?_, ?_⟩
  · refine ⟨(hX τ a).1.1, hHB, fun p k hk => ⟨1, one_ne_zero, fun m => ?_⟩⟩
    rw [one_mul]
    exact (hX p.1 p.2).1.2 k hk m
  · refine ⟨(hX τ a).2.1, fun τ' => ?_, fun p k hk => ⟨1, one_ne_zero, fun m => ?_⟩⟩
    · by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        refine ⟨(hHB τ').1.mul (blockDiag_transvection (cols_same_block hb hbj hca hcb) _), ?_⟩
        rw [Matrix.det_mul, det_transvection' hc, mul_one]
        exact (hHB τ').2
      · rw [Function.update_of_ne e]
        exact hHB τ'
    · rw [one_mul]
      have hm := (hX p.1 p.2).2.2 k hk m
      by_cases e : p.1 = τ
      · rw [if_pos e] at hm
        rw [e, Function.update_self]
        rw [e] at hm
        exact hm
      · rw [if_neg e] at hm
        rw [Function.update_of_ne e]
        exact hm

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifthStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_fifth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ w ∈ mcPts (mCoordIdeal y), {O | ∃ z ∈ mcPts (mCoordIdeal y'), O = {z'' | SameOrbit z'' z} ∧ CovMap.IsImg Cv z w}.ncard = (GroundTheory.Heights₂.Heights.Inter.ptsOverPt (mCoordIdeal M'.x) Cv.v (basePart M.blk w)).ncard := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibreCount.fibre_count | exact GlobalTheory.CompanionTheory.Ar.PB.FibreCount.fibre_count | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibreCount.fibre_count <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeBoundStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_degree_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∃ O' : Set ((Σ k, ιk k) → ℂ), IsOpen O' ∧ pO M Rb keep v F kb V r h = O' ∩ mcPts (mCoordIdeal (y ∘ v)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn.main <;> assumption)
end

