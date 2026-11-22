import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenNearCover
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticOrbitOffBoundary
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_sub_eq_of_sameOrbit (A B : HermLine ι) (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (ho : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  have hP : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A.smul c z' hc, B.smul c z' hc, ← hab, Real.log_mul hP (A.pos z' hz').ne',
    Real.log_mul hP (B.pos z' hz').ne']
  ring

theorem exactLine_not_mem_mcPts_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz
  have h1 := hz.2 1 Submodule.mem_top
  simp at h1

theorem exactLine_basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (ho : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

end SlopeTestRemainingChoices

theorem log_fsHerm_add_ph_eq_potAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x₀ : FA.Re.R.X) (z₀ : (Σ k, ι k) → ℂ) (b : BM.Rb.X) (p : Ψ × Fin N) (hm : Matrix (Fin N) (Fin N) ℂ), b ∈ BM.O l \ bdry BM.s → SameOrbit (FA.Re.R.lift x₀ x₀) z₀ → SameOrbit (basePart M.blk z₀) (BM.Rb.lift b b) → M.ExactAt (BM.F l) p z₀ hm → IsBlockDiag j hm → hm.det ≠ 0 → Real.log ((fsHerm ι (M.dy p)).h z₀) + FA.S.ph (some p) (FA.Re.π x₀) = potAt BM l p b hm := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l x₀ z₀ b p hm hb hx hbase hex hbd hdet
  have hsymm : ∀ {K' : Type} {ι' : K' → Type} {u v : (Σ k, ι' k) → ℂ}, SameOrbit u v → SameOrbit v u := by
    intro K' ι' u v h
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k),
      funext fun q => (inv_mul_cancel_left₀ (hc q.1) (v q)).symm⟩
  have htrans : ∀ {K' : Type} {ι' : K' → Type} {u v w : (Σ k, ι' k) → ℂ},
      SameOrbit u v → SameOrbit v w → SameOrbit u w := by
    intro K' ι' u v w h h'
    obtain ⟨c, hc, rfl⟩ := h
    obtain ⟨e, he, rfl⟩ := h'
    exact ⟨fun k => c k * e k, fun k => mul_ne_zero (hc k) (he k),
      funext fun q => (mul_assoc _ _ _).symm⟩
  have hmemx : FA.Re.R.lift x₀ x₀ ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀)
  have hmem : z₀ ∈ mcPts (mCoordIdeal y) :=
    ReciprocityTheory.ChartRestriction.G.Geo.mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y) (hsymm hx) hmemx
  have hpr : FA.pr (FA.Re.π x₀) = b := by
    apply BM.Rb.inj
    · exact exactLine_not_mem_mcPts_top _
    · exact htrans (hsymm (FA.pr_eq x₀)) (htrans (exactLine_basePart_orbit M.blk hx) hbase)
  have hopen : FA.Re.π x₀ ∈ FA.S.open' := by
    show FA.Re.π x₀ ∈ (bdry FA.S.s)ᶜ
    rw [Set.mem_compl_iff]
    intro h
    apply hb.2
    have h' : FA.S.s (FA.Re.π x₀) (FA.Re.π x₀) = 0 := h
    simp only [FA.s_eq, hpr] at h'
    show BM.s b b = 0
    exact h'
  have hhom := FA.hom_eq p x₀ hopen
  rw [FA.ref_some p] at hhom
  have hz0 : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0 := hmem.1
  have hsub := log_h_sub_eq_of_sameOrbit (BM.hom p) (fsHerm ι (M.dy p)) (BM.hom_deg p) hz0 hx
  have hind := BM.induced l b hb p z₀ hmem hbase hex.1 hm hbd hdet
  have hval : valAt M.x ((BM.F l).υ p) (BM.Rb.lift b b) = valAt M.x ((BM.F l).υ p) (basePart M.blk z₀) :=
    valAt_eq_of_sameOrbit _ _ _ M.x _ _ _ (BM.Rb.mem b b (BM.Rb.mem_U b)) (hsymm hbase)
  unfold potAt upsLogAt upsVal
  by_cases hblk : M.blk p = none
  · have h1 := hind.2 hblk
    rw [if_pos hblk, hval]
    linarith
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hblk
    have h1 := hind.1 k hk (hex.2 k hk)
    rw [if_neg hblk, sub_zero]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackSecondStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyModelBaseMetricStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_model_base_metric : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ∃ (M : FlagModel (yFl Ψ N) Ψ N N) (BM : BaseMetric M 0), (∀ p, BM.hom p = yLineFl Ψ N p) ∧ (∀ p, fsHerm (FlIdx Ψ N) (M.dy p) = yLineFl Ψ N p) ∧ bdry BM.s = ∅ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flagModel_over_point | exact GlobalTheory.CompanionTheory.Ar.PB.flagModel_over_point | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flagModel_over_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionOpenStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_resolution_open : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, (∀ τ, IsBlockDiag j (pH keep h ε τ w) ∧ (pH keep h ε τ w).det ≠ 0) ∧ pBase M v (pPhi M F keep v bl h ε w) = bl (pB ε w) ∧ ∀ p k, keep p → M.blk p = some k → ∀ m : ι k, upV v (pPhi M F keep v bl h ε w) ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (bl (pB ε w)) * minorIJ (pH keep h ε p.1 w) I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionRegularStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_resolution_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => pPhi M F keep v bl h ε w p) (pD ε V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo.pPhi_holo | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo.pPhi_holo | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo.pPhi_holo <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianBundleQuotientDegreeBoundStatement
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_bundle_quotient_degree_bound : ∀ (g : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (r : ℕ) (ε : Fin r → E.carrier) (q : E.carrier →ₗ[𝓞 K] E'.carrier), Module.finrank (𝓞 K) E.carrier = g → LinearIndependent (𝓞 K) ε → LinearMap.ker q = Submodule.span (𝓞 K) (Set.range ε) → (∀ e' : E'.carrier, ∃ (a : 𝓞 K) (e : E.carrier), a ≠ 0 ∧ q e = a • e') → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2) → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ C * sqAt E σ x) → E'.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 K) E'.carrier + max (-E'.normDegree ⊤) 0) : ℝ) : EReal) → E.slopeMax ≤ ((C' * Real.log (2 + C' + max (-E.normDegree ⊤) 0) + C' : ℝ) : EReal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log | exact GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log | (intros; apply GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormulaStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_family_defect_formula : RatRStatement → ResBridgeStatement → GoodProjExistsStatement → AvoidStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (L : Fin e → HermLine ι) (A B : HermLine ι) (f g : MRing ι) (w : ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → IsLineIso P A.a B.a f g → IsDefectOn P (mcPts P) f g A B w → I P (e + 1) (Fin.snoc L A) - I P (e + 1) (Fin.snoc L B) = -mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt | exact GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionLocConstTrivial
section
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem intersection_locConst_trivial : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (B : HermLine ι) (Λ : (F →+* ℂ) → ℝ) (II : IntersectionSystem), IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → B.a = 0 → IsSmoothHerm B → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) → II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) = ∑ sg : F →+* ℂ, Real.log (Λ sg) * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hInt K _ ι _ Ω _ F _ _ _ y D L B Λ II hII hP hL hB0 hB hex hloc
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg => {z | LiesOver y sg z}
  have hSc : ∀ sg, IsClosed (S sg) := fun sg =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.isClosed_liesOver y sg
  have hSs : ∀ sg (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S sg →
      (fun p => t p.1 * z p) ∈ S sg :=
    fun _ t _ _ hz => GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.liesOver_smul hz t
  have hex' : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg, z ∈ S sg := hex
  have hR := (hII K ι).2.2 (mCoordIdeal y) D L B 1 0 hP hL hB (fun k => by simp [hB0])
    tele_one_homog (fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1))
  have hnum : II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) =
      ptsIntegral (mCoordIdeal y) (pot L) fun z => Real.log (B.h z) := by
    rw [hR]
    unfold recR
    rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
    unfold arInt
    have hl : logNorm B 1 = fun z => - Real.log (B.h z) := by
      funext z
      simp [logNorm, Real.log_inv]
    rw [hl, tele_ptsIntegral_neg, neg_neg]
    rfl
  have hw : ptsIntegral (mCoordIdeal y) (pot L) (fun z => Real.log (B.h z)) =
      ptsIntegral (mCoordIdeal y) (pot L)
        (fun z => ∑ s, Real.log (Λ s) * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    have hval : B.h z = Λ sg := (hloc z hz sg hsg).self_of_nhds
    rw [Finset.sum_eq_single sg]
    · rw [Set.indicator_of_mem (show z ∈ S sg from hsg), mul_one, hval]
    · intro s _ hs
      have hns : z ∉ S s := fun h => hs ((hex z hz).unique h hsg)
      rw [Set.indicator_of_notMem hns, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [hnum, hw]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt K ι _ D L (F →+* ℂ) S
    (fun s => Real.log (Λ s)) hP hL hSc hSs hex'

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCxVarOfMemMinimalPrimesCxIdeal
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

theorem isCxVar_of_mem_minimalPrimes_cxIdeal :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P (d + 1) →
    ∀ Q ∈ (cxIdeal P).minimalPrimes, IsCxVar Q d ∧
      Q.comap (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) = P := by
  classical
  intro K _ ι _ P d hP Q hQ
  obtain ⟨hK, ⟨hPp, hPm, hPr⟩, hPh, hdim⟩ := hP
  have hc : Q.comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) = P :=
    GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.comap_of_minimal P hPh Q hQ
  have hCm : IsMultiHomogIdeal (cxIdeal P) := by
    obtain ⟨T, hT, hPT⟩ := hPm
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [cxIdeal, hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun m hm k => ha m (support_map_subset _ _ hm) k⟩
  have hQm : IsMultiHomogIdeal Q :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.GenNearCover.isMultiHomogIdeal_of_mem_minimalPrimes hCm hQ
  have hQr : IsRelevant Q := fun k => by
    obtain ⟨i, hi⟩ := hPr k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hc, Ideal.mem_comap, MvPolynomial.map_X]
    exact hX
  have hP' : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [hPh] at this
    exact this
  obtain ⟨hQp, -, hQdim⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have hmapP : cxIdeal P =
      (ReciprocityTheory.AnForm.R.extQ P).map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [cxIdeal, GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.map_int_complex_eq, ← Ideal.map_map]
    rfl
  have hQ' := hQ
  rw [hmapP] at hQ'
  refine ⟨⟨hK, ⟨hQ.1.1, hQm, hQr⟩, ?_⟩, hc⟩
  rw [ReciprocityTheory.AnForm.R.BaseChangeC.ringKrullDim_of_mem_minimalPrimes_map _ Q hQ']
  rw [hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega] at hQdim
  exact GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.dim_cancel_one hQdim

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicQuotientStructureStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_quotient_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R₀.form I → ∃ (g' k : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (e : Fin k → Λ) (form' : Λ' →ₗ[ℤ] Λ' →ₗ[ℤ] ℤ) (π : Λ → Λ'), k + g' = g ∧ (∀ x', ∃ x, (∀ y ∈ I, R₀.form x y = 0) ∧ π x = x') ∧ ∀ R : RiemLat E g Λ, R.form = R₀.form → LinearIndependent ℂ (fun i => R.P (e i)) ∧ Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) ∧ ∀ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), Function.Surjective q → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → ∃ R' : RiemLat E g' Λ', R'.form = form' ∧ (∀ x, (∀ y ∈ I, R.form x y = 0) → R'.P (π x) = q (R.P x)) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemRealStructureStatement
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_system_real_structure : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ (f : HermLine ι), IsConjInvariantH f → ∀ (th : LocPot X), (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, Real.log (f.h (lift x y)) - th.φ x y = (G y).re) → ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.pot_conj_pluriharmonic | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.pot_conj_pluriharmonic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.pot_conj_pluriharmonic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicLiftRealisationStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_holomorphic_lift_realisation : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (a : σ) (e : ℕ) (V : Set (Fin e → ℂ)) (ΦY : (Fin e → ℂ) → S.X) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (z : Fin e → ℂ), Re.J = ⊤ → Re.deg = 1 → Re.br = ∅ → IsOpen V → z ∈ V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, ∀ x₀, Re.π x₀ = ΦY u → SameOrbit (Re.R.lift x₀ x₀) (zex u)) → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, (S.th a).φ (ΦY z) (ΦY z') = Real.log ((Re.ref a).h (zex z')) + (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family <;> assumption)
end

