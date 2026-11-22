import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0130
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0132
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0020
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0111
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0133
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PRhoContinuous
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont

theorem continuous_upV {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Kk : Type} [Fintype Kk]
    {ιk : Kk → Type} [∀ k, Fintype (ιk k)] (v : (Σ k, ιk k) → (Σ k, ι k)) :
    Continuous (upV v) := by
  refine continuous_pi fun q => ?_
  by_cases hq : ∃ q', v q' = q
  · simp only [upV, dif_pos hq]
    exact continuous_apply _
  · simp only [upV, dif_neg hq]
    exact continuous_const

theorem pSgn_ne_zero {Ψ : Type} {N j : ℕ} (hj : j ≤ N) (keep : Ψ × Fin N → Prop) (q : PIdx j keep) :
    pSgn (stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2)) q.1.1.2.1 q.1.1.2.2 ≠ 0 := by
  obtain ⟨-, -, hb, ha, hc⟩ := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q hj
  have hX : IsLowerUni (pMat (j := j) keep (fun _ => (0 : ℂ)) q.1.1.1) := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · unfold pMat lowMat
      rw [dif_neg (fun h => lt_irrefl _ h.1), if_pos rfl]
    · unfold pMat lowMat
      rw [dif_neg (fun h => lt_asymm hab h.1), if_neg hab.ne]
  exact (GlobalTheory.T.minorIJ_lowerUni_swap N _ _ _ _ hX ha hb q.1.2.1 (hc fun _ => 0).2).2

section Flag

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ContinuousOn (pRho M Rb keep v F kb r h ε) (pO M Rb keep v F kb V r h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε H
  obtain ⟨hv, hcov, hF, hB, horb, hr, hh⟩ := H
  obtain ⟨hVo, hVt, -, -, hbl⟩ := hB
  have hbase : Set.MapsTo (pBase M v) (pO M Rb keep v F kb V r h) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    (GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hv hcov).1 z hz.1
  have cU : Continuous (upV v) := continuous_upV v
  have cB : Continuous (pBase M v) := continuous_pi fun q =>
    (continuous_apply (⟨q.1.1, q.2⟩ : Σ k, ι k)).comp cU
  have hgood : ∀ z ∈ pO M Rb keep v F kb V r h, M.GoodAt F (mCoordIdeal (pBase M v z)) := by
    intro z hz
    have h3 := (hbl _ hz.2.2.1).2.2
    rw [(Rb.A.chart kb).left_inv hz.2.1] at h3
    have e := orbit_trans (orbit_symm (horb _ (hbase hz))) h3.2
    rw [GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit e]
    exact h3.1
  intro z hz
  have hz₄ : ∀ p k, keep p → M.blk p = some k →
      twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0 := hz.2.2.2
  refine continuousWithinAt_pi.2 fun i => ?_
  rcases e : ε.symm i with l | q
  · simp only [pRho, e]
    have c2 : ContinuousWithinAt (r ∘ pBase M v) (pO M Rb keep v F kb V r h) z :=
      ContinuousWithinAt.comp (hr _ (hbase hz)) cB.continuousWithinAt hbase
    have c3 : ContinuousAt (fun x => Rb.A.chart kb x l) ((r ∘ pBase M v) z) :=
      (continuous_apply l).continuousAt.comp ((Rb.A.chart kb).continuousAt hz.2.1)
    exact ContinuousAt.comp_continuousWithinAt (g := fun x => Rb.A.chart kb x l) c3 c2
  · simp only [pRho, e]
    obtain ⟨hk, -, -, -, -⟩ := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q M.j_le
    have cT := fun (k : K) (J : Finset (Fin N)) => twMinor_continuousWithinAt M F cB.continuousWithinAt hbase
      (hbase hz) (hgood z hz) cU.continuousWithinAt (pStep j keep q.1.1.1 q.1.1.2.2) k (h q.1.1.1)⁻¹ J
    cases e' : M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) with
    | none =>
      simp only [pRead, e', Option.elim_none]
      exact continuousWithinAt_const
    | some k =>
      simp only [pRead, e', Option.elim_some]
      have hd := mul_ne_zero (pSgn_ne_zero M.j_le keep q) (hz₄ _ k hk e')
      exact ContinuousWithinAt.div (cT k _) (ContinuousWithinAt.mul continuousWithinAt_const (cT k _)) hd

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLine
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem stepWeight_exists : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) → ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (B : FinHolAtlas e R.X), (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) → IsPotential R.A (BM.L.pullback pr hp.1) → IsSection R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m (fun k => pr ⁻¹' BM.W k) → IsAdaptedAtlas R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → ∃ (ph : R.X → ℝ) (C₅ : ℝ), (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x → Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) ∧ (∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → ph x = ph x') ∧ IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ιk fun k => M.dy p (κ k))) ph C₅ ∧ IsGradBound B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) ph C₅ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM p Kk _ ιk _ κ v hb hr e R pr hp B h1 hpot hsec hsnc had
  have hyp : IsStepHyp M BM p κ v R pr := ⟨hb, hr, hp, h1⟩
  have hc := GlobalTheory.T.flag_gap_pullback_third K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp
  have hfs : IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) :=
    (GlobalTheory.T.log_resolution_fubini_study_positive Kk ιk _ e R).1 _ (GlobalTheory.T.fubini_study_metric_smooth Kk ιk _)
  have hnorm : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  have hsm := GlobalTheory.T.flag_gap_holomorphic_pullback_first K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hps := GlobalTheory.T.flag_gap_holomorphic_pullback_second K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.flag_gap_holomorphic_pullback_third K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hgr := GlobalTheory.T.flag_gap_holomorphic_pullback_fourth K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.singular_potential_log_growth_psh e R.X R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm _ (stepPh M BM p v R pr) C₁ hfs hsm hps hC₁
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.T.adapted_atlas_smooth_potential_local e R.X R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm had (stepPh M BM p v R pr) hsm hgr
  refine ⟨stepPh M BM p v R pr, max C₂ C₃, ?_, ?_, ?_, hC₃ _ (le_max_right _ _)⟩
  · intro x hx z hz hzv
    have := GlobalTheory.T.flag_gap_pullback_first K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x z (R.mem_U x) hx hz hzv
    rw [this, stepGap]
    ring
  · intro x x' hxx hk
    exact GlobalTheory.T.flag_gap_pullback_second K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x' hxx hk
  · obtain ⟨h1', h2', h3', h4'⟩ := hC₂
    refine ⟨h1', h2', h3', fun x hx => ?_⟩
    have hlog : 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
      apply Real.log_nonneg
      have := hnorm x
      have h2 := Real.add_one_le_exp (1 : ℝ)
      unfold rW
      linarith
    obtain ⟨ha, hb'⟩ := h4' x hx
    refine ⟨?_, hb'.trans (le_max_left _ _)⟩
    have : -max C₂ C₃ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) ≤
        -C₂ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) :=
      mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left _ _)) hlog
    exact this.trans ha

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SemipositiveLeviOfLogMetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semipositive_levi_of_log_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (A : HermLine J), IsSmoothHerm A → (∀ a, ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, 0 ≤ levi (fun t' => Real.log (A.h ((D.chart a).γ t'))) t v) → IsSemipositiveH (mCoordIdeal D.y) A := by
  first | exact @GlobalTheory.CompanionTheory.Relay.semipositive_levi_of_log_metric | exact GlobalTheory.CompanionTheory.Relay.semipositive_levi_of_log_metric | (intros; apply GlobalTheory.CompanionTheory.Relay.semipositive_levi_of_log_metric <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHoldsStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signed_convergence_statement_holds : ConvergenceSignedStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned | exact GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolution
section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isUnit_algebraMap_locRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (pt : Fin n → ℂ)
    (g : MvPolynomial (Fin n) ℂ) (hg : eval pt g ≠ 0) :
    IsUnit (algebraMap _ (ReciprocityTheory.AnForm.R.locRing I pt) g) := by
  have := (IsLocalization.map_units (ReciprocityTheory.AnForm.R.locPt pt)
    (⟨g, fun h => hg (RingHom.mem_ker.mp h)⟩ : (ReciprocityTheory.AnForm.R.ptIdeal pt).primeCompl)).map
    (algebraMap (ReciprocityTheory.AnForm.R.locPt pt) (ReciprocityTheory.AnForm.R.locRing I pt))
  rwa [← IsScalarTower.algebraMap_apply] at this

theorem not_mem_conePts_top (z : (Σ k, ι k) → ℂ) :
    z ∉ ReciprocityTheory.AnForm.R.conePts (⊤ : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :=
  fun hz => by simpa using hz.2 1 Submodule.mem_top

theorem exists_isEmbedded_of_algRes {P J : Ideal (MRing ι)} {e : ℕ} (hJ : IsMultiHomogIdeal J)
    (hJP : ¬ J ≤ P) (hPC : ∀ f : MRing ι, map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P)
    (R : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) (pC J) e)
    (hsurj : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), ∃ i, ∃ x ∈ R.src i,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q)) z)
    (hinj : ∀ i j, ∀ x ∈ R.src i, ∀ x' ∈ R.src j,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q))
        (fun q => eval (R.coord j x') (R.lift j q)) → x = x')
    (hinv : ∀ i, ∀ x ∈ R.src i, ∀ p : (k : K) → ι k, (∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0) →
      ∃ O : Set R.M, IsOpen O ∧ x ∈ O ∧ O ⊆ R.src i ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ)
        (F : Fin (R.amb i) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O,
          (∀ k, eval (R.coord i y) (R.lift i ⟨k, p k⟩) ≠ 0) ∧
          eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q ≠ 0 ∧
          ∀ l, R.coord i y l * eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q =
            eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) (F l)) :
    ∃ R' : AnLogRes P J e, IsEmbedded R'.A P R'.U R'.lift := by
  classical
  let R0 : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) ⊤ e :=
    { M := R.M
      n := R.n
      amb := R.amb
      ideal := R.ideal
      src := R.src
      isOpen_alt_bis := R.isOpen_alt_bis
      cover := R.cover
      coord := R.coord
      isEmbedding := R.isEmbedding
      image := R.image
      trans := R.trans
      regular := R.regular
      dim := R.dim
      lift := R.lift
      lift_one := R.lift_one
      lift_mem := R.lift_mem
      compat := R.compat
      surj := fun z hz _ => hsurj z hz
      inj := fun i j x hx x' hx' _ h => hinj i j x hx x' hx' h
      inv := fun i x hx _ p hp => hinv i x hx p hp
      bd := fun _ => ⊤
      le_bd := fun _ => le_top
      zero_bd := fun i x hx =>
        ⟨fun h => absurd (h 1 Submodule.mem_top) (by simp), fun h => absurd h (not_mem_conePts_top _)⟩
      rc := 0
      comp := Fin.elim0
      sncAt := fun i x hx =>
        { r := (R.sncAt i x hx).r
          J := ∅
          h := 1
          σ := fun _ => none
          σ_injOn := by simp
          σ_eq_none := by simp
          span_eq := (R.sncAt i x hx).span_eq
          eval_h := by simp
          mem_bd := Submodule.mem_top
          le_span := fun g _ => by simp }
      comp_eq := fun i x hx => ⟨R.src i, R.isOpen_alt_bis i, hx, subset_rfl, fun k => k.elim0⟩
      mult := fun f a hf hfP hz => ⟨Fin.elim0, fun i x hx =>
        ⟨_, isUnit_algebraMap_locRing _ _ _ (by
          rw [ReciprocityTheory.AnForm.R.eval_bind_one]
          intro h0
          exact not_mem_conePts_top _ (hz _ (R.lift_mem i x hx) h0)), by simp⟩⟩ }
  obtain ⟨A, hA⟩ := R0.exists_atlas
  have hA' : R.IsGoodAtlas A := hA
  choose idx hidx using R.cover
  let R' : AnLogRes P J e :=
    { homog := hJ
      nondeg := hJP
      X := R.M
      A := A
      U := fun x => R.src (idx x)
      isOpen_U := fun x => R.isOpen_alt_bis (idx x)
      mem_U := hidx
      lift := fun x y q => eval (R.coord (idx x) y) (R.lift (idx x) q)
      holo := fun x p => hA'.1 (idx x) (R.lift (idx x) p)
      mem := fun x y hy => by
        rw [mem_mcPts_iff_conePts_pC]
        exact R.lift_mem (idx x) y hy
      compat := fun x x' y hy => R.compat (idx x) (idx x') y hy
      surj := fun z hz _ => by
        rw [mem_mcPts_iff_conePts_pC] at hz
        obtain ⟨i, x, hx, hxz⟩ := hsurj z hz
        exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
      inj := fun x x' _ hxx => hinj (idx x) (idx x') x (hidx x) x' (hidx x') hxx
      immersion := fun x _ p hp j hj =>
        R0.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) (not_mem_conePts_top _) p hp j hj
      snc := fun f a hfP hf hz => by
        have hf' : ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) f) a :=
          fun m hm k => hf m (support_map_subset _ _ hm) k
        have hfP' : map (Int.castRingHom ℂ) f ∉ pC P := fun h => hfP (hPC f h)
        have hz' : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), eval z (map (Int.castRingHom ℂ) f) = 0 →
            z ∈ ReciprocityTheory.AnForm.R.conePts (pC J) := by
          intro z hz1 hz2
          rw [← mem_mcPts_iff_conePts_pC] at hz1 ⊢
          exact hz z hz1 hz2
        obtain ⟨m, hm⟩ := R.isSNC_pullback A hA' idx hidx (fun _ _ => 0) _ a hf' hfP' hz'
        exact ⟨R.rc, m, R.comp, hm⟩
      null := fun j => by
        refine MeasureTheory.measure_mono_null ?_ (R.volume_preimage_eq_zero A hA' j)
        rintro y ⟨hy1, hy2⟩
        refine ⟨hy1, idx _, hidx _, ?_⟩
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy2 ⊢
        rw [← mem_mcPts_iff_conePts_pC]
        exact hy2 }
  refine ⟨R', ?_⟩
  exact
    { isOpen := fun x => R.isOpen_alt_bis (idx x)
      mem_U := hidx
      holo := fun x p => hA'.1 (idx x) (R.lift (idx x) p)
      mem := R'.mem
      compat := R'.compat
      surj := fun z hz => by
        rw [mem_mcPts_iff_conePts_pC] at hz
        obtain ⟨i, x, hx, hxz⟩ := hsurj z hz
        exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
      inj := fun x x' hxx => hinj (idx x) (idx x') x (hidx x) x' (hidx x') hxx
      immersion := fun x p hp j hj =>
        R0.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) (not_mem_conePts_top _) p hp j hj }

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
  GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem isEmbedded_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∃ R : AnLogRes (mCoordIdeal y) J e, IsEmbedded R.A (mCoordIdeal y) R.U R.lift := by
  intro K _ ι _ Ω _ _ y e J hP hJ hJP hsnc
  classical
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hP.2.1.2.1
  have hDh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC J) := isMultiHomogIdeal_pC hJ
  obtain ⟨hcpt, hsrc⟩ := GlobalTheory.T.snc_resolution_compact_embedded K ι _ hPh
  obtain ⟨himage, htrans⟩ := GlobalTheory.T.snc_resolution_transition_polynomial K ι _ hPh
  obtain ⟨hcover, hliftmem, hcompat, hsurj, hinj, hzero⟩ := GlobalTheory.T.snc_resolution_cover_and_cone K ι _ _ hPh hDh
  have hinv := GlobalTheory.T.snc_resolution_local_chart_polynomial K ι _ hPh
  have hreg := GlobalTheory.T.snc_resolution_regular_local_ring K ι Ω y e J hP hsnc
  have hsc := GlobalTheory.T.snc_resolution_boundary_normal_crossing K ι Ω y e J hP hJ hJP hsnc
  let E := Fintype.equivFin ((k : K) → ι k)
  let R : ReciprocityTheory.AnForm.R.AlgRes ι (pC (mCoordIdeal y)) (pC J) e :=
    { M := Pts (pC (mCoordIdeal y))
      compact := hcpt
      n := Fintype.card ((k : K) → ι k)
      amb := fun _ => Fintype.card (Σ k, ι k)
      ideal := fun i => ideal _ (E.symm i)
      src := fun i => src _ (E.symm i)
      isOpen_alt_bis := fun i => (hsrc _).1
      cover := fun x => by
        obtain ⟨p, hp⟩ := hcover x
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, hp⟩
      coord := fun i => coord _ (E.symm i)
      isEmbedding := fun i => (hsrc _).2
      image := fun i => himage _
      trans := fun i j => htrans _ _
      regular := fun i x hx => (hreg _ x hx).1
      dim := fun i x hx => (hreg _ x hx).2
      lift := fun i => lift (E.symm i)
      lift_one := fun i => ⟨E.symm i, fun k => by simp [lift]⟩
      lift_mem := fun i => hliftmem _
      compat := fun i j => hcompat _ _
      surj := fun z hz _ => by
        obtain ⟨p, x, hx, h⟩ := hsurj z hz
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, x, hx, h⟩
      inj := fun i j x hx x' hx' _ h => hinj _ _ x hx x' hx' h
      inv := fun i x hx _ p' hp' => hinv _ x hx p' hp'
      bd := fun i => bd _ (pC J) (E.symm i)
      le_bd := fun i => le_trans (Ideal.map_mono (sup_le_sup_right le_sup_left _)) Ideal.le_radical
      zero_bd := fun i => hzero _
      rc := rc _ (pC J)
      comp := comp _ (pC J)
      sncAt := fun i x hx => (hsc _ x hx).choose
      comp_eq := fun i x hx => (hsc _ x hx).choose_spec.1
      mult := fun f a hf hfP hz => ⟨fun k => ordAlong (compIdeal _ (pC J) k) _ f,
        fun i x hx => (hsc _ x hx).choose_spec.2 f a hf hfP hz⟩ }
  refine exists_isEmbedded_of_algRes hJ hJP (pcContract K ι _ e hP) R ?_ ?_ ?_
  · intro z hz
    obtain ⟨p, x, hx, h⟩ := hsurj z hz
    obtain ⟨i, rfl⟩ := E.symm.surjective p
    exact ⟨i, x, hx, h⟩
  · intro i j x hx x' hx' h
    exact hinj _ _ x hx x' hx' h
  · intro i x hx p' hp'
    exact hinv _ x hx p' hp'

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedFrameValueFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_frame_value_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (zb₂ : (Σ k, baseIdx ι M.blk k) → ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (H U : Ψ → Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.blk (τ, a) = some k₀ → baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) → SameOrbit zb₂ (baseOf M k₀ z) → (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) → IsBlockDiag j V → V.BlockTriangular id → (∀ c ∈ stepCols N j a, V c c ≠ 0) → (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (H p.1 * U p.1) I (stepCols N j p.2)) → (∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (H τ * (1 + Matrix.single cb ca t) * V) I (stepCols N j a)) → SameOrbit (sqZ M F zb₂ H k₀ τ ca cb t) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags <;> assumption)
end

