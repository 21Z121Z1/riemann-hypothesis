import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0385
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGap
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0174
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0425
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0257
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0426
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiscreteSeriesDegreeBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0007
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.HermitianCurvature.BesselNonvanishingReduction

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFiniteBesselPeriodNeZeroGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselPeriodNonzeroGap

open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity GlobalTheory.BesselPeriodNonzero

set_option maxHeartbeats 1600000 in

theorem nzOn_of_mass (hy : GlobalTheory.GapIn.Hyp) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {R : Rep k r}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Mt k r)} {B l : R.H → Wp} {w : R.H} (hR : R.IsDS ε mu)
    (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hS : SideG k r z π u μW μN μG νq) (hB : IsBes R z π B) (hwK : R.KFin w) {c : ℝ} (hc : 0 ≤ c)
    (hiso : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = ENNReal.ofReal (c * ‖v‖ ^ 2))
    (h0 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0) (hl : IsBeL R z π μW μN l) :
    ∃ v ∈ R.sm, l v ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hK : PI.KFinSmooth := hy.1.1.2.2.1
  have hRG : R.IsDG ε mu := ⟨hR.1, hR.2, ⟨h, hgap, hok⟩⟩
  obtain ⟨hmul, hone, hun, hsm, hTK, hTKs, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have hwT := hKT w hwK
  have hw := hTK w hwT
  have hΦ := fun v hv => (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r ε mu R hR Wp B hB.1 hB.2.1 hB.2.2.2 v hv).1
  have hS' := hS
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hWh, hNh, hGh, hq⟩ := hS'
  have := hWh.1; have := hNh.1; have := hGh.1
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_id
  have hSeq : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN = (μW.prod μN).map (fun p => mulMt p.1 p.2) := rfl
  have hsf : SFinite (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) := by rw [hSeq]; infer_instance
  have hGm : MeasurableSet {y : Mt k r | Matrix.of y ∈ GG k r} := (isClosed_UH.preimage hof).measurableSet
  have hSae : ∀ᵐ s ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN), Matrix.of s ∈ GG k r := by
    rw [hSeq]
    refine (ae_map_iff measurable_mulMt.aemeasurable hGm).2 ?_
    filter_upwards [hPae] with p hp
    exact Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hS0 : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN ≠ 0 := GlobalTheory.SideCompare.muS_ne_zero hWh.2.1 hNh.2.1
  have hνae := GlobalTheory.BesselNorm.quot_ae hq hGae hSae hS0
  have hνs : SigmaFinite νq := GlobalTheory.SideCompare.sigmaFinite_of_isQuotMeas hS0 hq
  have hSC : SecondCountableTopology Wp := by
    have := FiniteDimensional.proper ℂ Wp
    infer_instance
  have one_mem : (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) ∈ GG k r := by
    show (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)ᴴ * Hpk k r * 1 = Hpk k r; simp
  have memDD : ∀ g ∈ GG k r, R.σ g w ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have wDD : w ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w := by
    have := memDD 1 one_mem; rwa [hone] at this
  have DDsm : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, v ∈ R.sm := by
    intro v hv
    refine hTK v (Submodule.span_le.2 ?_ hv)
    rintro _ ⟨g, hg, rfl⟩
    exact hTKs g hg w hwT
  have hnorm : ∀ g ∈ GG k r, ‖R.σ g w‖ = ‖w‖ := fun g hg => (sigma_facts hR.2).2 g hg w
  have hcw : c * ‖w‖ ^ 2 ≠ 0 := by
    intro h1; apply h0; rw [hiso w wDD, h1, ENNReal.ofReal_zero]
  have hmeas : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      AEStronglyMeasurable (fun y : Mt k r => B (R.σ (Matrix.of y) v)) νq := fun v hv =>
    aesm_of_contOn ((hΦ v (DDsm v hv)).comp hof.continuousOn fun y hy => hy) hGm hνae
  have hsq : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      Integrable (fun y : Mt k r => ‖B (R.σ (Matrix.of y) v)‖ ^ 2) νq ∧
        ∫ y : Mt k r, ‖B (R.σ (Matrix.of y) v)‖ ^ 2 ∂νq = c * ‖v‖ ^ 2 := fun v hv =>
    sq_int (hmeas v hv) (by positivity) (hiso v hv)

  have hpair : ∀ a ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, ∀ b ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      Integrable (fun y : Mt k r => ⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ) νq ∧
      ∫ y : Mt k r, ‖⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ‖ ∂νq ≤ c * ‖a‖ ^ 2 + c * ‖b‖ ^ 2 ∧
      (∫ y : Mt k r, ⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ ∂νq).re = c * (⟪a, b⟫_ℂ).re := by
    intro a ha b hb
    obtain ⟨i1, i2, i3⟩ := inner_int (hmeas a ha) (hmeas b hb) (hsq a ha).1 (hsq b hb).1
    have e : ∫ y : Mt k r, ‖B (R.σ (Matrix.of y) a) + B (R.σ (Matrix.of y) b)‖ ^ 2 ∂νq = c * ‖a + b‖ ^ 2 := by
      rw [← (hsq (a + b) (Submodule.add_mem _ ha hb)).2]
      apply integral_congr_ae
      filter_upwards [hνae] with y hy
      rw [map_add, hB.1 _ (hsm _ hy a (DDsm a ha)) _ (hsm _ hy b (DDsm b hb))]
    rw [(hsq a ha).2, (hsq b hb).2] at i2 i3
    rw [e, norm_add_sq (𝕜 := ℂ)] at i3
    refine ⟨i1, i2, ?_⟩
    simp only [RCLike.re_to_complex] at i3
    linarith

  set m : Mt k r → ℂ := fun g => ⟪w, R.σ (Matrix.of g) w⟫_ℂ with hm
  have hmc : ContinuousOn m {y : Mt k r | Matrix.of y ∈ GG k r} :=
    continuousOn_const.inner ((hcont w).comp hof.continuousOn fun y hy => hy)
  have hmi : Integrable m μG := by
    obtain ⟨C, Ws, -, hd⟩ := Gp91.GlobalTheory.BesselDecay.decay_TK hy.1 k r ε mu h R hRG hgap hok w hwT
    obtain ⟨-, -, t1, t2⟩ := GlobalTheory.thresholds_of_gapOK k r h hok
    have hg := GlobalTheory.gN_rpow_neg_integrable_haar k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hGh (by linarith)
    refine (hg.const_mul (C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum)).mono'
      (aesm_of_contOn hmc hGm hGae) ?_
    filter_upwards [hGae] with y hy
    rw [neg_sub]
    exact hd w hw _ hy

  set F : Mt k r × Mt k r → ℂ := fun q =>
    star (m q.1) * ⟪B (R.σ (Matrix.of q.2) w), B (R.σ (Matrix.of q.2 * Matrix.of q.1) w)⟫_ℂ with hF
  have hFm : AEStronglyMeasurable F (μG.prod νq) := by
    have c1 : Continuous (fun q : Mt k r × Mt k r => (Matrix.of q.1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_fst
    have c2 : Continuous (fun q : Mt k r × Mt k r => (Matrix.of q.2 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_snd
    refine aesm_of_contOn (s := {q : Mt k r × Mt k r | Matrix.of q.1 ∈ GG k r ∧ Matrix.of q.2 ∈ GG k r}) ?_
      ((isClosed_UH.preimage c1).inter (isClosed_UH.preimage c2)).measurableSet
      ((Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hνae))
    exact (continuous_star.comp_continuousOn (hmc.comp continuous_fst.continuousOn fun q hq => hq.1)).mul
      (((hΦ w hw).comp c2.continuousOn fun q hq => hq.2).inner
        ((hΦ w hw).comp (c2.matrix_mul c1).continuousOn fun q hq => Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hq.2 hq.1))
  have hF1 : ∀ g : Mt k r, Matrix.of g ∈ GG k r → (fun y => F (g, y)) =ᵐ[νq] fun y =>
      star (m g) * ⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ := by
    intro g hg
    filter_upwards [hνae] with y hy
    simp only [hF]
    rw [hmul _ hy _ hg]
  have hF2 : ∀ g : Mt k r, Matrix.of g ∈ GG k r → (fun y => F (g, y)) =ᵐ[νq] fun y =>
      ⟪B (R.σ (Matrix.of y) (m g • w)), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ := by
    intro g hg
    filter_upwards [hνae, hF1 g hg] with y hy h1
    rw [h1, map_smul, hB.2.1 _ _ (hsm _ hy w hw), inner_smul_left]
    rfl
  have hFi : Integrable F (μG.prod νq) := by
    rw [integrable_prod_iff hFm]
    constructor
    · filter_upwards [hGae] with g hg
      exact ((hpair w wDD _ (memDD _ hg)).1.const_mul _).congr (hF1 g hg).symm
    · refine (hmi.norm.mul_const (c * ‖w‖ ^ 2 + c * ‖w‖ ^ 2)).mono' hFm.norm.integral_prod_right' ?_
      filter_upwards [hGae] with g hg
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      have e : ∫ y, ‖F (g, y)‖ ∂νq = ‖m g‖ *
          ∫ y : Mt k r, ‖⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ‖ ∂νq := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hF1 g hg] with y hy
        rw [hy, norm_mul, norm_star]
      rw [e]
      have := (hpair w wDD _ (memDD _ hg)).2.1
      rw [hnorm _ hg] at this
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

  have hzero : ∫ q, F q ∂(μG.prod νq) = 0 := by
    rw [integral_prod_symm F hFi]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hνae, hFi.prod_left_ae] with y hy hi
    set f : Mt k r → ℂ := fun g => star ⟪R.σ (Matrix.of y) w, R.σ (Matrix.of g) w⟫_ℂ *
      ⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of g) w)⟫_ℂ with hf
    have hfc : ContinuousOn f {y : Mt k r | Matrix.of y ∈ GG k r} :=
      (continuous_star.comp_continuousOn (continuousOn_const.inner
        ((hcont w).comp hof.continuousOn fun y hy => hy))).mul
        (continuousOn_const.inner ((hΦ w hw).comp hof.continuousOn fun y hy => hy))
    have hfm : AEStronglyMeasurable f (μG.map (lmulM (Matrix.of y))) := by
      rw [hGh.2.2.2 _ hy]; exact aesm_of_contOn hfc hGm hGae
    have hlm : Measurable (lmulM (k := k) (r := r) (Matrix.of y)) :=
      measurable_mulMt.comp (measurable_const.prodMk measurable_id : Measurable fun x : Mt k r => (y, x))
    have e : (fun g => F (g, y)) =ᵐ[μG] f ∘ lmulM (Matrix.of y) := by
      filter_upwards [hGae] with g hg
      show star ⟪w, R.σ (Matrix.of g) w⟫_ℂ * _ = star ⟪R.σ (Matrix.of y) w, R.σ (Matrix.of y * Matrix.of g) w⟫_ℂ * _
      rw [hmul _ hy _ hg w, hun _ hy, ← hmul _ hy _ hg w]
      rfl
    have hfi : Integrable f μG := by
      rw [← hGh.2.2.2 _ hy]
      exact (integrable_map_measure hfm hlm.aemeasurable).2 (hi.congr e)
    have e2 : ∫ g, F (g, y) ∂μG = ∫ g, f g ∂μG := by
      rw [integral_congr_ae e]
      conv_rhs => rw [← hGh.2.2.2 _ hy]
      exact (integral_map hlm.aemeasurable hfm).symm
    rw [e2]
    refine unfold_zero hK hR hS hB hw (fun x hx => ?_) _ hfi
    obtain ⟨j1, j2⟩ := hl.2 x hx _ (hTKs _ hy w hwT)
    refine ⟨j1, ?_⟩
    rw [j2, hcon x hx]
    ext ξ; simp

  obtain ⟨d, hd, hSch⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hy.1 k r ε μG hGh
  obtain ⟨s1, s2⟩ := (hSch mu R hRG).2 w w w w
  have hdpos : 0 < d * fdegHC mu := mul_pos hd (GlobalTheory.BesselNorm.fdegHC_pos mu hR.1.1.injective)
  have hre : (∫ q, F q ∂(μG.prod νq)).re = c * (∫ g, m g * star (m g) ∂μG).re := by
    rw [integral_prod F hFi]
    have a1 := integral_re hFi.integral_prod_left
    have a2 := integral_re s1
    simp only [RCLike.re_to_complex] at a1 a2
    rw [← a1, ← a2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hGae] with g hg
    rw [integral_congr_ae (hF2 g hg), (hpair _ (Submodule.smul_mem _ _ wDD) _ (memDD _ hg)).2.2, inner_smul_left,
      mul_comm ((starRingEnd ℂ) (m g))]
    rfl
  rw [hzero, s2, inner_self_eq_norm_sq_to_K] at hre
  have e3 : (((‖w‖ : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / ((d * fdegHC mu : ℝ) : ℂ))).re =
      ‖w‖ ^ 2 * ‖w‖ ^ 2 / (d * fdegHC mu) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre' : 0 = c * (‖w‖ ^ 2 * ‖w‖ ^ 2 / (d * fdegHC mu)) := by rw [← e3]; exact hre
  have hw2 : ‖w‖ ^ 2 ≠ 0 := right_ne_zero_of_mul hcw
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcw
  exact mul_ne_zero hc0 (div_ne_zero (mul_ne_zero hw2 hw2) hdpos.ne') hre'.symm

theorem exists_kFin_period_ne_zero : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B l : R.H → Wp) (w : R.H), R.IsDS ε mu → GapAtLeast ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → SideG k r z π u μW μN μG νq → IsBes R z π B → R.KFin w → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0 → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → IsBeL R z π μW μN l → ∃ v, R.KFin v ∧ l v ≠ 0 := by
  intro hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq B l w hR hgap hok hS hB hwK h0 hfin hl
  have hK : PI.KFinSmooth := hy.1.1.2.2.1
  have hw : w ∈ R.sm := hK k r ε mu R.H R.σ hR.1 hR.2 w hwK
  obtain ⟨c, hc, hiso⟩ := GlobalTheory.T.exists_l2SG_translates_eq_const_mul_norm_sq k r ε mu R Wp z π u μW μN μG νq B w hR hS hB hw hfin
  exact GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r ε mu R hR Wp l hl.1.1 hl.1.2.1 hl.1.2.2.2
    (nzOn_of_mass hy hR hgap hok hS hB hwK hc hiso h0 hl)

end GlobalTheory.BesselPeriodNonzeroGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThree
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.AutInhab

noncomputable section

namespace GlobalTheory.PerpInst

theorem exists_drop {n : ℕ} (ε : Fin n → Bool) (k : Fin n) :
    ∃ (m : ℕ) (f : Fin m → Fin n), m + 1 = n ∧ Function.Injective f ∧ (∀ i, f i ≠ k) ∧
      ∀ b, (univ.filter fun a => ε (f a) = b).card + (if ε k = b then 1 else 0) =
        (univ.filter fun a => ε a = b).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.2; omega⟩
  refine ⟨m, k.succAbove, rfl, Fin.succAbove_right_injective, k.succAbove_ne, fun b => ?_⟩
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ k, add_comm]

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J y x = star y ⬝ᵥ (J *ᵥ x) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem form_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (J G : Matrix (Fin n) (Fin n) E)
    (y x : Fin n → E) : star (G *ᵥ y) ⬝ᵥ (J *ᵥ (G *ᵥ x)) = star y ⬝ᵥ ((Gᴴ * J * G) *ᵥ x) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem hasSignature_all (I : AutInst) {P Q : ℕ} (h : HasSig I P Q) (φ : I.E →+* ℂ) :
    Formalism.UG.HasSignature (I.J.map φ) P Q := by
  have key : ∃ v, φ = I.φ v ∨ φ = ComplexEmbedding.conjugate (I.φ v) := by
    refine ⟨(InfinitePlace.mk φ).comap (algebraMap I.F I.E), ?_⟩
    rcases GlobalTheory.Count.Test.embedding_cases I (InfinitePlace.mk φ) with h | h <;>
      rcases InfinitePlace.embedding_mk_eq φ with h' | h'
    · exact Or.inl (h'.symm.trans h)
    · right
      rw [← h, h']; simp
    · exact Or.inr (h'.symm.trans h)
    · left
      exact star_injective (h'.symm.trans h)
  obtain ⟨v, rfl | rfl⟩ := key
  · rw [← (h v).1, ← (h v).2]; exact hasSignature_inst I v
  · rw [← (h v).1, ← (h v).2]
    refine hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ((I.P_unit v).map (starRingEnd ℂ).mapMatrix) ?_
    have h1 := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (I.P_spec v)
    simp only [Matrix.map_mul] at h1
    have h2 : (Formalism.REAL.Jm (I.ε v)).map (starRingEnd ℂ) = Formalism.REAL.Jm (I.ε v) := by
      rw [Formalism.REAL.Jm, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext a
      split_ifs <;> simp
    rw [h2] at h1
    exact h1

theorem exists_point (I : AutInst) (ε : Fin I.n → Bool) (γ : GL (Fin I.n) I.E)
    (hγ : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E) = signMat I.E ε) :
    ∃ xf : I.Gf, ∀ z, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I (1, xf) ↔ z ∈ intLat I.E I.n := by
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  have hsur : Function.Surjective G.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 γ.isUnit
  have hinj : Function.Injective G.mulVec := Matrix.mulVec_injective_iff_isUnit.2 γ.isUnit
  let Λ : Submodule (𝓞 I.E) (Fin I.n → I.E) := (intLat I.E I.n).map (G.mulVecLin.restrictScalars (𝓞 I.E))
  have hΛ : ∀ z, G *ᵥ z ∈ Λ ↔ z ∈ intLat I.E I.n := fun z =>
    ⟨fun ⟨w, hw, e⟩ => (hinj e : w = z) ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
  obtain ⟨xf, hxf⟩ := GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual I Λ ⟨(intLat_fg _).map _, by
      have : (Λ : Set (Fin I.n → I.E)) = G.mulVecLin '' (intLat I.E I.n : Set (Fin I.n → I.E)) := rfl
      rw [this, ← Submodule.map_span, intLat_span, Submodule.map_top, LinearMap.range_eq_top]
      exact hsur⟩ (by
      intro x
      obtain ⟨x, rfl⟩ := hsur x
      rw [hΛ, intLat_dual ε]
      constructor
      · rintro h _ ⟨y, hy, rfl⟩
        have := h y hy
        rw [hform_eq, ← hγ, ← form_mulVec, ← hform_eq] at this
        exact this
      · intro h y hy
        have := h _ ((hΛ y).2 hy)
        rwa [hform_eq, form_mulVec, hγ, ← hform_eq] at this)
  exact ⟨xf, fun z => hxf ▸ hΛ z⟩

theorem exists_isPerpInst : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  intro I P Q h _ s hs
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  set ε := I.ε v with hε
  have hP : (univ.filter fun a => ε a = true).card = P := (h v).1
  have hQ : (univ.filter fun a => ε a = false).card = Q := (h v).2
  obtain ⟨k, hk⟩ : ∃ k, ε k = s := by
    have : 0 < (univ.filter fun a => ε a = s).card := by
      cases s
      · rw [hQ]; exact hs
      · rw [hP]; exact hs
    obtain ⟨k, hk⟩ := Finset.card_pos.1 this
    exact ⟨k, (Finset.mem_filter.1 hk).2⟩
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.hermitian_spaces_same_signature_isometric I.E I.cm.cmUnram I.n I.J (signMat I.E ε) I.J_herm (signMat_isHerm ε)
    I.J_det (signMat_det ε) ⟨I.L, ⟨I.L_fg, I.L_span⟩, fun x => by simpa only [hform_eq] using I.L_dual x⟩
    ⟨intLat I.E I.n, ⟨intLat_fg _, intLat_span _⟩, fun x => by simpa only [hform_eq] using intLat_dual ε x⟩
    (fun φ => ⟨P, Q, hasSignature_all I h φ, by
      rw [signMat_map, ← hP, ← hQ]
      exact hasSignature_of_frame (P := 1) isUnit_one (by simp)⟩)
  obtain ⟨xf, hxf⟩ := exists_point I ε γ hγ
  obtain ⟨m, f, hm, hf, hfk, hcard⟩ := exists_drop ε k
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  let C : Matrix (Fin I.n) (Fin m) I.E := (1 : Matrix (Fin I.n) (Fin I.n) I.E).submatrix id f
  refine ⟨ofSigns I.cm (fun a => ε (f a)), RingEquiv.refl I.E, G *ᵥ Pi.single k 1, G * C, xf,
    ⟨fun _ => rfl, hm, ?_, ?_, ?_, ?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · rw [form_mulVec, hγ]
    simp [signMat, sgn, hk]
  · have : star (G *ᵥ Pi.single k 1) ᵥ* (I.J * (G * C)) = star (Pi.single k 1) ᵥ* ((Gᴴ * I.J * G) * C) := by
      rw [star_mulVec, vecMul_vecMul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    funext j
    simp [signMat, C, vecMul, dotProduct, Pi.single_apply, Matrix.one_apply, hfk j]
    rfl
  · have : (G * C)ᴴ * I.J * (G * C) = Cᴴ * (Gᴴ * I.J * G) * C := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    change _ = signMat I.E fun a => ε (f a)
    ext i j
    rw [Matrix.mul_apply]
    simp [signMat, C, Matrix.one_apply, Matrix.diagonal_apply, hf.eq_iff]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · exact (hxf _).2 (Submodule.subset_span ⟨k, by simp⟩)
  · change ∀ y : Fin m → I.E, y ∈ intLat I.E m ↔ (G * C) *ᵥ y ∈ lamX I (1, xf)
    intro y
    rw [← mulVec_mulVec, hxf, mem_intLat, mem_intLat]
    constructor
    · intro hy i
      change ∑ j, C i j * y j ∈ _
      refine sum_mem fun j _ => mul_mem ?_ (hy j)
      simp only [C, submatrix_apply, id, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro hy j
      have := hy (f j)
      simpa [C, mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using this
  · change (univ.filter fun a => ε (f a) = true).card = _
    have := hcard true
    rw [hP, hk] at this
    cases s <;> simp at this ⊢ <;> omega
  · change (univ.filter fun a => ε (f a) = false).card = _
    have := hcard false
    rw [hQ, hk] at this
    cases s <;> simp at this ⊢ <;> omega

end GlobalTheory.PerpInst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqHarishChandraRatioLargeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapDegreeRatio

theorem deg_eq_of_goodS (hH : GlobalTheory.GapIn.Hyp) (D : D7) :
    ∃ c : ℝ, 0 < c ∧ ∀ (W : LocW D.R.k D.R.rS) (l : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ),
      GoodS D l A → GapAtLeast (epsSH D.R) l h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h →
      A.deg = c * Formalism.QuantumDeterminants.fdegHC l := by
  obtain ⟨c, hc, hF⟩ := hH.1.2.2.2.2.2.2 D.R.k D.R.rS (epsSH D.R) (Formalism.MainNotions.S.Inh.obj_cayleyU_rows D)
  set s : NNReal := D.s.cdScale _ (epsSH D.R) with hs
  have hs0 : 0 < s := D.s.cdScale_pos _ _
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  refine ⟨c / s, div_pos hc hs0', fun W l A h hA hg hok => ?_⟩
  obtain ⟨hl, ⟨Q, hQ, hDS⟩, -, -, -, -, -, -, -, -, P, hP, hd⟩ := hA
  have hFQ : IsFdeg (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q)) (c * Formalism.QuantumDeterminants.fdegHC l) :=
    hF l A.H (fun g => A.σ (Q⁻¹ * g * Q)) ⟨h, hg, hok⟩ hl hDS
  have hFQs : IsFdeg ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q))
      (c * Formalism.QuantumDeterminants.fdegHC l / s) := by
    refine ⟨div_pos hFQ.1 hs0', fun v w v' w' => ⟨(hFQ.2 v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
    rw [integral_smul_measure, (hFQ.2 v w v' w').2, ENNReal.coe_toReal, Complex.real_smul]
    have hd0 : ((c * Formalism.QuantumDeterminants.fdegHC l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hFQ.1.ne'
    have hcc : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0'.ne'
    push_cast at hd0 ⊢
    field_simp
  have : Nontrivial A.H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : A.H)
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ (epsSH D.R) := ⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.1.2⟩
  have h1 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (P⁻¹ * g * P)) (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q = (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw
  have h2 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (Q⁻¹ * g * Q)) (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 _ hFQs w hw
  rw [← h1, h2]
  ring

theorem deg_ratio : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (W : LocW D.R.k D.R.rS) (l l' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A A' : LocS W) (h : ℝ), GoodS D l A → GoodS D l' A' → GapAtLeast (epsSH D.R) l h → GapAtLeast (epsSH D.R) l' h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → A'.deg / A.deg = Formalism.QuantumDeterminants.fdegHC l' / Formalism.QuantumDeterminants.fdegHC l := by
  intro hH D W l l' A A' h hA hA' hg hg' hok
  obtain ⟨c, hc, hk⟩ := deg_eq_of_goodS hH D
  rw [hk W l A h hA hg hok, hk W l' A' h hA' hg' hok]
  exact mul_div_mul_left _ _ hc.ne'

end GlobalTheory.GapDegreeRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesLocalDataUnimodularStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gluedLattices_iff_existsUnique_localDatum : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ Λ : LV D, (Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ ∃ y : Dat Z FP, Λ ∈ globSet G G' y) ∧ (∀ y y' : Dat Z FP, Λ ∈ globSet G G' y → Λ ∈ globSet G G' y' → y = y') ∧ (∀ y : Dat Z FP, Λ ∈ globSet G G' y → (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite) ∧ ∀ (y y' : Dat Z FP), ∀ h ∈ H0 F F', RMoves h y y' → (Λ ∈ globSet G G' y ↔ Formalism.HermitianLatticesTheory.gmap h Λ ∈ globSet G G' y') := by
  first | exact @GlobalTheory.GlueDat.glued_data | exact GlobalTheory.GlueDat.glued_data | (intros; apply GlobalTheory.GlueDat.glued_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InputsOfSubsetWidths
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem inputs_of_subset_widths : ∀ S S' : Set ℝ, S ⊆ S' → (AmpOn S' → AmpOn S) ∧ (SmallOn S' → SmallOn S) ∧ (CntOn S' → CntOn S) ∧ (CountBoundOn S' → CountBoundOn S) ∧ (TieOn S' → TieOn S) := by
  intro S S' hSS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h Cg cb Cu cT CT hb hT
    obtain ⟨C, C2, Ch, h1, h2, h3⟩ := h Cg cb Cu cT CT hb hT
    refine ⟨C, C2, Ch, h1, h2, fun Cpr δ hδ => ?_⟩
    obtain ⟨thr, ht⟩ := h3 Cpr δ hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT δ hb hT hδ
    obtain ⟨thr, ht⟩ := h Cg cb Cu cT CT δ hb hT hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, cS, c4, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, cS, c4, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨cV, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨cV, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩

end GlobalTheory.Core.Deg
end

