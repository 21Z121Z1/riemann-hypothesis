import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0438
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0481
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UMatMulLoc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0427
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0477
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0473
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0459
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0455
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0206

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGap
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JFactTie

theorem jFactN_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  intro D X Y hF hI C hB u u' hGap t hG hr
  have hex : ∃ s : TT Y u u', s.toTerm = tc hI t :=
    Formalism.L2.SG.Pf.liftOntoC_of Formalism.L2.SG.Pf.WittFlags.LatIso_holds D X Y u u' (tc hI t)
  have hs : hex.choose.toTerm = tc hI t := hex.choose_spec
  have hrel : hex.choose.relevant := by
    show hex.choose.toTerm.relevant
    rw [hs]
    exact (hI.relevant t).1 hr
  have hsG : hex.choose.G ≠ 0 := by
    show hex.choose.toTerm.G ≠ 0
    rw [hs]
    intro h0
    apply hG
    apply (algebraMap D.host.F D.host.E).injective
    rw [gterm_val hI t, h0, map_zero]
  have hP : HasPin hex.choose := GlobalTheory.T.relevantLift_normalisedData_exist D X Y u u' hex.choose hrel hsG
  have hx := hP.choose_spec
  have hJ : JtOf hI t = Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') hex.choose := by
    unfold JtOf; rw [dif_pos hex]
  have hV : volRC hI t = (hP.choose.2.1 hP.choose.2.2).toReal := by
    unfold volRC covR; rw [dif_pos ⟨hr, hG, hex⟩, dif_pos hP]
  have hinv : ∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (hex.choose.pt.1 v), ∀ y,
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * (r * y))) =
        Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * y)) := by
    intro v
    obtain ⟨τ, rfl⟩ : ∃ τ, v = vOf X τ := ⟨X.pl v, by simp [vOf]⟩
    obtain ⟨p, hp⟩ := GlobalTheory.T.relevant_term_has_real_relative_point D X Y hF hI 1 C u u' t hex.choose hs hG hr τ
    exact GlobalTheory.StabInv.stab_inv D X 1 C hB u u' τ (hex.choose.pt.1 (vOf X τ)) p hGap hp
  obtain ⟨μl, νl, hH, hQ, hR, hA⟩ := GlobalTheory.T.normalisedLift_amplitude_eq_covolume_mul_local D X Y 1 C u u' hex.choose hP.choose hrel hsG hx.1 hx.2.1 hx.2.2 hinv
  have hloc : ∀ τ, j1 hI C hB t τ = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) *
      hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ))) := by
    intro τ
    haveI : SigmaFinite (μl (vOf X τ)) := (hH (vOf X τ)).1
    exact GlobalTheory.T.localAmplitude_wittLift_eq_quotientIntegral D X Y hF hI C hB u u' t hex.choose hs hG hr hGap τ (μl (vOf X τ)) (νl (vOf X τ)) inferInstance
      (hQ (vOf X τ)) (hR τ)
  have hK := GlobalTheory.T.amplitudeConstant_eq_prod_covolumes D X Y hF 1 C hB u u' one_pos hGap
  have hre : (∏ τ, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ)))) =
      ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (hex.choose.pt.1 v)) :=
    Fintype.prod_equiv X.pl.symm _ _ (fun τ => rfl)
  have hcov : covN (Y := Y) C u * covN (Y := Y) C u' =
      ((Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := rfl
  rw [hJ, hV, hA, hcov]
  unfold P1
  rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, hre, hK]
  ring

end GlobalTheory.JFactTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

open MeasureTheory NumberField Formalism.FourierDecayAlt Finset

namespace GlobalTheory.UnifPTGap

open Formalism.MainNotions.BridgeLemma

theorem tFrame_of_dsig (hM : Formalism.HermitianLatticesTheory.SiegelMassRatio) (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC)
    {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 := by
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  exact level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith)
    (level_formula_family Fm C0 Cg cb Cu cT CT (fun x i => mass_ratio_of_siegel_cm_unramified hM (Fm.D x i)) (mass_two_bound_family_holds Fm) hR)
    (Formalism.L2.SG.Pf.SzHypFam.localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

theorem uniformPT_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps),
    thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i =>
      VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  intro hM hH hBp Cg cb Cu cT CT C0 C1
  set Cβ : ℝ := max 2 (max Cu (max CT (1 / 8 + 2 * Cg))) with hCβ
  have hβ2 : 2 ≤ Cβ := le_max_left _ _
  have hu : Cu ≤ Cβ := (le_max_left _ _).trans (le_max_right _ _)
  have hT : CT ≤ Cβ * 1 := by rw [mul_one]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hg : 1 / 8 + 2 * Cg ≤ Cβ * 1 := by
    rw [mul_one]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨Cb, Cg₀, hBP⟩ := (GlobalTheory.T.besselPointwiseBound_at_largeGaps hH hBp 1).imp fun _ h => h.imp fun _ h Cg hCg => (h Cg hCg).2.2
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.T.oneBessel_torusTranslates_largeGap hH
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.T.amplitude_eq_besselFunction_largeGaps hH Cg cb Cu cT CT C0 C1
  refine ⟨max (Ca + Cβ * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0), 1000, fun eps Fm _ hl hR Cn => ?_⟩
  obtain ⟨m₀, hA⟩ := hAmp Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  have hAmpF : OwnEv Fm fun C' Cl x i => Bridge.AmpIsBessel (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Ca :=
    ⟨x0, fun x hx i => hA (Fm.D x i) (Fm.L x i) _ _ hl (hx0 x hx i).2.2.2.2.1 (hx0 x hx i).2.1
      (Fm.ties x i).cdScale_tie⟩
  obtain ⟨a', hFr⟩ := hFrm Cn
  have hStd := Formalism.MainNotions.BridgeLemma.stdHypS_of Fm Cg cb Cu cT CT C0 1 Cβ (by linarith) zero_le_one hβ2 hu hT hg
    (max Cg₀ a') (200 * Cn)
  have hTF := tFrame_of_dsig hM hH.2.2.2 Fm (by linarith) hR
  exact Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H =>
    AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity _ _ _ _ _ _ _ _ _ _ Cn C1 Ca 1 Cf (max Cg₀ a') (200 * Cn) Cβ (max Cb 0) _ H.1.1
      (hFr _ (le_max_right _ _) _ (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus _ Cgf 2 le_rfl (hOB _)))
      H.1.2 H.2
      (OnePlaceEstimates.upper_bound_mono_constant _ one_pos (le_max_left _ _) (hBP _ (le_max_left _ _) _ Cn (200 * Cn) le_rfl))
      (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _)) ((hAmpF.and hStd).and hTF)

end GlobalTheory.UnifPTGap
end

