import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0482
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.CountT
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0483
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
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

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalDataStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeBound_at_terms_of_localData : GlobalTheory.TypeAsm.LocDatC → GlobalTheory.TypeAsm.TailP → GlobalTheory.TypeAsm.AmpP := by
  first | exact @GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound | exact GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound | (intros; apply GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountClausesClosed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.IrrCountEv

theorem k_ge_of_hypLine {D : D7} (L : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D L C' Cl Cg cb Cu cT CT) :
    8 * L.CGam * L.sc.L ≤ D.R.k := by
  have h8 : 8 * L.CGam ≤ C' := hH.1
  have hk : C' * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L ≤ D.R.k := hH.2.1
  have hL : 0 ≤ L.sc.L := by unfold Scale.L; exact Real.rpow_nonneg (le_trans zero_le_one L.sc.one_lt_alt.le) _
  have hmfL : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L := by positivity
  have h1 : 8 * L.CGam * ((D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L) ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L) :=
    mul_le_mul_of_nonneg_right h8 hmfL
  have h2 := logGam_ge L
  linarith

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem hypLine_ev (hR : ResidualStandingConditions Fm) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    Fm.x1 < x ∧ ArithmeticConditionsOfDatum (Fm.D x i) ∧
      StandingHypotheses (Fm.D x i) (Fm.L x i) Fm.CkLow (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu := by
  obtain ⟨r1, ⟨x5, HT⟩, x0, HR⟩ := hR
  have he := eps_pos' Fm
  obtain ⟨x4, hx4⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < eps / 100)).eventually_ge_atTop
      (max (2 * sCl Fm) (max 2 (5 / (eps / 100)))))
  refine ⟨max (Fm.x1 + 1) (max x0 (max x4 x5)), fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) hx
    linarith
  have hx0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx45 : max x4 x5 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx4' := hx4 x (le_trans (le_max_left _ _) hx45)
  obtain ⟨r2, hA⟩ := HR x hx0 i
  obtain ⟨t1, t2⟩ := HT x (le_trans (le_max_right _ _) hx45) i
  have r3 := tuWin_of (Fm.L x i) Fm.CTu t1 t2
  have hth : szTh (Fm.L x i) = eps / 100 := by unfold szTh; rw [Fm.L_eps]
  have hXX : XX (Fm.L x i) = x ^ (eps / 100) := by unfold XX; rw [hth, Fm.L_x x i hx1]
  have hH := standing_hypotheses_of_bounds (Fm.L x i) (Fm.params x hx1 i) (Fm.sizes x hx1 i) (sCl Fm) (1 / 2) Fm.CTu (sCl_pos Fm)
    (by rw [Fm.params_CCount]; exact sCl_le_CCount Fm) (by rw [Fm.params_Cgap]; exact sCl_le_Cgap Fm)
    (by rw [hXX]; exact le_trans (le_max_left _ _) hx4')
    (by rw [hXX]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx4')
    (by rw [hXX, hth]; exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx4')
    (by rw [Fm.params_CkLow, Fm.CGam_eq]; exact r1) r2 r3
  rw [Fm.params_CkLow, Fm.params_CYL] at hH
  exact ⟨hx1, hA, hH⟩

end Fam

theorem countClauses_closed : ∀ (𝒞 : FamClass) (c30 : List ℝ → CountingConstants),
    (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) →
    (∀ {eps : ℝ} (Fm : FamP eps), 0 < (c30 Fm.cOut).cb) →
    (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) →
    Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      AdmissibleBoundsFromSource.CountTheoremHypotheses (Fm.D x i) (Fm.L x i) (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C (c30 Fm.cOut).cb ∧
        4 * (Fm.D x i).R.r < (Fm.D x i).host.g 1 := by
  intro 𝒞 c30 hc30 hcb hTu
  refine Formalism.MainNotions.Pk.Closed.large (linkThresholds (fun _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩) c30)
    (Formalism.MainNotions.Pk.Closed.of_class (P := fun Fm _ => TuSize Fm) fun Fm _ hc => hTu Fm hc) ?_
  intro eps Fm CH hL hT
  obtain ⟨-, hCl2, hCl3, h8⟩ := link_thresholds_spec Fm CH _ c30 hL
  have hR : ResidualStandingConditions Fm := ⟨h8, hT, Formalism.L2.SG.ResidEvFree.residEv_free Fm⟩
  obtain ⟨hC, hA⟩ := hc30 Fm
  have hcb7 := hcb Fm
  have hG := cGam_pos Fm
  obtain ⟨Y1, hY1, HY1⟩ := linear_le_pow_eight_eventually (8 * Fm.CGam) ((c30 Fm.cOut).n0 : ℝ) (by positivity)
  obtain ⟨Y2, -, HY2⟩ := linear_le_pow_eight_eventually ((c30 Fm.cOut).cb * (8 * Fm.CGam)) 8 (by positivity)
  obtain ⟨x4, hx4⟩ := ev_y Fm (max Y1 Y2)
  obtain ⟨x3, hx3⟩ := GlobalTheory.IrrCountEv.hypLine_ev Fm hR
  refine ⟨max x3 x4, fun x hx i => ?_⟩
  obtain ⟨hx1, hAr, hH⟩ := hx3 x (le_trans (le_max_left _ _) hx) i
  have hy := hx4 x (le_trans (le_max_right _ _) hx)
  set y : ℝ := x ^ (eps / 8) with hydef
  have hy1 : 1 ≤ y := le_trans hY1 (le_trans (le_max_left _ _) hy)
  have a1 := HY1 y (le_trans (le_max_left _ _) hy)
  have a2 := HY2 y (le_trans (le_max_right _ _) hy)
  have hLx := scL_eq Fm x hx1 i
  have hk8 := GlobalTheory.IrrCountEv.k_ge_of_hypLine (Fm.L x i) hH
  rw [hLx, Fm.CGam_eq x i] at hk8
  refine GlobalTheory.T.countParameterConditions_of_sizeHypotheses (Fm.D x i) (Fm.L x i) _ _ _ _ _ _ _ (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C
    (c30 Fm.cOut).cb hC hcb7 hA ?_ hCl2 hCl3 ?_ hAr hH
  · have : ((c30 Fm.cOut).n0 : ℝ) ≤ (c30 Fm.cOut).n0 * y := le_mul_of_one_le_right (Nat.cast_nonneg _) hy1
    linarith
  · rw [hLx, Real.log_pow]
    have h1 : Real.log y ≤ y := Real.log_le_self (by linarith)
    have h2 : (c30 Fm.cOut).cb * (8 * Fm.CGam * y ^ 8) ≤ (c30 Fm.cOut).cb * ((Fm.D x i).R.k : ℝ) :=
      mul_le_mul_of_nonneg_left hk8 hcb7.le
    push_cast
    nlinarith

end GlobalTheory.IrrCountEv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof : GlobalTheory.SnFam.FamilyGroupSumFactorsWeightAmplitude := by
  first | exact @GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | exact GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | (intros; apply GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGapStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBesselJFactor_all_words_of_gap : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  first | exact @GlobalTheory.JFactTie.jFactN_all | exact GlobalTheory.JFactTie.jFactN_all | (intros; apply GlobalTheory.JFactTie.jFactN_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  first | exact @GlobalTheory.UnifPTGap.uniformPT_gap | exact GlobalTheory.UnifPTGap.uniformPT_gap | (intros; apply GlobalTheory.UnifPTGap.uniformPT_gap <;> assumption)
end

