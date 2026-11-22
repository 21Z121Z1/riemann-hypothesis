import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0425
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0426
import Formalism.LocalToGlobal.Bundle0002
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0427
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0253
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0059
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0422
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0322
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumDegreeEqMulFormalDegreeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.GapDegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem deg_eq_mul_fdegH : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → (∃ h : ℝ, GapAtLeast (epsSH D.R) lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  intro _ D τ w w' θ W _ hW
  have hμ : PI.BesselPeriodGGP.IsHaarOn (GG D.R.k D.R.rS) W.μG := hW.2.2.2.2.2.2.1
  by_cases hQ : ∃ Q, IsCayley D.R.k D.R.rS (epsSH D.R) Q
  swap
  · refine ⟨1, one_pos, fun lam A hA _ => absurd ?_ hQ⟩
    obtain ⟨P, hP, -⟩ := hA.2.2.2.2.2.2.2.2.2.2
    exact ⟨P, hP⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  obtain ⟨a, ha0, hat, ha⟩ := GlobalTheory.BesselDegree.haar_eq_smul hQd hQ.2 W.μG hμ
  set s : ℝ≥0∞ := ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ≥0∞) with hs
  have hs0 : s ≠ 0 := ENNReal.coe_ne_zero.2 (D.s.cdScale_pos _ _).ne'
  have hst : s ≠ ∞ := ENNReal.coe_ne_top
  have hb0 : a / s ≠ 0 := (ENNReal.div_pos ha0 hst).ne'
  have hbt : a / s ≠ ∞ := (ENNReal.div_lt_top hat hs0).ne
  have hκ : 0 < (a / s).toReal := ENNReal.toReal_pos hb0 hbt
  refine ⟨(a / s).toReal, hκ, fun lam A hA _ v hv => ?_⟩
  obtain ⟨P, hP, hd, hS⟩ := hA.2.2.2.2.2.2.2.2.2.2
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hme : MeasurableEmbedding (phi (epsSH D.R) P) :=
    (phi_closedEmbedding (ε := epsSH D.R) Formalism.REAL.isClosedEmbeddingMatrix hPd).measurableEmbedding
  have hb : W.μG = (a / s) • (s • Formalism.REAL.muG (epsSH D.R)).map (phi (epsSH D.R) P) := by
    rw [Measure.map_smul, smul_smul, ENNReal.div_mul_cancel hs0 hst, GlobalTheory.DegreeTie.map_phi_eq hP hQ]
    exact ha
  have hf : PI.BesselPeriodGGP.fdegH W.μG A.σ v = A.deg / (a / s).toReal := by
    refine Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq (div_pos hd hκ) (fun v w v' w' => ?_) hv
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [hb]
    constructor
    · refine Integrable.smul_measure ?_ hbt
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, A.σ (Matrix.of (phi (epsSH D.R) P g)) v⟫_ℂ *
          star ⟪w', A.σ (Matrix.of (phi (epsSH D.R) P g)) v'⟫_ℂ
          ∂(s • Formalism.REAL.muG (epsSH D.R)) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((A.deg : ℝ) : ℂ) := h2
      rw [h3, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  refine ⟨?_, hd⟩
  rw [hf]
  field_simp

end GlobalTheory.GapDegreeTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedSteps
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

theorem rowMainEqP_of_pinned (hCh : PN.NGChain) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLocGenPinnedG) (hT : StepThmBGP) : GlobalTheory.SnPos.RowMainEqP :=
  GlobalTheory.T.equalWordGenericBound_of_cutBound_positive hCh Formalism.L2.SG.Pf.MainEqCut.meanAmplitudeGeneric_holds
    (GlobalTheory.T.generic_height_bound_of_local_estimates Formalism.L2.SG.NGCut.sizes_of_hypotheses hC hN hP (stepHeightG_of_normOne hO)
      (GlobalTheory.T.analyticGenericBound_of_choiceStep_positive hTi hB (GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps hE hV hL hT)))

example : PN.NGChain → StepClassG → StepNormalsG → StepPointsG → StepNormOneG → TieOfCtx → StepChoiceConstantsC →
    StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → GlobalTheory.SnPos.RowMainEqP :=
  rowMainEqP_of_pinned

end GlobalTheory.SnPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExactRanksAlongTiedFamily
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem exact_ranks_along_tied_family : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (eps : ℝ) (Fm : FamP eps), Formalism.L2.TSelF Fm →
    ∀ C0 Cg cb Cu cT CT : ℝ, PX.RanksF Fm C0 Cg cb Cu cT CT := by
  intro hU eps Fm s C0 Cg cb Cu cT CT
  refine ⟨max s.1 (Fm.x1 + 1), fun x hx i hh => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hx)
  have R := s.2 x hx1 (le_trans (le_max_left _ _) hx) i
  have hr := R.T.theta.real
  have hm : ∀ u, StandardLattice.Mu0Tie (Fm.D x i) u := GlobalTheory.T.rankCondition_of_columns_equal_symmetricLevel _ R.T.cols
  have h4f : StandardLattice.Conclusion4f (Fm.D x i) (Fm.ex x hx1 i).lev :=
    StandardLattice.HarishChandraReduction.rankFormula_of_classNumber _ _ (ColClassNumber.classNumber_all _ _)
  obtain ⟨-, -, -, -, -, -, -, -, hT, -, h0, h1, -⟩ := hh.1
  have hS : ∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j) :=
    Fin.forall_fin_two.2 ⟨RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 0) h0,
      RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 1) h1⟩
  exact exact_ranks_of_record (Fm.D x i) hS (RankVolume.definiteSpaceVolume_eq_mass_of_volumeComparison (fun D => hU D) _ hr)
    (StandardLattice.factDstar_fam Fm x hx1 i)
    (fun u => h4f (first_type_prime_large_of_record _) hS u
      (RankSplit.splitsF_of_norm _ _ ((Fm.D x i).mem u).A.T_prime (hT u).1) (hm u))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalVectorCongruentLocalOrthogonal
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocApprox

theorem iota_gS_typed {D : D7} (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w := by
  obtain ⟨sg, hsg, hq, -⟩ := Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.typed_data Z p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]

end GlobalTheory.LocApprox

namespace GlobalTheory.LocApprox

set_option maxHeartbeats 1000000 in

theorem approx : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O, c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → ∀ {T : D.host.E} (F : LFlag (VS D) D.R.rS T), ∀ x ∈ lattice₂ D Z.M p Λ, x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) → ∃ l ∈ Lrep Λ F, x - baseChange₂ D p l ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))) (lattice₂ D Z.M p Λ) := by
  intro D Z p hc Λ hΛ T F x hx hxp
  have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
  rcases hs : (Z.M p).split with _ | g
  · refine ⟨0, zero_mem _, ?_⟩
    have ht : Formalism.MainNotions.S.LocNG.theta (Z.M p) = 1 := by simp [Formalism.MainNotions.S.LocNG.theta, hs]
    rw [ht, map_one, map_zero, sub_zero]
    exact Submodule.subset_span ⟨x, hx, one_smul _ _⟩
  · have ht : Formalism.MainNotions.S.LocNG.theta (Z.M p) = (g.q : (D.s.atP p).Fp) := by simp [Formalism.MainNotions.S.LocNG.theta, hs]
    obtain ⟨w, hw, he⟩ := iota_gS_typed Z p g hs
    rw [ht]
    have hspan := GlobalTheory.LocExt.perp_le Z p F hxp
    have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (orth (VS D) (Xsp F)) hΛ.fg
    have hxL : x ∈ lattice₂ D Z.M p (Lrep Λ F) := by
      have : x ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) (Xsp F))) : Set (Vp D p)) := by
        rw [hsat]; exact ⟨hx, hspan⟩
      exact this
    clear hx hxp hspan hsat
    induction hxL using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact ⟨l, hl, by rw [sub_self]; exact zero_mem _⟩
    | zero => exact ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
    | add u v _ _ ihu ihv =>
      obtain ⟨l, hl, h⟩ := ihu
      obtain ⟨l', hl', h'⟩ := ihv
      refine ⟨l + l', add_mem hl hl', ?_⟩
      rw [map_add, show u + v - (baseChange₂ D p l + baseChange₂ D p l') = (u - baseChange₂ D p l) + (v - baseChange₂ D p l') by abel]
      exact add_mem h h'
    | smul o v _ ih =>
      obtain ⟨l, hl, h⟩ := ih
      have ho : (o : (D.s.atP p).Ep) ∈ (D.s.atP p).O := hO ▸ o.2
      obtain ⟨a, o', ho', hco⟩ := hc _ ho
      refine ⟨a • l, Submodule.smul_mem _ a hl, ?_⟩
      have hbl : baseChange₂ D p l ∈ lattice₂ D Z.M p Λ := Submodule.subset_span ⟨l, hl.1, rfl⟩
      have e1 : baseChange₂ D p (a • l) = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l := by
        rw [← baseChange_smul₂]; congr 1; exact (algebraMap_smul D.host.E a l).symm
      have key : ∀ (oo ia ig th : (D.s.atP p).Ep) (vv b : Vp D p), oo = ia + ig * o' → ig = th * w →
          oo • vv - ia • b = oo • (vv - b) + th • ((w * o') • b) := by
        intro oo ia ig th vv b h1 h2
        subst h1 h2
        simp only [smul_sub, add_smul, smul_smul, ← mul_assoc]
        abel
      have hov : o • v = (o : (D.s.atP p).Ep) • v := rfl
      have hob : (o : (D.s.atP p).Ep) • (v - baseChange₂ D p l) ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) :=
        Submodule.smul_mem _ o h
      have hwo : w * o' ∈ (Z.M p).L.O := hO ▸ mul_mem hw ho'
      have k1 := key (o : (D.s.atP p).Ep) _ _ _ v (baseChange₂ D p l) hco he
      have h3 : (w * o') • baseChange₂ D p l ∈ lattice₂ D Z.M p Λ := (lattice₂ D Z.M p Λ).smul_mem ⟨_, hwo⟩ hbl
      have h4 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • ((w * o') • baseChange₂ D p l) ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) :=
        Submodule.subset_span ⟨_, h3, rfl⟩
      have h5 : (o : (D.s.atP p).Ep) • v - (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) := by
        rw [k1]; exact add_mem hob h4
      have h6 : o • v - baseChange₂ D p (a • l) = (o : (D.s.atP p).Ep) • v - (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l := by
        rw [hov, e1]
      rw [h6]
      exact h5

end GlobalTheory.LocApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGoodLocalDatumOfNonzeroPeriodsGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DatumOfPeriodsGap

theorem exists_goodS : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDG (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  intro hH D τ w w' θ W lam R _ l l' dd _ _ hRG hl hl' hdd hn hn'
  have hK : PI.KFinSmooth := hH.1.1.2.2.1
  have hR : R.IsDS (epsSH D.R) lam := GlobalTheory.isDS_of_isDG hRG
  obtain ⟨P, hP, hD⟩ := hR.2
  have hD' : Formalism.MainNotions.S.IsDS (epsSH D.R) lam (fun g => R.σ (P⁻¹ * g * P)) := hD
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ hD' _ (D.s.cdScale_pos _ (epsSH D.R))
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hD'
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hvs : v ∈ R.sm :=
    ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK _ _ _ lam R hR P hP S hS.1 hS.2.1).1 v hvS).2
  refine ⟨{ H := R.H, σ := R.σ, B := fun x => ((Real.sqrt (Module.finrank ℂ W.Wp : ℕ) : ℝ) : ℂ) • l x,
            B' := fun x => ((Real.sqrt (Module.finrank ℂ W.Wq : ℕ) : ℝ) : ℂ) • l' x,
            v0 := v, cN := ‖v‖ ^ 2 / dd, deg := d },
    hR.1, hR.2, GlobalTheory.DatumOfPeriods.isBesselMapSm_smul hl _, GlobalTheory.DatumOfPeriods.isBesselMapSm_smul hl' _, hvs, hv0,
    ⟨P, hP, ?_⟩, div_pos (pow_pos (norm_pos_iff.2 hv0) 2) hdd,
    GlobalTheory.DatumOfPeriods.l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn v hvs), GlobalTheory.DatumOfPeriods.l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn' v hvs),
    P, hP.1, hd⟩
  exact (le_sSup (s := {S | IsKTypeOf (epsSH D.R) (fun g => R.σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (epsSH D.R) lam) S}) hS) hvS

end GlobalTheory.DatumOfPeriodsGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFinCoefTorusNe
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapAmpTK

open GlobalTheory.AmpTK

theorem exists_kFinCoef_torus_ne : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro H k r L l l' κ τ hκ hτ hl hl' hxe hye
  have hK : PI.KFinSmooth := H.1.1.2.2.1
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, L.hσ⟩
  obtain ⟨hmul0, hone0, hinn0, hsm0, hTKsm0, hTKg0, hKT0, -, -⟩ :=
    GlobalTheory.rep_basic_of_isDS hK k r L.ε L.lam (rep L) hDS
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v : L.Hs, L.σ (g * h) v = L.σ g (L.σ h v) := hmul0
  have hone : ∀ v : L.Hs, L.σ 1 v = v := hone0
  have hinn : ∀ g ∈ BranchingSupport.GG k r, ∀ v w : L.Hs, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := hinn0
  have hR : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) (rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  have hd : Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH hκ hτ
  have hdi : Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH hκ hτ
  have hddi : ∀ v : L.Hs, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) v) = v := by
    intro v
    rw [← hmul _ hd _ hdi, Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ, hone]
  have side : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (m : L.Hs → V),
      SmCW L m → (∃ x ∈ (rep L).TK, m x ≠ 0) →
      ∃ x₀ : L.Hs, (rep L).KFin x₀ ∧ m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) ≠ 0 := by
    intro V _ _ _ m hm ⟨x, hxT, hx⟩
    haveI := FiniteDimensional.complete ℂ V
    refine GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r L.ε L.lam (rep L) hDS V
      (fun v => m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v)) ?_ ?_ ?_ ?_
    · intro v hv w hw
      exact (congrArg m (map_add (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) v w)).trans
        (hm.1 _ (hsm0 _ hd _ hv) _ (hsm0 _ hd _ hw))
    · intro a v hv
      exact (congrArg m (map_smul (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) a v)).trans (hm.2.1 _ _ (hsm0 _ hd _ hv))
    · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hd) hm.2.2
    · refine ⟨L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) x, hsm0 _ hdi _ (hTKsm0 _ hxT), ?_⟩
      exact fun h0 => hx ((congrArg m (hddi x)).symm.trans h0)
  obtain ⟨x₀, hx₀, hx₀'⟩ := side l hl hxe
  obtain ⟨y₀, hy₀, hy₀'⟩ := side l' hl' hye
  set ξ := l (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) with hξ
  set ξ' := l' (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀) with hξ'
  let P : L.Hs →L[ℂ] L.Wp := (innerSL ℂ x₀).smulRight ξ
  let Q : L.Wq →L[ℂ] L.Hs := (innerSL ℂ ξ').smulRight y₀
  let X : L.Wq →L[ℂ] L.Wp := (innerSL ℂ ξ').smulRight ξ
  have hP : ∀ v, P v = ⟪x₀, v⟫_ℂ • ξ := fun v => rfl
  have hQ : ∀ w, Q w = ⟪ξ', w⟫_ℂ • y₀ := fun w => rfl
  have hX : ∀ w, X w = ⟪ξ', w⟫_ℂ • ξ := fun w => rfl
  refine ⟨fun g => P.comp ((L.σ g).comp Q), ⟪ξ, X ξ'⟫_ℂ, ⟨P, Q, ?_, ?_, fun g => rfl⟩, ?_, ?_⟩
  · intro w
    obtain ⟨S, hS, hyS, hSK⟩ := hy₀
    refine ⟨S, hS, ?_, hSK⟩
    rw [hQ]
    exact S.smul_mem _ hyS
  · intro v
    have hadj : ContinuousLinearMap.adjoint P v = ⟪ξ, v⟫_ℂ • x₀ := by
      apply ext_inner_right ℂ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hP, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    rw [hadj]
    obtain ⟨S, hS, hxS, hSK⟩ := hx₀
    exact ⟨S, hS, S.smul_mem _ hxS, hSK⟩
  · refine ⟨1, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀,
      fun _ => X, fun _ => ⟨hTKg0 _ hd _ (hKT0 _ hx₀), hTKg0 _ hd _ (hKT0 _ hy₀)⟩, ?_, ?_⟩
    · intro g hg
      have key : L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ g) =
          (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ)).comp ((L.σ g).comp (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ))) := by
        ext v
        show L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ * g * Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v = _
        rw [hmul _ (GlobalTheory.BesselMove.mul_mem' hdi hg) _ hd, hmul _ hdi _ hg]
        rfl
      have key2 : ∀ u, ⟪x₀, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u⟫_ℂ =
          ⟪L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, u⟫_ℂ := by
        intro u
        rw [← hinn _ hd x₀ (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u), hddi]
      ext w
      simp only [Fin.sum_univ_one, ContinuousLinearMap.comp_apply, key, ContinuousLinearMap.smul_apply, hP, hQ, hX,
        map_smul, key2, inner_smul_right, smul_smul, mul_comm]
      exact congrArg (fun c : ℂ => c • ξ) (mul_comm _ _)
    · simp only [Fin.sum_univ_one]
      rfl
  · rw [hX, inner_smul_right]
    exact mul_ne_zero (inner_self_ne_zero.2 hy₀') (inner_self_ne_zero.2 hx₀')

end GlobalTheory.GapAmpTK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLatticeOfUnimodularLandherrStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormalLattice_of_unimodular_landherr : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) := by
  first | exact @GlobalTheory.Mass.exists_orthoLattice_of_unimodular | exact GlobalTheory.Mass.exists_orthoLattice_of_unimodular | (intros; apply GlobalTheory.Mass.exists_orthoLattice_of_unimodular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowOfUnimodularLatticePrimitiveVector
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.RowsOrb.exists_row_of_unimod : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) → ∃ Λ ∈ Y.what₂ u, ∃ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ = L := by
  intro D large₂ X Y u hStd L hL hU hprim
  obtain ⟨hlat, hun⟩ := GlobalTheory.RowsOrb.Glue.glue_isLattice_unimodular D large₂ X hStd L hL hU
  have hgen := GlobalTheory.RowsOrb.ExGenus.mem_genus_of_isUnimodular D large₂ hStd X u _ hlat hun
  obtain ⟨hx, hx0, hlm, hsub⟩ := GlobalTheory.RowsOrb.parts_of_lat D X u L
  have hzL : GlobalTheory.RowsOrb.zb X u ∈ L := by
    have h1 := (hprim 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rwa [one_smul] at h1
  have hzΛ : X.zu u ∈ latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY := by
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact ⟨GlobalTheory.RowsOrb.zb X u, hzL, rfl⟩
  have hfix0 := (X.Fu_fixed u).2.2.2.1
  have hlf : (lf D (X.Fu u)) = (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) := by
    show (⟨X.Fu u, (X.Fu u).z⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS _) = _
    rw [X.flagZVector u]
  have hfix : FixedHyp D (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
    refine ⟨hlat, hun, ⟨?_, rfl⟩, ?_, ?_⟩
    · show (X.Fu u).z ∈ _
      rw [X.flagZVector u]; exact hzΛ
    · intro P
      rw [hx]
      rw [← hx0, hlf]
      exact hfix0 P
    · intro c hc
      have hc' : ((c • GlobalTheory.RowsOrb.zb X u : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
        rw [Submodule.coe_smul, GlobalTheory.RowsOrb.zb_coe, ← X.flagZVector u]; exact hc
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((hprim c).1 (hsub _ hc'))
      exact ⟨o, ho⟩
  have hrow : IsRowLat D (X.Fu u) (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := ⟨hgen, hfix, hx⟩
  obtain ⟨Λ', ⟨hΛ', γ, hγ, hmap⟩, -⟩ := (Y.rowsOK u).2 _ hrow
  obtain ⟨g, hg⟩ := GlobalTheory.RowsOrb.exists_gz_lmap D X u γ hγ
  exact ⟨Λ', hΛ', g, by rw [hg, hmap, hlm]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypotheses
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapSetup

theorem isFamG_of_num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) :
    IsFamG lam q0 R := by
  have H := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  intro ν hν
  have hd := hF ν hν
  exact ⟨hd.1, hd.2, ⟨h / 2, (H.2 ν hν).2.2.1, H.1.2.2.2.2⟩⟩

theorem families_gap : (∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → IsFamG lam q0 R) ∧ ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg ↔ SetupG lam u b bv ga h q0 z π μW μN μG νq R lb dg := by
  refine ⟨isFamG_of_num, ?_⟩
  intro k r Wp _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg
  constructor
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, isFamG_of_num k r lam u b bv ga h q0 R hN hF, hS, hSF⟩
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, fun ν hν => GlobalTheory.isDS_of_isDG (hF ν hν), hS, hSF⟩

end GlobalTheory.GapSetup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameGramMulEqConjTransposeMulFrameMatrices
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.ZxMul

theorem zx_mul : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (g γ h : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (C B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat (g⁻¹ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) C → GlobalTheory.LoopAct.IsMatOn (uMat (h v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) B → Formalism.L2.SG.RealObj.ZX X u u' 1 (g * γ * h) v = Cᴴ * Formalism.L2.SG.RealObj.ZX X u u' 1 γ v * B := by
  intro D X u u' g γ h v C B hC hB
  have hU : (uMat (g⁻¹ v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (g⁻¹ v) = Formalism.REAL.Jm (X.B.I.ε v) := (g⁻¹ v).2
  have e : uMat ((g * γ * h) v) = uMat (g v) * uMat (γ v) * uMat (h v) := rfl
  have hL : ∀ a, uMat (g⁻¹ v) *ᵥ Formalism.L2.SG.RealObj.frm X u 1 v a =
      ∑ c, Cᵀ a c • Formalism.L2.SG.RealObj.frm X u 1 v c := fun a => by
    rw [hC a]; rfl
  have hM : ∀ b, uMat (h v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b =
      ∑ d, Bᵀ b d • Formalism.L2.SG.RealObj.frm X u' 1 v d := fun b => by
    rw [hB b]; rfl
  unfold Formalism.L2.SG.RealObj.ZX
  rw [e, GlobalTheory.GxConj.zhat_conj _ _ _ _ _ _ _
    (GlobalTheory.GxConj.hJ_adj _ _ _ hU (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (g v))) _ _ hL hM,
    Matrix.transpose_transpose]
  rfl

end GlobalTheory.ZxMul
end
end

