import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0486
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Formalism.LocalToGlobal.Bundle0002
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0456
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0463
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TcritLowOfDsig
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0006
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0429
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0462
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0436
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0480

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IrreducibilityRowOfConcreteAutomorphicDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibilityRow_of_concreteAutomorphicData : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∃ cIc : ℝ, 0 < cIc ∧ ∀ 𝒞 : FamClass, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => 𝒞 Fm → ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, ∃ (X : HidaSetting (Fm.D x i)) (G : GoodOp X) (ι : (Fm.D x i).s.HH ≃ₗᵢ[ℂ] HHX X), AutTie (Fm.D x i) X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i), LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) := by
  first | exact @GlobalTheory.IrrRowConcrete.irr_row_closed | exact GlobalTheory.IrrRowConcrete.irr_row_closed | (intros; apply GlobalTheory.IrrRowConcrete.irr_row_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowBoundsAlongFamilyLargeGaps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.L2.SG.RowsU

noncomputable section

namespace GlobalTheory.LoopRowBoundsGap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 cV CGam : ℝ, ∃ C₀ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), Fm.CGam = CGam → thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) ∧ ∀ (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1), rows_TiesF Fm C1 X Y → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u')) → (∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') → (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A cV) → ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧ RowsOne (X x hx i) (Y x hx i u u') C := by
  intro hSMR hH hBp Cg cb Cu cT CT C0 A C1 cV CGam
  obtain ⟨c3, cH, cS, c4, thr1, HC⟩ := GlobalTheory.T.rowCounts_uniform_constants_families hSMR Cg cb Cu cT CT C0 A
  obtain ⟨Ca, C2, Ch, thr2, hCa, hCh, HA⟩ := GlobalTheory.T.amplitude_bounds_uniform_large_gap_families hSMR hH hBp Cg cb Cu cT CT C0 A C1
  let U : UC := ⟨c3, cH, cV, cS, c4, fun _ => Ca, fun _ => C2, fun _ => Ch⟩
  refine ⟨c0U CT A C0 CGam U, max 40 (max thr1 thr2), fun eps Fm hG hs hl hR => ?_⟩
  have hs1 : thr1 ≤ sC' Fm := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hl1 : thr1 ≤ sCl Fm := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hs2 : thr2 ≤ sC' Fm := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hl2 : thr2 ≤ sCl Fm := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have h40 : 40 ≤ sCl Fm := (le_max_left _ _).trans hl
  have h3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm := fun x _ i u => GlobalTheory.T.rows_raw_mass_and_genus_mass (Fm.D x i) u
  obtain ⟨a10a, a6, a7, a8, a10b, hform⟩ :=
    GlobalTheory.CritLevelGap.along_family hH.2.2.2 eps Fm Cg cb Cu cT CT C0 A h40 hR h3
  refine ⟨hform, fun X Y hT hTI hBL hVol C hC => ?_⟩
  obtain ⟨LocalHeightDeterminant, H27, H4, H21⟩ := HC eps Fm hs1 hl1
  have hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U :=
    ⟨LocalHeightDeterminant, H27, hVol, H4, H21, fun Cpr => ⟨hCh, hCa, fun δ hδ => HA eps Fm hs2 hl2 hR Cpr δ hδ⟩⟩
  exact GlobalTheory.T.admissible_family_satisfies_row_estimates eps Fm C1 X Y Cg cb Cu cT CT C0 A a10a a6 a7 a8 a10b hT hTI hBL U hU C (by rw [hG]; exact hC)

end GlobalTheory.LoopRowBoundsGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMainEqPOfSiegelWeilConstants
section
namespace GlobalTheory

theorem rowMainEqP_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.Pf.BDat.StepThmBG → Formalism.L2.SG.RowsPos.RowMainEqP := by
  intro h hB hT
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _h8, h9⟩ := GlobalTheory.T.equalWords_nonGeneric_estimates_chain
  refine GlobalTheory.T.equalWordGenericBound_of_normalisedSteps h1 h2 GlobalTheory.T.normalCount_genericRow h3 h4 h5 hB h6 h7 (h9 (GlobalTheory.T.genericFamilyStep_of_siegelWeil (GlobalTheory.St.swxs_of_siegelWeil h))) ?_
  intro Cg cb Cw cT CT C0 _ _ A
  obtain ⟨CB, h0, a, b, H⟩ := hT Cg cb Cw cT CT C0 A
  exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u _ => H C' Cl h1 h2 D large₂ X Y u⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeilConstants
section
namespace GlobalTheory

theorem rowNGP_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.NGAnalytic.StepThmBPinnedC → Formalism.L2.SG.RowsPos.RowNGP := by
  intro h hB hT
  refine GlobalTheory.T.corankOneNonGenericRowBound_closed (GlobalTheory.St.swxs_of_siegelWeil h) hB GlobalTheory.stepPinExists_and_formNGC.1 GlobalTheory.stepPinExists_and_formNGC.2 ?_
  intro Cg cb Cw cT CT C0 _ _ A
  obtain ⟨CB, h0, a, b, H⟩ := hT Cg cb Cw cT CT C0 A
  exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u u' _ => H C' Cl h1 h2 D large₂ X Y u u'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsPosTypeP
section
namespace GlobalTheory

theorem rowsPos_typeP : Formalism.L2.SG.RowsPos.TypeP :=
  GlobalTheory.T.typeBound_of_largeGap_discreteSeries_bessel (GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.1) GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.2

end GlobalTheory
end

