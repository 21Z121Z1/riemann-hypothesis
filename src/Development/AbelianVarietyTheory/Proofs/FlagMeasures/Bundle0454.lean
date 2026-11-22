import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0447
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0401
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountIsometryPairsWithGivenFixedSpace
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0284
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0433
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0448
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0450
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0449
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselExteriorPowerConstantBoundLargeGapStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselExteriorPower_constant_bound_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  first | exact @GlobalTheory.GapWedgeKappaL.kappa_bound | exact GlobalTheory.GapWedgeKappaL.kappa_bound | (intros; apply GlobalTheory.GapWedgeKappaL.kappa_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldFiniteAdeleTensorEquivMemIntegralAdelesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFieldFiniteAdeleTensorEquiv_mem_integralAdeles : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E), a ∈ ReciprocityTheory.Aut.ALint D.host.E → GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
  first | exact @GlobalTheory.FixedConj.adeleEquiv_mem_intAf | exact GlobalTheory.FixedConj.adeleEquiv_mem_intAf | (intros; apply GlobalTheory.FixedConj.adeleEquiv_mem_intAf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionMovedLatticeEqLocalCoordinatesStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_moved_lattice_eq_local_coordinates : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (𝓞 D.host.E) (VS D).V), GlobalTheory.LocOver.Ext p σ g → (placesOf Z).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ)) := by
  first | exact @GlobalTheory.HL.placesLat_gcoordLat_eq | exact GlobalTheory.HL.placesLat_gcoordLat_eq | (intros; apply GlobalTheory.HL.placesLat_gcoordLat_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountIsometryPairsWithGivenFixedSpaceStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_isometry_pairs_with_given_fixed_space : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' s n : ℕ) (U : Submodule K V), 1 ≤ x → 1 ≤ x' → 1 ≤ n → Module.finrank K U + s = (Module.finrank K V) → GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L₀) = n → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U}).encard : ℕ∞) : ℝ≥0∞) ≤ if (n : ℝ) ≤ (D₀ : ℝ) * x * x' then ENNReal.ofReal (((2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' / n) ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * cf K + 1) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (3 * (2 * j + 1)) * ((4 * s * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * s * (Formalism.HermitianLatticesTheory.fDeg K))) else 0 := by
  first | exact @GlobalTheory.DegCnt.FixedSpaceCount.main | exact GlobalTheory.DegCnt.FixedSpaceCount.main | (intros; apply GlobalTheory.DegCnt.FixedSpaceCount.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeUnipotentIntegralNormalisedHaarStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_unipotentIntegral_normalisedHaar : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := by
  first | exact @GlobalTheory.CovNFormulaPf.main | exact GlobalTheory.CovNFormulaPf.main | (intros; apply GlobalTheory.CovNFormulaPf.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalHypothesesOfRowsAndWindow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem lemmaPG_record : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg C : ℝ, 40 ≤ Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Glob0 D x eps CD Cg → Nodes D x eps → DuWin D 3 → AdmissibleBoundsFromSource.hyp D large₂ 3 C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ Formalism.L2.SG.RowsConc.TFrameAt D ∧ C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 ∧ C ≤ (D.R.k : ℝ) := by
  intro hSM hDs eps CD heps0 heps1 hCD C' Cl Cg C hCl40 hClCD
  have hCl0 : (0 : ℝ) < Cl := by linarith
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.dataConditions_of_global_and_real_rows eps CD heps0 heps1 hCD
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.hypotheses_of_global_rows_and_nodes eps CD heps0 heps1 hCD C' Cl Cg hCl0 hClCD
  obtain ⟨x3, hx3⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD heps0 heps1 hCD (max C (3 * Real.exp 8))
  refine ⟨max x1 (max x2 x3), ?_⟩
  intro x hx D large₂ hL hC' hTies hAdm hG hN hW
  have hx1' : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2' : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3' : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx

  obtain ⟨-, hAr⟩ := GlobalTheory.T.two_le_rootDiscriminant_and_split_arithmetic_conditions D
  have hData : StandingNumericalData D 3 := hx1 x hx1' D Cg 3 hG hN hAr hW

  obtain ⟨-, -, -, -, -, hm1, hk, hxe⟩ := hx3 x hx3' _ _ _ _ _ hG.nums
  have hxe0 : (0 : ℝ) ≤ x ^ eps := le_of_lt (lt_trans zero_lt_one hxe)
  have h3 : (3 : ℝ) ≤ max C (3 * Real.exp 8) :=
    le_trans (by have := Real.add_one_le_exp (8 : ℝ); linarith) (le_max_right _ _)
  have hCm : C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxe0) hm1
  have h3m : 3 * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right h3 hxe0) hm1
  have h3k : 3 * Real.exp 8 ≤ (D.R.k : ℝ) := le_trans (le_max_right _ _) hk
  have hCk : C ≤ (D.R.k : ℝ) := le_trans (le_max_left _ _) hk

  have hLpos : 0 < large₂.sc.L := by rw [hL]; linarith
  have hb1 : 1 < large₂.sc.b := by
    show 1 < Real.exp large₂.sc.L
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hLpos
  have hb0 : 0 < large₂.sc.b := lt_trans zero_lt_one hb1
  have hm0 : (0 : ℝ) < (D.R.m : ℝ) := by
    have := D.R.two_le_m
    exact_mod_cast (show 0 < D.R.m by omega)
  have hT1 : ∀ u, (1 : ℝ) ≤ Tr D u := fun u => by
    show (1 : ℝ) ≤ ((D.mem u).A.T : ℝ)
    exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hmb : (D.R.m : ℝ) * Real.log large₂.sc.b ≠ 0 := (mul_pos hm0 (Real.log_pos hb1)).ne'
  obtain ⟨CT0, hCT0⟩ : ∃ c : ℝ, c * ((D.R.m : ℝ) * Real.log large₂.sc.b) = ∑ v, Real.log (Tr D v) :=
    ⟨(∑ v, Real.log (Tr D v)) / ((D.R.m : ℝ) * Real.log large₂.sc.b), div_mul_cancel₀ _ hmb⟩
  have hwin0 : ∀ u, large₂.sc.b ^ ((0 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧
      Tr D u ≤ large₂.sc.b ^ (CT0 * (D.R.m : ℝ)) := by
    intro u
    refine ⟨by rw [zero_mul, Real.rpow_zero]; exact hT1 u, ?_⟩
    rw [Real.rpow_def_of_pos hb0,
      show Real.log large₂.sc.b * (CT0 * (D.R.m : ℝ)) = CT0 * ((D.R.m : ℝ) * Real.log large₂.sc.b) by ring, hCT0]
    calc Tr D u = Real.exp (Real.log (Tr D u)) :=
          (Real.exp_log (lt_of_lt_of_le zero_lt_one (hT1 u))).symm
      _ ≤ Real.exp (∑ v, Real.log (Tr D v)) :=
          Real.exp_le_exp.mpr (Finset.single_le_sum (fun v _ => Real.log_nonneg (hT1 v))
            (Finset.mem_univ u))

  have hHyp0 : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 := hx2 x hx2' D large₂ 0 CT0 hL hC' hG hN hwin0
  have hCnt : Cnt.Hyp0 D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 :=
    (⟨hHyp0, hData, by norm_num⟩ : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 ∧ StandingNumericalData D 3 ∧ (1 : ℝ) ≤ 3)

  have hFr := (GlobalTheory.pgFrame_at_record hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm).1
  have hwin := GlobalTheory.T.levelPrimes_size_bounds_columnDimension hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm

  have hHyp : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) :=
    hx2 x hx2' D large₂ (1 / 2) (4 * Cg + 13) hL hC' hG hN hwin
  exact ⟨(⟨hData, hHyp, by norm_num⟩ :
      StandingNumericalData D 3 ∧ StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ (1 : ℝ) ≤ 3), hFr, hCm, hCk⟩

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOnePrimeFrameReducedMatricesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degreeOne_prime_frame_reduced_matrices : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (N p : ℕ) (hN : I.n = N) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)), p.Prime → Nat.card (𝓞 I.E ⧸ w.asIdeal) = p → ∃ fr : GlobalTheory.RowLev.PlFrame I N p w, ∀ k ∈ I.Kset, ∀ M : Matrix (Fin N) (Fin N) (ZMod p), (∀ (i j : Fin N) (hij : ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (Fin.cast hN.symm i) (Fin.cast hN.symm j) ∈ Formalism.L2.Herm.intAf I.F I.E), Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w)) → fr.ActsAs k M := by
  first | exact @GlobalTheory.RowLev.exists_plFrame_of_isFrame | exact GlobalTheory.RowLev.exists_plFrame_of_isFrame | (intros; apply GlobalTheory.RowLev.exists_plFrame_of_isFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRectangularConjInstanceMatrixStandardPsiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rectangular_conj_instanceMatrix_standardPsi : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)), StdPsi hF PY → ∃ (U : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) (U' : Matrix (Fin D.R.r) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧ ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ y))).2) = U * ((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF) * U' := by
  first | exact @GlobalTheory.FixedConjMat.fmat_iota_conj_stdPsi | exact GlobalTheory.FixedConjMat.fmat_iota_conj_stdPsi | (intros; apply GlobalTheory.FixedConjMat.fmat_iota_conj_stdPsi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPoint
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocOver

section MatrixFacts

variable {K : Type*} [Field K] {N : ℕ}

theorem upUni_inv_facts {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) :
    IsUpUni U⁻¹ ∧ U * U⁻¹ = 1 ∧ U⁻¹ * U = 1 := by
  have hbt : U.BlockTriangular id := fun i j hij => (hU i j).1 hij
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl
  have hu : IsUnit U.det := by rw [hdet]; exact isUnit_one
  have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hu
  have h2 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hu
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hbt' : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j => ⟨fun hij => hbt' hij, fun hij => ?_⟩, h1, h2⟩
  subst hij
  have e := congrFun (congrFun h2 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
  · rw [(hU i i).2 rfl, mul_one] at e; simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hbt' h, zero_mul]
    · rw [(hU k i).1 h, mul_zero]
  · simp

theorem loUni_inv_facts {L : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) :
    IsLoUni L⁻¹ ∧ L * L⁻¹ = 1 ∧ L⁻¹ * L = 1 := by
  have hT : IsUpUni L.transpose := fun i j => ⟨fun hij => (hL j i).1 hij, fun hij => by subst hij; simpa using (hL i i).2 rfl⟩
  obtain ⟨h0, -, -⟩ := upUni_inv_facts hT
  have hbt : L.transpose.BlockTriangular id := fun i j hij => (hT i j).1 hij
  have hdet : L.det = 1 := by
    rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hT i i).2 rfl
  have hu : IsUnit L.det := by rw [hdet]; exact isUnit_one
  refine ⟨fun i j => ?_, Matrix.mul_nonsing_inv L hu, Matrix.nonsing_inv_mul L hu⟩
  have e : L⁻¹ i j = (L.transpose)⁻¹ j i := by rw [← Matrix.transpose_nonsing_inv]; rfl
  rw [e]
  exact ⟨fun hij => (h0 j i).1 hij, fun hij => (h0 j i).2 hij.symm⟩

end MatrixFacts

theorem tw_tw {K : Type*} [CommRing K] {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.MainNotions.BridgeLemma₂.rows_tw (Formalism.MainNotions.BridgeLemma₂.rows_tw B) = B := by
  have hs : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1) ^ n) = 1 := by
    intro n; rw [← mul_pow]; simp
  ext i j
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply]
  linear_combination (B i j * (-1) ^ (r - j.val) * (-1) ^ (r - j.val)) * hs (r - i.val) + B i j * hs (r - j.val)

theorem tw_upUni {K : Type*} [CommRing K] {r : ℕ} {B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hB : IsUpUni B) : IsUpUni (Formalism.MainNotions.BridgeLemma₂.rows_tw B) := by
  intro i j
  refine ⟨fun hij => by simp [Formalism.MainNotions.BridgeLemma₂.rows_tw, (hB i j).1 hij], fun hij => ?_⟩
  subst hij
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply, (hB i i).2 rfl, mul_one]
  rw [← mul_pow]; simp

variable {D : D7}

theorem zhatL_chg {T T' : D.host.E} {F F₂ : LFlag (VS D) D.R.rS T} {F₁ F₃ : LFlag (VS D) D.R.rS T'}
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h₂ : Chg (frame F) A (frame F₂)) (h₃ : Chg (frame F₁) A' (frame F₃)) :
    ZhatL F₂ F₃ = A.conjTranspose * ZhatL F F₁ * A' := by
  ext a b
  have e2 : F₂.fl.fvec a = ∑ c, A c a • F.fl.fvec c := h₂ a
  have e3 : F₃.fl.fvec b = ∑ d, A' d b • F₁.fl.fvec d := h₃ b
  simp only [ZhatL, Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e2, e3]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

theorem zhatL_leadMinor {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T')
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E} (hA : Uni A) (hA' : Uni A') (l : ℕ) :
    leadMinorE (A.conjTranspose * ZhatL F F₁ * A') l = leadMinorE (ZhatL F F₁) l := by
  unfold leadMinorE
  split_ifs with hl
  · exact Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant D.host.E _ l hl _ _ _
      (fun i => by simp [Matrix.conjTranspose_apply, hA.2 i])
      (fun i j hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij])
      (fun i => hA'.2 i) (fun i j hij => hA'.1 i j hij)
  · rfl

theorem base_frames_at_point : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → IsInCell (ZhatOM (ZhatL F F₁)) w → (∃ (F00 : LFlag (VS D) D.R.rS T) (F'0 : LFlag (VS D) D.R.rS T'), Tri D.host.E (frame F) (frame F00) ∧ Tri D.host.E (frame F₁) (frame F'0) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w) ∧ ∀ (F₂ : LFlag (VS D) D.R.rS T) (F₃ : LFlag (VS D) D.R.rS T'), Tri D.host.E (frame F) (frame F₂) → Tri D.host.E (frame F₁) (frame F₃) → IsInCell (ZhatOM (ZhatL F₂ F₃)) w ∧ Gval F₂ F₃ = Gval F F₁ := by
  intro D T T' F F₁ w hT hT' hcell
  obtain ⟨L, U, hL, hU, hZ⟩ := hcell
  refine ⟨?_, ?_⟩
  · obtain ⟨hLi, -, hLL⟩ := loUni_inv_facts hL
    obtain ⟨hUi, hUU, -⟩ := upUni_inv_facts hU
    have hA : Uni (L⁻¹).conjTranspose :=
      ⟨fun a b hba => by simp [Matrix.conjTranspose_apply, (hLi b a).1 hba],
        fun a => by simp [Matrix.conjTranspose_apply, (hLi a a).2 rfl]⟩
    have hA'u := tw_upUni hUi
    have hA' : Uni (Formalism.MainNotions.BridgeLemma₂.rows_tw U⁻¹) := ⟨fun a b hba => (hA'u a b).1 hba, fun a => (hA'u a a).2 rfl⟩
    obtain ⟨F00, h00⟩ := (GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F hT).1 _ hA
    obtain ⟨F'0, h'0⟩ := (GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F₁ hT').1 _ hA'
    refine ⟨F00, F'0, ⟨_, hA, h00⟩, ⟨_, hA', h'0⟩, ?_⟩
    rw [zhatL_chg h00 h'0, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ, tw_tw, Matrix.conjTranspose_conjTranspose]
    calc L⁻¹ * (L * ptMat w * U) * U⁻¹ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
  · rintro F₂ F₃ ⟨A, hA, h2⟩ ⟨A', hA', h3⟩
    have hZ2 := zhatL_chg h2 h3
    constructor
    · have hAl : IsLoUni A.conjTranspose := fun i j =>
        ⟨fun hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij],
          fun hij => by subst hij; simp [Matrix.conjTranspose_apply, hA.2 i]⟩
      have hAu : IsUpUni A' := fun i j => ⟨fun hij => hA'.1 i j hij, fun hij => by subst hij; exact hA'.2 i⟩
      refine ⟨A.conjTranspose * L, U * Formalism.MainNotions.BridgeLemma₂.rows_tw A', Formalism.MainNotions.BridgeLemma₂.rows_loUni_mul hAl hL,
        Formalism.MainNotions.BridgeLemma₂.rows_upUni_mul hU (tw_upUni hAu), ?_⟩
      rw [hZ2, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ]
      simp only [Matrix.mul_assoc]
    · show Gflag F₂.fl F₃.fl = Gflag F.fl F₁.fl
      have hD : ∀ l, Dl F₂.fl F₃.fl l = Dl F.fl F₁.fl l := fun l => by
        show leadMinorE (ZhatL F₂ F₃) l = leadMinorE (ZhatL F F₁) l
        rw [hZ2]; exact zhatL_leadMinor F F₁ hA hA' l
      unfold Gflag
      rw [hD, hD]

end GlobalTheory.LocOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticeWeightedCountLeExplicitStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_weightedCount_le_explicit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.L2.SG.Pf.LocCP.LocTied D → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → ∃ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s ∧ (s.Nonempty → (∃ Λ, IsRowLat D (X.Fu u) Λ ∧ G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G')) ∧ glueSum (lf D (X.Fu u)) G' s ≤ 2 * (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
  first | exact @GlobalTheory.GlueCount.glueSum_le | exact GlobalTheory.GlueCount.glueSum_le | (intros; apply GlobalTheory.GlueCount.glueSum_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGapsStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_formalDegree_compactDual_large_gaps : ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      (∃ a, ε a = true) → (∃ a, ε a = false) → Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (Formalism.QuantumDeterminants.fdegHC lam) := by
  first | exact @GlobalTheory.FdegGap.fdeg_gap | exact GlobalTheory.FdegGap.fdeg_gap | (intros; apply GlobalTheory.FdegGap.fdeg_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermAbsoluteVolumeBoundOfVolumeRatioInductionStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermAbsoluteVolumeBound_of_volume_ratio_induction : VolumeStep → AbsoluteVolume := by
  first | exact @GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep | exact GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep | (intros; apply GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep <;> assumption)
end

