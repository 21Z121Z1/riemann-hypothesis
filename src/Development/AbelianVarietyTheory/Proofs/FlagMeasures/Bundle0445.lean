import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0440
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0441
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0442
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegerPointsCoverRealPointsRootCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0433
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIota
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Development.AbelianVarietyTheory.Counterexamples.TransversalityLocal.FramePairFixatorUnitaryAndFixesFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqSmulNormalisedAmplitudeLargeGapStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_eq_smul_normalisedAmplitude_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  first | exact @GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap | exact GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap | (intros; apply GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypothesesStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeLocalData_momentPieriHypotheses : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  first | exact @GlobalTheory.Amp.LocalSetupGap.exists_setup_both | exact GlobalTheory.Amp.LocalSetupGap.exists_setup_both | (intros; apply GlobalTheory.Amp.LocalSetupGap.exists_setup_both <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudePieriRelevantCellLargeGapStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_pieri_relevantCell_largeGap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  first | exact @GlobalTheory.CellPieriG.amp_pieri | exact GlobalTheory.CellPieriG.amp_pieri | (intros; apply GlobalTheory.CellPieriG.amp_pieri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapMultipleIsometryLargeGapStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselMap_multipleIsometry_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), 1000 ≤ Cl → (∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → 0 < θ) → (∀ w, 0 < Tr D w) → BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  first | exact @GlobalTheory.BesselSchurGap.bessel_schur | exact GlobalTheory.BesselSchurGap.bessel_schur | (intros; apply GlobalTheory.BesselSchurGap.bessel_schur <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapsLargeGapPeriodIdentitiesStatement
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_besselMaps_largeGap_periodIdentities : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → 0 < L.κN → L.κN ≠ ⊤ → ∃ (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), GlobalTheory.AmpTK.BeTK L l l' ∧ GlobalTheory.AmpTK.SmCW L l ∧ GlobalTheory.AmpTK.SmCW L l' := by
  first | exact @GlobalTheory.AmpTKGap.exists_besselTK | exact GlobalTheory.AmpTKGap.exists_besselTK | (intros; apply GlobalTheory.AmpTKGap.exists_besselTK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowTermOfLocalCompletionsTermsStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowTerm_of_local_completions_terms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ t : TauC Y u u', TG F F' t Λ := by
  first | exact @GlobalTheory.RowTermReal.exists_term_of_locOver | exact GlobalTheory.RowTermReal.exists_term_of_locOver | (intros; apply GlobalTheory.RowTermReal.exists_term_of_locOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianSumStabiliserUnfoldingStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianSum_stabiliserUnfolding : GaugeUnfold := by
  first | exact @GlobalTheory.StabUnfold.gaugeUnfold | exact GlobalTheory.StabUnfold.gaugeUnfold | (intros; apply GlobalTheory.StabUnfold.gaugeUnfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermVolumeRatioSameKindOfVolumeRatioInductionStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction : VolumeStep → VolumeRatio := by
  first | exact @GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep | exact GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep | (intros; apply GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegerPointsCoverRealPointsRootCoordinatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integerPoints_cover_realPoints_rootCoordinates : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (γw sf s' : X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → sf ∈ X.SinfU u → s' ∈ X.SinfU u' → s.pt.1 = sf * γw * s'⁻¹ → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → ∃ T : (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ) → (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasureTheory.MeasurePreserving T MeasureTheory.volume MeasureTheory.volume ∧ ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃ q ∈ Formalism.L2.SG.TermOp.ROinf s, T (GlobalTheory.LoopVol.ratCoord X u' w γw sf (q * r)) ∈ Ω := by
  first | exact @GlobalTheory.LoopVol.cover_action | exact GlobalTheory.LoopVol.cover_action | (intros; apply GlobalTheory.LoopVol.cover_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelPrimesSizeBoundsColumnDimension
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem levelPrime_size : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → C0 * Real.exp 8 ≤ D.R.k → LocalBesselAndTopKernel.FamilyMidVolume D → ∀ u, large₂.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m : ℝ)) := by
  intro hS hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl hCu hC0 hR u
  obtain ⟨hF, hA, -, hk⟩ := pgFrame_at_record hS hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl hCu hC0 hR
  have hcrit := GlobalTheory.T.criticalLevel_le_pow_allPlaces hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl
  obtain ⟨hS0, hData, hC01⟩ := hH
  dsimp only [StandingHypotheses] at hS0
  obtain ⟨-, -, hm4, hfk, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, hv, -, -, -, -, hClm, -⟩ := hS0
  have hwin := (hData.2.2.2.2.2.2.2.2.2.1 u).2

  have hLpos : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hb : 1 < large₂.sc.b := by
    have := Real.add_one_le_exp large₂.sc.L
    show 1 < Real.exp large₂.sc.L
    linarith
  have hbpos : 0 < large₂.sc.b := by linarith
  have hm40 : (40:ℝ) ≤ D.R.m := le_trans hCl hClm
  have hmk : ((D.R.m + 3 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  push_cast at hmk
  have hk40 : (40:ℝ) ≤ D.R.k := by linarith
  have hkpos : (0:ℝ) < D.R.k := by linarith
  have hfpos : (0:ℝ) < D.R.f := by
    have h1 : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_trans h1 hm4)
  have hfk' : (D.R.f:ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hrS : 2 * D.R.rS + 2 = D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    omega

  have hkb : 0 < (D.R.k:ℝ) * large₂.sc.b := mul_pos hkpos hbpos
  have hgg : ((D.R.k:ℝ) * large₂.sc.b) ^ 16 ≤ gg D := by
    show _ ≤ (D.host.g 0 : ℝ) * D.host.g 1
    have h0 : 0 ≤ ((D.R.k:ℝ) * large₂.sc.b) ^ 8 := (pow_pos hkb 8).le
    calc ((D.R.k:ℝ) * large₂.sc.b) ^ 16 = ((D.R.k:ℝ) * large₂.sc.b) ^ 8 * ((D.R.k:ℝ) * large₂.sc.b) ^ 8 := by ring
      _ ≤ _ := mul_le_mul hg1 hg2 h0 (le_trans h0 hg1)
  have hggpos : 0 < gg D := lt_of_lt_of_le (pow_pos hkb 16) hgg

  have hka_pos : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
  have hka_le : D.host.ka ≤ 4 := by
    show Real.pi / D.host.v ≤ 4
    rw [div_le_iff₀ (by linarith)]
    linarith [Real.pi_le_four]
  have hK_pos : 0 < Bridge.kaS D := div_pos hka_pos hggpos
  have hK : Bridge.kaS D * large₂.sc.b ^ 16 ≤ 1 := by
    show D.host.ka / gg D * large₂.sc.b ^ 16 ≤ 1
    rw [div_mul_eq_mul_div, div_le_one hggpos]
    have hk16 : (D.R.k:ℝ) ≤ (D.R.k:ℝ) ^ 16 := le_self_pow₀ (by linarith) (by norm_num)
    have hb16 : 0 ≤ large₂.sc.b ^ 16 := (pow_pos hbpos 16).le
    calc D.host.ka * large₂.sc.b ^ 16 ≤ 4 * large₂.sc.b ^ 16 := mul_le_mul_of_nonneg_right hka_le hb16
      _ ≤ (D.R.k:ℝ) ^ 16 * large₂.sc.b ^ 16 := mul_le_mul_of_nonneg_right (by linarith) hb16
      _ = ((D.R.k:ℝ) * large₂.sc.b) ^ 16 := by ring
      _ ≤ gg D := hgg
  unfold Formalism.L2.SG.RowsConc.TFrameAt at hF
  have hT0 : 0 ≤ Tr D u := Nat.cast_nonneg _
  have hlow : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ Tr D u := by
    have h1 := hF u
    have h2 : (Bridge.kaS D * large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ 1 :=
      pow_le_one₀ (mul_pos hK_pos (pow_pos hbpos 16)).le hK
    rw [mul_pow] at h2
    have hP : 0 ≤ (large₂.sc.b ^ 16) ^ (2 * D.R.rS) := (pow_pos (pow_pos hbpos 16) _).le
    have e : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) * (Tr D u * Bridge.kaS D ^ (2 * D.R.rS)) =
        Tr D u * (Bridge.kaS D ^ (2 * D.R.rS) * (large₂.sc.b ^ 16) ^ (2 * D.R.rS)) := by ring
    linarith [mul_le_mul_of_nonneg_left h1 hP, mul_le_mul_of_nonneg_left h2 hT0]
  refine ⟨le_trans ?_ hlow, ?_⟩
  · rw [← pow_mul, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb.le
    have : ((2 * D.R.rS + 2 : ℕ) : ℝ) = D.R.m := by exact_mod_cast hrS
    push_cast at this ⊢
    linarith
  ·
    by_contra hup
    push Not at hup
    have hbm : 0 < large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := Real.rpow_pos_of_pos hbpos _
    have hTpos : 0 < Tr D u := lt_trans hbm hup
    obtain ⟨q, hq⟩ : ∃ q, q = large₂.sc.b ^ (-(D.R.m:ℝ)) := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := by rw [hq]; exact (Real.rpow_pos_of_pos hbpos _).le
    have hq1 : q ≤ 1 := by
      rw [hq]; exact (Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)).le
    have hq_eq : large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m:ℝ)) = q * large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := by
      rw [hq, ← Real.rpow_add hbpos]; congr 1; ring
    have hgg0 : 0 ≤ gg D := hggpos.le
    have hTc_pos : ∀ τ, 0 < Tcrit D u τ := by
      intro τ
      have h := hk u τ
      have h1 : (0:ℝ) < (D.R.k:ℝ) ^ (3 * D.R.rS) := pow_pos hkpos _
      by_contra hc
      push Not at hc
      have : gg D ^ (-(D.R.m:ℝ)) * Tcrit D u τ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hgg0 _) hc
      linarith
    have hxpos : ∀ τ, 0 < Tcrit D u τ / Tr D u := fun τ => div_pos (hTc_pos τ) hTpos
    have hx : ∀ τ, Tcrit D u τ / Tr D u ≤ q := by
      intro τ
      rw [div_le_iff₀ hTpos]
      calc Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m:ℝ)) := hcrit u τ
        _ = q * large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := hq_eq
        _ ≤ q * Tr D u := mul_le_mul_of_nonneg_left hup.le hq0
    have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
    obtain ⟨τ0⟩ := hTau
    classical
    have hprod : ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k ≤ q ^ D.R.k := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ0)]
      have hrest : ∏ τ ∈ Finset.univ.erase τ0, (Tcrit D u τ / Tr D u) ^ D.R.k ≤ 1 :=
        Finset.prod_le_one (fun τ _ => pow_nonneg (hxpos τ).le _)
          (fun τ _ => pow_le_one₀ (hxpos τ).le (le_trans (hx τ) hq1))
      calc (Tcrit D u τ0 / Tr D u) ^ D.R.k * ∏ τ ∈ Finset.univ.erase τ0, (Tcrit D u τ / Tr D u) ^ D.R.k
          ≤ (Tcrit D u τ0 / Tr D u) ^ D.R.k * 1 :=
            mul_le_mul_of_nonneg_left hrest (pow_nonneg (hxpos τ0).le _)
        _ ≤ q ^ D.R.k := by rw [mul_one]; exact pow_le_pow_left₀ (hxpos τ0).le (hx τ0) _
    have hP0 : 0 < ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k :=
      Finset.prod_pos (fun τ _ => pow_pos (hxpos τ) _)
    unfold UnitaryVolumeMass.cTvA at hA
    obtain ⟨hlo, hhi⟩ := hA u
    have hQ : 0 < D.what₂.Dstar / (D.duS u : ℝ) := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hP0) hlo
    have hd : 0 < (D.duS u : ℝ) := by
      rcases (Nat.cast_nonneg (D.duS u) : (0:ℝ) ≤ _).eq_or_lt with h | h
      · rw [← h, div_zero] at hQ
        exact absurd hQ (lt_irrefl 0)
      · exact h
    have hDs : 0 < D.what₂.Dstar := by
      have := mul_pos hQ hd
      rwa [div_mul_cancel₀ _ hd.ne'] at this
    have hC0pos : 0 < C0 := by linarith

    have hlogG : 0 < Real.log (D.mem u).A.GamP := by
      rw [large₂.Gam_eq u]
      have hL0 : 0 < large₂.sc.L := by linarith
      have hm0 : (0:ℝ) < D.R.m := by linarith
      exact mul_pos (mul_pos (mul_pos large₂.CGam_pos (pow_pos hm0 5)) hfpos) hL0
    have hG0 : (D.mem u).A.GamP ≠ 0 := by
      intro h
      rw [h, Real.log_zero] at hlogG
      exact lt_irrefl 0 hlogG
    have hGabs : 1 < |(D.mem u).A.GamP| := by
      rw [← Real.exp_log_eq_abs hG0]
      have := Real.add_one_le_exp (Real.log (D.mem u).A.GamP)
      linarith
    have hGz : (D.mem u).A.GamP ^ (-2:ℤ) ≤ 1 := by
      rw [zpow_neg, zpow_two]
      apply inv_le_one_of_one_le₀
      rw [← abs_mul_abs_self (D.mem u).A.GamP]
      exact (one_lt_mul_of_lt_of_le hGabs hGabs.le).le
    have hwin' : (D.duS u : ℝ) ≤ 1 * D.what₂.Dstar * C0 :=
      le_trans hwin (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGz hDs.le) hC0pos.le)
    have hinv : 1 / C0 ≤ D.what₂.Dstar / (D.duS u : ℝ) :=
      (div_le_div_iff₀ hC0pos hd).mpr (by linarith)

    have h2pow : (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ 8 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith : (3:ℝ) - D.R.k ≤ 3)
      have h8 : (2:ℝ) ^ (3:ℝ) = 8 := by
        rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      linarith
    have hexp1 : (D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ 8 * D.R.k := by
      calc (D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ (D.R.f:ℝ) * 8 := mul_le_mul_of_nonneg_left h2pow hfpos.le
        _ ≤ 8 * D.R.k := by linarith
    have hqk : q ^ D.R.k = Real.exp (-((D.R.k:ℝ) * large₂.sc.L * D.R.m)) := by
      rw [hq, show large₂.sc.b = Real.exp large₂.sc.L from rfl, ← Real.exp_mul, ← Real.exp_nat_mul]
      congr 1
      ring
    have hLm : (40:ℝ) * D.R.k ≤ (D.R.k:ℝ) * large₂.sc.L * D.R.m := by
      have h40 : (1:ℝ) * 40 ≤ large₂.sc.L * D.R.m := mul_le_mul hLpos.le hm40 (by norm_num) (by linarith)
      rw [mul_assoc]
      linarith [mul_le_mul_of_nonneg_left h40 hkpos.le]
    have hmain : 1 / C0 ≤ Real.exp (-(32 * (D.R.k:ℝ))) := by
      calc 1 / C0 ≤ D.what₂.Dstar / (D.duS u : ℝ) := hinv
        _ ≤ Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k)) * ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k := hhi
        _ ≤ Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k)) * q ^ D.R.k :=
            mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
        _ = Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) - (D.R.k:ℝ) * large₂.sc.L * D.R.m) := by
            rw [hqk, ← Real.exp_add]
            ring_nf
        _ ≤ Real.exp (-(32 * (D.R.k:ℝ))) := Real.exp_le_exp.mpr (by linarith)
    have hC0k : C0 ≤ D.R.k := by
      have h8 := Real.add_one_le_exp 8
      calc C0 = C0 * 1 := (mul_one C0).symm
        _ ≤ C0 * Real.exp 8 := mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
        _ ≤ D.R.k := hC0
    have hkexp : (D.R.k:ℝ) + 1 ≤ Real.exp D.R.k := Real.add_one_le_exp _
    have h31 : Real.exp (-(31 * (D.R.k:ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hsplit : Real.exp (D.R.k:ℝ) * Real.exp (-(32 * (D.R.k:ℝ))) = Real.exp (-(31 * (D.R.k:ℝ))) := by
      rw [← Real.exp_add]
      ring_nf
    have he32 : 0 < Real.exp (-(32 * (D.R.k:ℝ))) := Real.exp_pos _
    have h1C : 1 ≤ C0 * Real.exp (-(32 * (D.R.k:ℝ))) := by
      rw [div_le_iff₀ hC0pos] at hmain
      linarith
    have e : ((D.R.k:ℝ) + 1) * Real.exp (-(32 * (D.R.k:ℝ))) =
        (D.R.k:ℝ) * Real.exp (-(32 * (D.R.k:ℝ))) + Real.exp (-(32 * (D.R.k:ℝ))) := by ring
    linarith [mul_le_mul_of_nonneg_right hC0k he32.le, mul_le_mul_of_nonneg_right hkexp he32.le]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalGlobalCongruenceLatticeTypedPlace
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IotaLocGlob

open Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : D7}

theorem bcP_osmul (p : PlF D) (a : 𝓞 D.host.E) (y : (VS D).V) :
    baseChange₂ D p (a • y) = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]

theorem smulLat_le (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') :
    (locH Z p).smulLat (algebraMap _ _ (Formalism.MainNotions.S.LocNG.theta (Z.M p))) (lattice₂ D Z.M p Λ) ≤
      lattice₂ D Z.M p (NgX Λ (gS D) F F') := by
  rw [GlobalTheory.NonGenericLocalCheck.theta_some (M := Z.M p) (h := hs)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  exact IotaBP.typed_q_mem Z p g hs F F' hv

theorem mem_latP_XLam (Z : LocDat D) (p : PlF D) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ.FG) {T : D.host.E}
    (F : LFlag (VS D) D.R.rS T) {v : Vp D p} (hv : v ∈ lattice₂ D Z.M p Λ)
    (hX : v ∈ (locH Z p).X (scaled Z p (frame F))) : v ∈ lattice₂ D Z.M p (XLam Λ F) := by
  have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (Xsp F) hΛ
  have hsp : v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp F : Set (VS D).V)) := by
    refine (Submodule.span_le.2 ?_) hX
    rintro _ ⟨a, rfl⟩
    have e : scaled Z p (frame F) a.castSucc = frFac Z.δ p a.castSucc • baseChange₂ D p (F.fl.e a) := by
      simp only [scaled, GlobalTheory.LocExt.frame_castSucc]
    show scaled Z p (frame F) a.castSucc ∈ _
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨F.fl.e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩)
  have h : v ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (Xsp F)) : Set (Vp D p)) := by
    rw [hsat]; exact ⟨hv, hsp⟩
  exact h

theorem locglob : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (Z.M p).split ≠ none → ∀ a : 𝓞 D.host.E, (∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (a : D.host.E) - 1 = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) → (∀ p' : PlF D, p' ≠ p → ∃ o ∈ (D.s.atP p').O, (D.s.atP p').ιE (a : D.host.E) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) * o) → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → ∀ {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T'), ∀ y ∈ Λ, (a • y ∈ NgX Λ (gS D) F F' ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) (baseChange₂ D p y)) := by
  intro D Z p hsp a ⟨o, ho, hao⟩ hoth Λ hΛ T T' F F' y hy
  obtain ⟨g, hs⟩ := Option.ne_none_iff_exists'.1 hsp
  have hyp : baseChange₂ D p y ∈ lattice₂ D Z.M p Λ := BwdNP.baseChange_mem_localLattice Z hy p
  constructor
  · intro h
    obtain ⟨μ, hμ, ξ, hξ, ξ', hξ', e⟩ := IotaBP.NgX_dec h
    obtain ⟨w, hw, w', -, hgq, -⟩ := IotaBP.gS_typed Z p g hs
    have h2 : baseChange₂ D p (a • y) = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • baseChange₂ D p μ + baseChange₂ D p ξ + baseChange₂ D p ξ' := by
      rw [e, map_add, map_add, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    have key : baseChange₂ D p y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) •
        (w • (baseChange₂ D p μ - o • baseChange₂ D p y)) + baseChange₂ D p ξ + baseChange₂ D p ξ' := by
      calc baseChange₂ D p y = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y - ((D.s.atP p).ιE (a : D.host.E) - 1) • baseChange₂ D p y := by
            rw [sub_smul, one_smul]; abel
        _ = _ := by
            rw [hao, ← bcP_osmul, h2, hgq]
            simp only [smul_sub, smul_smul, mul_assoc]
            abel
    refine ⟨_, ?_, baseChange₂ D p ξ, BwdNP.baseChange_mem_localLattice Z (IotaBP.xi_mem hξ) p, baseChange₂ D p ξ', BwdNP.baseChange_mem_localLattice Z (IotaBP.xi_mem hξ') p,
      GlobalTheory.LocExt.bcP_Xsp_mem Z p F (Submodule.mem_inf.1 hξ).2, GlobalTheory.LocExt.bcP_Xsp_mem Z p F' (Submodule.mem_inf.1 hξ').2, key⟩
    rw [GlobalTheory.NonGenericLocalCheck.theta_some (M := Z.M p) (h := hs)]
    refine Submodule.subset_span ⟨w • (baseChange₂ D p μ - o • baseChange₂ D p y), ?_, rfl⟩
    exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p hw
      (sub_mem (BwdNP.baseChange_mem_localLattice Z hμ p) (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p ho hyp))
  · rintro ⟨A, hA, B, hB, C, hC, hBX, hCX, he⟩
    refine BwdNP.mem_of_bcP Z (IotaBP.isLattice_NgX hΛ F F') fun p' => ?_
    by_cases hp : p' = p
    · rw [hp, bcP_osmul]
      have e : (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y =
          baseChange₂ D p y + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • baseChange₂ D p y) := by
        rw [smul_smul, ← hao, sub_smul, one_smul]; abel
      rw [e]
      refine add_mem ?_ (IotaBP.smul_gS_mem Z p F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p ho hyp))
      rw [he]
      refine add_mem (add_mem (smulLat_le Z p g hs Λ F F' hA) ?_) ?_
      · exact IotaBP.localLattice_mono Z p (le_sup_right.trans le_sup_left) (mem_latP_XLam Z p hΛ.fg F hB hBX)
      · exact IotaBP.localLattice_mono Z p le_sup_right (mem_latP_XLam Z p hΛ.fg F' hC hCX)
    · obtain ⟨o', ho', hao'⟩ := hoth p' hp
      have e : baseChange₂ D p' (a • y) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • (o' • baseChange₂ D p' y) := by
        rw [bcP_osmul, smul_smul, ← hao']
      rw [e]
      exact IotaBP.smul_gS_mem Z p' F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p' ho' (BwdNP.baseChange_mem_localLattice Z hy p'))

end GlobalTheory.IotaLocGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrimeStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_rowLattice_orthogonal_split_prime : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (Lat.Tu D u).Prime → Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) → ∀ Λ : Cnt.LatV D, IsRowLat D F0 Λ → mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) = Cnt.massS D D.R.k * ((((Lat.Tu D u : ℕ) : ℝ) ^ D.R.k - 1) / (((Lat.Tu D u : ℕ) : ℝ) - 1)) ^ D.R.f ∧ Cnt.massS D D.R.k * Cnt.NT D u ^ (D.R.k - 1) ≤ mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) := by
  first | exact @GlobalTheory.Mass.RowPerpMass.main | exact GlobalTheory.Mass.RowPerpMass.main | (intros; apply GlobalTheory.Mass.RowPerpMass.main <;> assumption)
end

