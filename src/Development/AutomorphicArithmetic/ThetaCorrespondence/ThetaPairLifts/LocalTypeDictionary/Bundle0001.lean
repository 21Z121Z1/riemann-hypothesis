import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0465
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0901
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0511
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.DmOfHyp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0544
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.GlobalFormAtFrameLatNc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.BridgeTrue
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0427
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0900
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0870
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
section
section
namespace GlobalTheory.FunPr
structure ThetaLocalInputs : Prop where
  greenSeriesSt : GlobalTheory.Published.GreenSeriesSt
  linnik : GlobalTheory.Published.Linnik
  complexMultiplicationJSt : GlobalTheory.Published.ComplexMultiplicationJSt
  cuspidalMirabolic : GlobalTheory.Published.CuspidalMirabolic
  weylBranching : GlobalTheory.Published.WeylBranching
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  rallisInnerProductConvergent : GlobalTheory.Published.RallisInnerProductConvergent
  doublingMethod : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL
  hermitianLocalGlobal : GlobalTheory.Published.HermitianLocalGlobal
  quadraticClassFieldTheory : GlobalTheory.Published.QuadraticClassFieldTheory
  borelCasselman : GlobalTheory.Published.BorelCasselman
  radfordShufflePolynomial : GlobalTheory.Published.RadfordShufflePolynomial
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  heckeLPartialContinuation : GlobalTheory.Published.HeckeLPartialContinuation
  logDerOne : GlobalTheory.Mem.An.LogDerOne
  kFiniteVectorsUnitary : GlobalTheory.Published.KFiniteVectorsUnitary
  discreteSeriesLowestKType : GlobalTheory.Published.DiscreteSeriesLowestKType
  holomorphicDiscreteSeries : GlobalTheory.Published.HolomorphicDiscreteSeries
  gKGlobalisation : GlobalTheory.Published.GKGlobalisation
  cuspBounded : GlobalTheory.Published.CuspBounded
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  heckeLEntireAndNonzeroAtOne : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne
  realMetaplecticRepresentation : GlobalTheory.Published.RealMetaplecticRepresentation
  cuspDecayBound : GlobalTheory.Published.CuspDecayBound
  gLHoweDuality : GlobalTheory.Published.GLHoweDuality
  kudlaSplittingSplitUnitary : GlobalTheory.Published.KudlaSplittingSplitUnitary
  metaplecticRepresentation : GlobalTheory.Published.MetaplecticRepresentation
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  idealInvariantsOneOrbitSt : GlobalTheory.Published.IdealInvariantsOneOrbitSt
  hermitianHassePrinciple : GlobalTheory.Published.HermitianHassePrinciple
  stoneVonNeumann : GlobalTheory.Published.StoneVonNeumann
  discreteSeriesUpqExists : GlobalTheory.Published.DiscreteSeriesUpqExists
  formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual
  thetaRationalInvariance : GlobalTheory.Published.ThetaRationalInvariance
  discreteSeriesHermitianUnique : GlobalTheory.Published.DiscreteSeriesHermitianUnique
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay
  weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair
  discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists
  cuspDecaySobolev : GlobalTheory.Published.CuspDecaySobolev
  casselmanWallach : GlobalTheory.Published.CasselmanWallach
  howeDualityReal : GlobalTheory.Published.HoweDualityReal
  siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary
  weilRepresentationExists : GlobalTheory.Published.WeilRepresentationExists
end GlobalTheory.FunPr
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BesselMapUniqueOfBesselModelUniqueness
section
section
noncomputable section
open Matrix Topology Filter
open scoped ContDiff
namespace GlobalTheory.BesselMapOne
section Smooth
open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end
end Smooth
section Frame
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k r : ℕ}
variable {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
end Frame
section Dual
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
end Dual
section Main
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel PI.BesselMapUniq GlobalTheory.SmVec
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
end Main
end GlobalTheory.BesselMapOne
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BesselSpectral
section
section
noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict
open GlobalTheory.St.SpectralData
namespace UpperTheory.Lit
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem exists_spectralData_gap_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y) (tr : ∀ u, Transport X u (F u)), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧ (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧ Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ u, LevelMatch X (tr u) Y.hK ∧ ColDictInto X (tr u) Y.hK ∧ ColDictBij X (tr u) Y.hK ∧ ColDictIsom X (tr u) Y.hK (Y.cs u) (hF.shInj u) := by
  intro hSW hRF D F hG hLT
  obtain ⟨X, hb, ψ, hI, hι, hM, hψ, hstd, hCm, hL, hT⟩ := exists_setting hSW D F hG
  obtain ⟨Y⟩ := GlobalTheory.fullExists_of_locTied D X hLT
  obtain ⟨hWD, hph⟩ := CompanionTheory.Lime.BM.wuDecayOfGap_holds' D hG X
  have hF : FinX Y := GlobalTheory.FinitenessBundle.finX_of_decay hRF D X Y hWD hph
  choose tr htr using hT Y.hK
  refine ⟨X, hb, ψ, Y, hF, tr, hI, hι, hM, hψ, hstd, hCm, hL, hph, fun u => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.St.colDictCore_holds D X u (F u) (tr u) Y.hK (htr u)
    (GlobalTheory.columnLevel_stabTriv D X Y.hK u)
  exact ⟨htr u, h1, h2, h3 _ (Y.cs u) (hF.shInj u) (Y.colReps u)⟩
end UpperTheory.Lit
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjSelfDualGaloisRepCMDatum
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatum : Prop :=  ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → labAt hL D k v (Irr.ofDet 1 μ hμ) = X - C c
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DoublingMethodOfEisensteinFacts
section
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_zeta_of_eisenstein_facts : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals := by
  first | exact @_root_.ResidueKilled.dm_of_two | exact _root_.ResidueKilled.dm_of_two | (intros; apply _root_.ResidueKilled.dm_of_two <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
section
section
namespace GlobalTheory.NRows
structure GeometricGaloisRepCompatibility : Prop where
  weil : GlobalTheory.Published.WeilRepresentationUnitaryPair
  ds : GlobalTheory.Published.DiscreteSeriesExists
  ana : GlobalTheory.Published.HarishChandraAnalyticity
  dsc : GlobalTheory.Published.DiscreteSeriesClassification
  trc : GlobalTheory.Published.CuspTraceClass
  dm : GlobalTheory.Published.DixmierMalliavinFactorisation
  flath : GlobalTheory.Published.FlathFactorisation
  sw : GlobalTheory.Published.WeilSiegelFormulaUnitary
  dbl : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  udbl : GlobalTheory.Published.UnramifiedDoublingGL
  hl : GlobalTheory.Published.HeckeLPartialContinuation
  ht : GlobalTheory.HeightCounting.HtCard
end GlobalTheory.NRows
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalFormFrameLattice
section
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalFormAt_frameLat_of_siegelWeil : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → ∀ D : D7, SiegelWeilFock D → ∀ A : HSp D, GlobalFormAt A (frameLat A) := by
  first | exact @_root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc | exact _root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc | (intros; apply _root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweDualityGLOfMinguezThetaCorrespondence
section
section
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalBesselMultiplicityOne
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.LocalBesselMultiplicityOne : Prop :=  Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.HeightCounting.RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalGlobalCompatibilityCMDatum
section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.LocalGlobalCompatibilityCMDatum : Prop :=  ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → labAt hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NonGaloisTwistType
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.CoefDuty GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.NonGaloisTwistType : Prop :=  GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : NAt hL D cf nch tp), OPin a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SpehInfinitesimalCharacterOfResidual
section
section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
namespace GlobalTheory.SpehInfChar
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
end GlobalTheory.SpehInfChar
end
end

section

end
end

