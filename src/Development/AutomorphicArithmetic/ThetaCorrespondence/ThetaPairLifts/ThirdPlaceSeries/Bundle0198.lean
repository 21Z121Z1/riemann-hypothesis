import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0196
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0753
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0080
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0008
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0003
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0195
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0054
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0048
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0193
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0191
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0987
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0146
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OpenUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0192
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SeparableConjugates.ExistsHasSatakeOfUnr
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlLocalGlobalAboveLregAlg
section
theorem UpperTheory.GalS.CarUAlt.regAlg : type_of% (@UpperTheory.GalS.carU_of_regular_algebraic_purity) := @UpperTheory.GalS.carU_of_regular_algebraic_purity
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ArchimedeanLocalLanglandsCompatibility
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.ArchFromLit
theorem archimedean_local_langlands_compatibility_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt → _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses' → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL := by
  intro hLoc hAut hL
  exact
    { pht := GlobalTheory.PhtCompare.phtCmp
      lp := fun _ _ => ⟨⟨⟩⟩
      cg := fun _ _ _ => ⟨⟨⟩⟩ }
end GlobalTheory.ArchFromLit
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
section
set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.Mem.LiteralAutomorphy
structure NonEndoscopicHypothesesAlt : Prop where
  loc : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt
  aut : _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses'
  coh : LitCoh
  join : JoinOut
  fe : GlobalTheory.Published.HeckeTateFunctionalEquation
end GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Fc.S0
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure UnitaryGroupThirdPlaceHypotheses : Prop where
  clozelCohomological : GlobalTheory.Published.ClozelCohomological
  greenCuspidal : GlobalTheory.Published.GreenCuspidal
  heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter
  chebotarevDegreeOne : GlobalTheory.Published.ChebotarevDegreeOne
  galoisRepOfPolarizedCuspidal : _root_.UpperTheory.GalS.CuspUAlt
  baseChangeDefiniteUnitary : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup
  bhattScholzeCrystallineLattices : GlobalTheory.Published.BhattScholzeCrystallineLattices
  heckeLAdicCharacterAbove : GlobalTheory.Published.HeckeLAdicCharacterAbove
  cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  siegelWeilUnitaryConvergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  doublingMethod : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL
  bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration
  unlinkedProductIrreducible : GlobalTheory.Published.UnlinkedProductIrreducible
  depthZeroJacquetInjective : GlobalTheory.Published.DepthZeroJacquetInjective
  jacquetShalika : GlobalTheory.Published.JacquetShalika
  automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL
  localGlobalAboveL : _root_.UpperTheory.GalS.CarUAlt
  regularAlgebraicPurity : GlobalTheory.Published.RegularAlgebraicPurity
  globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity
  heckeLAdicParameterAbove : _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt
  deRhamPotSemistable : GlobalTheory.Published.DeRhamPotSemistable
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  greenRegularCharacters : GlobalTheory.Published.GreenRegularCharacters
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt
  rayCharacterArtin : GlobalTheory.Published.RayCharacterArtin
  genericUnitaryDualGL : GlobalTheory.Published.GenericUnitaryDualGL
  standardCosocleGL : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  casselmanWallach : GlobalTheory.Published.CasselmanWallach
  weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  siegelWeilUnitaryConvergent2 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  harishChandraAnalyticity : GlobalTheory.Published.HarishChandraAnalyticity
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  cMCurveGoodOutsidePrimeSt : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  weberRayFieldSt : GlobalTheory.Published.WeberRayFieldSt
  discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation
  siegelEisensteinSimplePole : _root_.GlobalTheory.Published.UnusedSlot72
  schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  litN : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt
  toHypothesesX : _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport
  localFiniteness : ReciprocityTheory.Gal.LocalFiniteness
  localTateDuality : ReciprocityTheory.Gal.LocalTateDuality
  localEulerChar : ReciprocityTheory.Gal.LocalEulerChar
theorem UnitaryGroupThirdPlaceHypotheses.geometricLemma (P : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses) : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration P.bernsteinZelevinskyFiniteness P.geometricLemmaFiltration
end GlobalTheory.Fc.S0
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTypeSplitProp
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.BlockTypeSplitThirdPlace : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.RegularLocalCondition hL D
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CgEqOfCharStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_rep_one_eq_of_character_choice : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (π : D.naut.CG 1), haveI := GlobalTheory.CuspRep.host_isCMField D.host; ((P.cg.e 1 π).1 : GlobalTheory.CuspRep.CG D.host.E 1) = GlobalTheory.CuspRep.CG.ofChar (P.chr.e1 π).1 := by
  first | exact @_root_.GlobalTheory.RankOneChar.cg_eq_ofChar_alt | exact _root_.GlobalTheory.RankOneChar.cg_eq_ofChar_alt | (intros; apply _root_.GlobalTheory.RankOneChar.cg_eq_ofChar_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalProperty
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.CompatibleSystemLocalPropertyThirdPlace : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalPropertyExplicit
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace GlobalTheory.SerSys.Assembly
abbrev _root_.GlobalTheory.SerSys.Assembly.CompatibleSystemLocalPropertyExplicitAlt : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L →
    (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
      TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) →
    GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D
end GlobalTheory.SerSys.Assembly
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsChar
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.WeilDeligne
section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
variable {N A}
end
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
end
end UpperTheory.GalS
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp
variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
variable {D T ι π s r}
end GlobalTheory.TripleLocal
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem exists_galois_character_crystalline_at_places (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hG : _root_.UpperTheory.GalS.CuspUAlt)
    (ι : Qbar l ≃+* ℂ) (ψ : HChar E) (hu : ∀ v, ψ.UnrAt v) (hr : ∀ τ, ∃ n : ℤ, expo ψ τ = n)
    (hp : ∃ χ, IsPolarized ((CuspSub.triv E (le_refl 1)).twist ψ) χ) :
    ∃ c : G E Ω →* (Qbar l)ˣ, Continuous c ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (B : ValuationSubring Ω) (g : G E Ω),
        IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g → ι (c g : Qbar l) = (((ψ.val w)⁻¹ : ℂˣ) : ℂ)) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
        IsCrysAt P Bw ((GeneralLinearGroup.scalar (Fin 1)).comp (c.comp (Dec (F := E) A).subtype)) := by
  obtain ⟨χ, hχ⟩ := hp
  have hreg : (CG.mk ((CuspSub.triv E (le_refl 1)).twist ψ)).IsRegAlg := (CG.isRegAlg_ofChar ψ).2 hr
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι 1 le_rfl _ χ hreg hχ
  have hcr : Continuous fun g => (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) := Units.continuous_val.comp H.cont
  have hsc : (GeneralLinearGroup.scalar (Fin 1)).comp (Matrix.GeneralLinearGroup.det.comp r) = r := by
    ext g i j
    rw [MonoidHom.comp_apply, coe_scalar, Subsingleton.elim i 0, Subsingleton.elim j 0]
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    change Matrix.det (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) = _
    rw [Matrix.det_fin_one]
  have hdet : Continuous fun x : GL (Fin 1) (Qbar l) => Matrix.GeneralLinearGroup.det x := GeneralLinearGroup.continuous_det
  refine ⟨MonoidHom.comp Matrix.GeneralLinearGroup.det r, hdet.comp H.cont, fun w hl B g hB hg => ?_, fun P AI hT w A h O _ _ _ Bw hj => ?_⟩
  · obtain ⟨y1, y2⟩ := _root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL ψ hB (hu w)
    have e1 : wdOf hB hl ι r = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar ψ) hB := by
      rw [H.eq_locPar hL hF hl hB y1, show (1 - ((1 : ℕ) : ℝ)) / 2 = 0 by norm_num, WD.lpTw_zero]
      rfl
    have f := frobEig_wdOf hl ι hcr (e1 ▸ y1) hB hg
    rw [e1, y2] at f
    have h1 : (r g : Matrix (Fin 1) (Fin 1) (Qbar l)).charpoly = X - C ((r g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0) := by
      simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]
    rw [h1] at f
    have f2 := congrArg (fun p => p.coeff 0) f
    simp at f2
    change ι (Matrix.det _) = _
    rw [Matrix.det_fin_one]
    exact f2.trans (Units.val_inv_eq_inv_val _).symm
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E 1 ((CuspSub.triv E (le_refl 1)).twist ψ) w
    have hc := (H.above P AI hT w A h O Bw hj).crys σ hσ ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) (ParLaws.toRep σ)).1 (by
      rw [← _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h]
      exact (_root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL ψ h (hu w)).1))
    have e : (GeneralLinearGroup.scalar (Fin 1)).comp ((Matrix.GeneralLinearGroup.det.comp r).comp (Dec (F := E) A).subtype) =
        r.comp (Dec (F := E) A).subtype := by
      rw [← MonoidHom.comp_assoc, hsc]
    rw [e]
    exact hc
end G
end GlobalTheory.HodgeOfTrue
namespace GlobalTheory.GalAway
end GlobalTheory.GalAway
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDepthZeroFixedVector
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DzVecLoc
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.HeightCounting.Up.CenLoc D P.M → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) ρ f, InSeries D k ρ f → PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ) → ∃ x, IsBlockVec (S i _ hw).mu ((S i _ hw).rep PI).π x ∧ NotKilled ((S i _ hw).rep PI).π (idemOf D k ρ) x := by
  intro _ hL D P hC S hT i PI k v hw ρ f hser hocc
  obtain ⟨s, hs⟩ := GlobalTheory.TypeBlockPf.splitAt D _ hw
  have key : ∀ (w : PlE D.host) (hw' : IsSplitPl D.host w), w = D.naut.plGw k v → ∃ x, IsBlockVec (S i w hw').mu ((S i w hw').rep PI).π x ∧ NotKilled ((S i w hw').rep PI).π (idemOf D k ρ) x := by
    intro w hw' hwv
    have e : w = s.w := hwv.trans hs.symm
    subst e
    exact _root_.GlobalTheory.DzVecLoc.vector_at_split_place hL D P hC S hT i PI k v s hw' hs ρ hser.1 hocc
  exact key _ hw rfl
end GlobalTheory.DzVecLoc
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockVec_notKilled_of_occurs : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.HeightCounting.Up.CenLoc D P.M → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) ρ f, InSeries D k ρ f → PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ) → ∃ x, IsBlockVec (S i _ hw).mu ((S i _ hw).rep PI).π x ∧ NotKilled ((S i _ hw).rep PI).π (idemOf D k ρ) x := by
  first | exact @_root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsGalRepCsdTwist
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
end GlobalTheory.HeightCounting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
end GlobalTheory.GalAllPlaces
end
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.CsdTwistGal
theorem exists_galRep_csd_twist_alt_alt : _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.HeckeLAdicCharacter →
  GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.BhattScholzeCrystallineLattices → _root_.UpperTheory.Zero.LLC.RecTExists →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
    ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
    ∀ (f : ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ, (J τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map (fun z => f - z)) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ((∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          P.IsLocComp w σ ∧ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w a)) → GlobalTheory.ExpFrame.CrysWith r J) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ → ∀ S : Multiset ℂˣ,
          GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w →
            IsFrob (F := E) B (normV w) g →
            (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
              Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ f))).prod := by
  intro hG _ _ _ _ hLL E Ω _ _ _ _ _ _ _ l _ ι a ha P hP m hm hnd f J hJ
  have hτ : ∀ σ : E →+* ℂ, ι.toRingHom.comp (ι.symm.toRingHom.comp σ) = σ := fun σ => by
    ext x; simp
  have hint : ∀ σ : E →+* ℂ, ∀ z ∈ m σ, ∃ k : ℤ, f - z = k := by
    intro σ z hz
    have h1 := hJ (ι.symm.toRingHom.comp σ)
    rw [hτ] at h1
    have h2 : f - z ∈ (m σ).map (fun z => f - z) := Multiset.mem_map_of_mem _ hz
    rw [← h1] at h2
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.1 h2
    exact ⟨k, hk.symm⟩
  have hfre : f = ((f.re : ℝ) : ℂ) := by
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨z, hz⟩ : ∃ z, z ∈ m τ0 := Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ0).1]; omega)
    have hc := infChar_conj_of_isCsd E a P hP τ0 _ _ (hm τ0) (hm _)
    have hz' : -z ∈ m (NumberField.ComplexEmbedding.conjugate τ0) := by
      rw [hc]; exact Multiset.mem_map_of_mem _ hz
    obtain ⟨k1, hk1⟩ := hint _ z hz
    obtain ⟨k2, hk2⟩ := hint _ _ hz'
    have e1 := congrArg Complex.im hk1
    have e2 := congrArg Complex.im hk2
    simp only [Complex.sub_im, Complex.intCast_im, Complex.neg_im] at e1 e2
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]; linarith
  set s : ℝ := ((a : ℝ) - 1) / 2 - f.re with hs
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hexpo : ∀ τ, expo (GlobalTheory.HeckeGal.Model.absPow E s) τ = s :=
    (GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 s hν
  have hm' : ∀ τ, (P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).HasInfChar τ ((m τ).map (· + (s : ℂ))) := fun τ => by
    have := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rwa [hexpo] at this
  have hinf' : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) :=
    fun τ => CG.HasInfChar.infChar_eq (hm' τ)
  have hr : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf' τ]
    refine ⟨(hnd τ).map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨k, hk⟩ := hint τ y hy
    refine ⟨-k, ?_⟩
    rw [hs]; push_cast
    linear_combination (-1 : ℂ) * hk + hfre
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι a ha _ _ hr (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s)
  have hHT : ∀ τ, HT τ = J τ := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hinf', hJ τ, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    rw [hs]; push_cast
    linear_combination (-1 : ℂ) * hfre
  refine ⟨r, H.cont, fun hsph => ⟨H.cont, fun PP AI T w A h O _ _ _ Bw hj => ?_⟩, ?_⟩
  · have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := hj.mem_placesOver h
    obtain ⟨σ, hσ, hsp⟩ := hsph w hw
    have HA := H.above PP AI T w A h O Bw hj
    refine ⟨HA.crys _ (hσ.twist _) (GlobalTheory.T.isSpherical_twist_absDetPow_GL E a w σ s hsp), fun τ LL' τ' hτ' => ?_⟩
    rw [← hHT]
    have hrc := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hLL h
    exact HA.jumps (_root_.UpperTheory.GalS.nice_of_spherical' hrc (hσ.twist _) (GlobalTheory.T.isSpherical_twist_absDetPow_GL E a w σ s hsp)) τ LL' τ' hτ'
  · intro w _ hl σ hσ S hS B g hB hg
    obtain ⟨rc, hrc⟩ : ∃ rc, _root_.UpperTheory.Zero.LLC.IsRecT hB rc := ⟨_, _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hLL hB⟩
    have e0 := H.aw hl hrc (hσ.twist (GlobalTheory.HeckeGal.Model.absPow E s))
    rw [_root_.GlobalTheory.CsdTwistGal.rec_twist_absPow_alt E Ω w B hB rc hrc a σ s, GlobalTheory.WeilDeligne.WD.lpTw_add] at e0
    have e1 := e0.eq_unr ((GlobalTheory.WeilDeligne.WD.unr_tw _ _).2 (_root_.UpperTheory.GalS.unr_rec_of_has_sat hrc σ S hS))
    rw [_root_.GlobalTheory.T.charpoly_inv_eq_prod_absNorm_cpow_of_isFrob E Ω l ι a r H.cont w hl B hB rc hrc σ S hS _ e1 g hg]
    have e2 : ((-(s + (1 - (a : ℝ)) / 2) : ℝ) : ℂ) = f := by
      rw [hfre, hs]; push_cast; ring
    rw [e2]
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
end GlobalTheory.TempSatGal
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}
theorem exists_hasSatake_of_unr_alt (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : IrrRep (GL (Fin a) (w.adicCompletion E))}
    (hu : (rc (cls σ)).unr) : ∃ α, HasSatake σ.ρ α := by
  obtain ⟨m, c, e⟩ := Unram.exists_diag hu
  have H' := H
  first | (have hOpn := UpperTheory.One.M.opn _ (H'); obtain ⟨_, _, _, H'⟩ := hOpn) | obtain ⟨_, _, _, -, H'⟩ := H'
  obtain rfl : a = m := by simpa [e] using (H'.dim (cls σ)).symm
  obtain ⟨τ, hτ⟩ := exists_hasSatake (k := w.adicCompletion E) fun i => (c i)⁻¹
  have e2 := _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hτ
  simp only [inv_inv] at e2
  have g : UpperTheory.Zero.LLC.Good (cls σ) :=
    (GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz _ _ ((H'.sph _).2 hu)).2
  obtain ⟨φ⟩ := (IrrGL.of_eq_of (π := τ.ρ) (σ := σ.ρ) (hs := τ.smooth) (hi := τ.irr) (hs' := σ.smooth) (hi' := σ.irr)).1
    (_root_.UpperTheory.One.M.LawsM.inj H' (cls τ) (cls σ) g (e2.trans e.symm))
  exact ⟨_, σ.irr, fixed_ne_bot_of_equiv φ hτ.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hτ.2.2⟩
end UpperTheory.One.M
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalLanglandsOfHyp
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recTExists_of_published_inputs : _root_.UpperTheory.Zero.LLC.RecTExists → LocalConverseGL → DepthZeroInduction → BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → _root_.UpperTheory.Zero.LLC.RecTExists := by
  first | exact @_root_.UpperTheory.One.M.New.llOf_alt | exact _root_.UpperTheory.One.M.New.llOf_alt | (intros; apply _root_.UpperTheory.One.M.New.llOf_alt <;> assumption)
end
end

