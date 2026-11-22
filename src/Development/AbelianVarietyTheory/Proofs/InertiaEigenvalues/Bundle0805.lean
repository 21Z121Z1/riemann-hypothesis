import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0708
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRefinedFlagChartIntegralPointsInOpen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinMapSplitPlaceUniformiserEqFrobeniusInvStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artinMap_splitPlaceUniformiser_eq_frobenius_inv : ∀ (D : D7) (Ω : Type) [Field Ω] [Algebra D.host.E Ω] (A : Type) [CommGroup A] (a : Recip D Ω), a.Good → ∀ φ : G D.host.E Ω →* A, IsOpen (φ.ker : Set (G D.host.E Ω)) → ∀ (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ B : ValuationSubring Ω, IsPlaceOver B P → (∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) → ∀ σ : G D.host.E Ω, IsFrob (F := D.host.E) B (normV P) σ → a.pull φ x = (φ σ)⁻¹ := by
  first | exact @GlobalTheory.SeriesTie.Recip.pull_locUnif | exact GlobalTheory.SeriesTie.Recip.pull_locUnif | (intros; apply GlobalTheory.SeriesTie.Recip.pull_locUnif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Conclusion41OfHyp
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.ClosingLocalInputs

theorem galoisFamilyConditions_of_sumRepresentations (D : D7) (h41 : SumRepresentations.Conclusion41 D) : GaloisFamilyConditions (D := D) :=
  fun i r hr => (h41 i).2.2 r hr

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris →
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C : ℝ) (CT : ℕ), 40 ≤ CT → 8 * (CT : ℝ) ≤ C → (∃ P : Pend D, admDZ P ∧ EigSpan P) →
    SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → SumRepresentations.Conclusion41 D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionG6 D →
    ResidualIrreducibleRankR D → GlobalTheory.TypeLeaf.SerLoc D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D → TieInePoly D → tieChi (D := D) →
    PairedCharacterCondition.aux₃ (D := D) C CT := by
  intro hGAR hBS hFB hBKL hLTD hLEC D HW F Cm C CT hCT hC hP htie0 hadm1 hadm2 hadm5 h41 hG5 hG6 hN9 hSer hO
    hIne hChi
  obtain ⟨P, hDZ, hEig⟩ := hP
  have hT : admT (D := D) CT := GlobalTheory.T.crystallinePeriodBound_all_constant_ge_forty hBS hFB hBKL hLTD hLEC D HW F Cm CT hCT
  have hLOC : LocalPushoutProposition (D := D) := GlobalTheory.T.local_absorption_length_bound_of_blochKato hBKL hLTD hLEC D HW F Cm
  have hRbar : ResidualAbsIrreducible (D := D) := GlobalTheory.Pass.residualRep_spans_matrixAlgebra_of_goodPoint D hN9
  have hN5g : TypePrimeChoiceLemmas (D := D) := GlobalTheory.supplier_type_prime_all D ⟨hadm5, h41, hN9, hO⟩
  have hTB : admTB (D := D) HW F := GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hBKL hLTD hLEC D HW F Cm
  have hBK : admBK (D := D) := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBKL hLTD hLEC D
  exact GlobalTheory.T.conclusion_of_local_conditions hGAR D P HW F C CT hC hadm5 hEig hIne hT hLOC hRbar hN5g hDZ
    (galoisFamilyConditions_of_sumRepresentations D h41) hG5 hG6 hSer hTB hBK hadm1 hadm2 htie0 hChi

end GlobalTheory.ClosingLocalInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspReadTOfCuspRead
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.HeightCounting

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

abbrev RecFam : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), IrrGL (w.adicCompletion E) → WD h

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

def compG {a : ℕ} (π : HostCGu H a) (w : PlE H) : IrrGL (w.adicCompletion H.E) :=
  haveI := host_isCMField H; ⟨a, ParLaws.toCl (π.1.loc w)⟩

def AllGood {a : ℕ} (π : HostCGu H a) : Prop := ∀ w : PlE H, Good (compG π w)

variable {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

def locGR (rc : RecFam) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a) (w : PlE H) : WD (pl.2 w) :=
  rc (pl.2 w) (compG π w)

theorem locGR_locRec (hL : GlobalTheory.Published.LocalLanglandsGL) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a)
    (w : PlE H) : locGR (fun h => ParLaws.locRec hL h) pl π w = ParLaws.locG hL pl π w := rfl

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

structure CGTrueT (rc : RecFam) (D : D7) (T : WDTie D.nd D.naut) where
  isRecT : ∀ w, IsRecT (D.nd.plOm.2 w) (rc (D.nd.plOm.2 w))
  e : ∀ a, D.naut.CG a ↪ HostCGu D.host a
  surj : ∀ a, 0 < a → ∀ π : HostCGu D.host a, AllGood π → ∃ σ, e a σ = π
  zero : IsEmpty (D.naut.CG 0)
  loc : ∀ a (π : D.naut.CG a) w, Good (compG (e a π) w) → T.e w (D.naut.locG π w) = locGR rc D.nd.plOm (e a π) w
  tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ)
  inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ
  csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd

variable {rc : RecFam} {D : D7} {T : WDTie D.nd D.naut}

def cgTrueT_of_cgTrue (hD : GlobalTheory.Published.DepthZeroTypeInertia) {hL : GlobalTheory.Published.LocalLanglandsGL} (C : CGTrue hL D T) :
    CGTrueT (fun h => ParLaws.locRec hL h) D T where
  isRecT w := (isRecT_iff _).2 (UpperTheory.Zero.LLC.isRecT_of_isRec hD (ParLaws.isRec_locRec hL (D.nd.plOm.2 w)))
  e := C.e
  surj a ha π _ := C.surj a ha π
  zero := C.zero
  loc a π w _ := C.loc a π w
  tw := C.tw
  inf := C.inf
  csd := C.csd

theorem cgTrueT_of_cgTrue_e (hD : GlobalTheory.Published.DepthZeroTypeInertia) {hL : GlobalTheory.Published.LocalLanglandsGL} (C : CGTrue hL D T) :
    (cgTrueT_of_cgTrue hD C).e = C.e := rfl

set_option maxHeartbeats 2000000 in

def trueCGT (hD : GlobalTheory.Published.DepthZeroTypeInertia) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (D : D7) (hE : IsEmpty D.nd.Loc) (T : WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLaws.locG hL D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLaws.locG hL D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLaws.locG hL D.nd.plOm η' w).unr ∧
      (ParLaws.locG hL D.nd.plOm η' w).frobEig = (ParLaws.locG hL D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ, (ParLaws.locG hL D.nd.plOm η w).frobEig = {a} →
      (ParLaws.locG hL D.nd.plOm η w').frobEig = {b} → a * b = 1) :
    CGTrueT (fun h => ParLaws.locRec hL h) (setCG D hE (trueK hL hF D T η η' h1 h2 h3 h4)) (wdCG hE _ T) :=
  cgTrueT_of_cgTrue hD (trueCG hL hF D hE T η η' h1 h2 h3 h4)

theorem trueCGT_e_surj (hD hL hF D hE T η η' h1 h2 h3 h4) (a : ℕ) (ha : 0 < a) :
    Function.Surjective ((trueCGT hD hL hF D hE T η η' h1 h2 h3 h4).e a) :=
  (trueCG hL hF D hE T η η' h1 h2 h3 h4).surj a ha

def CGTrueT.equivGood (C : CGTrueT rc D T) (a : ℕ) (h : 0 < a) :
    {σ : D.naut.CG a // AllGood (C.e a σ)} ≃ {π : HostCGu D.host a // AllGood π} :=
  Equiv.ofBijective (fun σ => ⟨C.e a σ.1, σ.2⟩)
    ⟨fun σ τ hst => Subtype.ext ((C.e a).injective (congrArg Subtype.val hst)),
     fun π => let ⟨σ, hσ⟩ := C.surj a h π.1 π.2; ⟨⟨σ, hσ ▸ π.2⟩, Subtype.ext hσ⟩⟩

@[simp] theorem CGTrueT.equivGood_apply (C : CGTrueT rc D T) (a : ℕ) (h : 0 < a) (σ) :
    (C.equivGood a h σ : HostCGu D.host a) = C.e a σ.1 := rfl

section Read

open Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

def recMapT {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : WDTie N A)
    (rc : RecFam) : RecMap A :=
  fun w _ σ => (T.e w).symm (rc (N.plOm.2 w) (cls (ParLaws.toRep σ)))

theorem recMapT_locRec {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (T : WDTie N A) (hL : GlobalTheory.Published.LocalLanglandsGL) :
    recMapT T (fun h => ParLaws.locRec hL h) = GlobalTheory.FormDict.recT T hL := rfl

def CuspReadT {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (rc : RecMap A) : Prop :=
  ∀ (a : ℕ) (P : CuspSub H.E a), 1 ≤ a → P.IsCsd →
    (∀ w : PlE H, ∃ σ, P.IsLocComp w σ ∧ Good (cls (ParLaws.toRep σ))) → ∃ π : A.CG a, A.csd π ∧
    (∀ w σ, P.IsLocComp w σ → A.locG π w = rc w a σ) ∧ ∀ τ m, P.HasInfChar τ m → A.infG π τ = m

theorem cuspReadT_of_cuspRead {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {rc : RecMap A} (h : CuspRead rc) : CuspReadT rc :=
  fun a P ha hP _ => h a P ha hP

theorem compG_eq {D : D7} {a : ℕ} (P : CuspSub D.host.E a) (hu : haveI := host_isCMField D.host; (CG.mk P).IsUnitary)
    {w : PlE D.host} {σ : SmIrr (GL (Fin a) (w.adicCompletion D.host.E))} (hσ : P.IsLocComp w σ) :
    compG (H := D.host) ⟨CG.mk P, hu⟩ w = cls (ParLaws.toRep σ) := by
  haveI := host_isCMField D.host
  have h1 : (CG.mk P).IsLoc w (Quotient.mk _ σ) := hσ
  simp only [compG]
  rw [CG.IsLoc.unique D.host.E a _ w _ _ h1.loc h1]
  rfl

theorem cuspReadT_recMapT : ∀ (rc : RecFam) (D : D7) (T : WDTie D.nd D.naut),
    CGTrueT rc D T → CuspReadT (recMapT T rc) := by
  intro rc D T C a P ha hP hg
  haveI := host_isCMField D.host
  have hu : (CG.mk P).IsUnitary := CsdUnitary.isUnitary_of_isCsd _ a (CG.mk P) hP
  have hgood : AllGood (H := D.host) ⟨CG.mk P, hu⟩ := fun w => by
    obtain ⟨σ, hσ, hg⟩ := hg w
    rw [compG_eq P hu hσ]; exact hg
  obtain ⟨π, hπ⟩ := C.surj a ha ⟨CG.mk P, hu⟩ hgood
  refine ⟨π, (C.csd a _).2 (by rw [hπ]; exact hP), fun w σ hσ => ?_, fun τ m hm => ?_⟩
  · apply (T.e w).injective
    rw [C.loc a π w (by rw [hπ]; exact hgood w)]
    simp only [recMapT, Equiv.apply_symm_apply, locGR, hπ]
    rw [compG_eq P hu hσ]
  · rw [C.inf, hπ]
    exact CG.HasInfChar.infChar_eq (π := CG.mk P) hm

end Read

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

theorem nonempty_equivGoodAll : ∀ (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : WDTie D.nd D.naut),
    GlobalTheory.HeightCounting.CGTrueT hT D T → ∀ a : ℕ, 0 < a →
      Nonempty (D.naut.CG a ≃ {ρ : HostCGu D.host a // GlobalTheory.HeightCounting.GoodAll ρ}) := by
  intro hT D T C a ha
  exact ⟨Equiv.ofBijective (fun π => ⟨C.e a π, C.good a π⟩)
    ⟨fun x y h => (C.e a).injective (congrArg Subtype.val h),
     fun ρ => let ⟨π, hπ⟩ := C.surj a ha ρ.1 ρ.2; ⟨π, Subtype.ext hπ⟩⟩⟩

def ofShared {hT : UpperTheory.Zero.LLC.RecTExists} {D : D7} {T : WDTie D.nd D.naut} (C : GlobalTheory.HeightCounting.CGTrueT hT D T) :
    GlobalTheory.RecT.CGTrueT (fun h => ParLawsT.locRecT hT h) D T where
  isRecT w := (GlobalTheory.RecT.isRecT_iff _).2 (ParLawsT.isRecT_locRecT hT (D.nd.plOm.2 w))
  e := C.e
  surj a ha π hπ := C.surj a ha π hπ
  zero := C.zero
  loc a π w _ := C.loc a π w
  tw := C.tw
  inf := C.inf
  csd := C.csd

end GlobalTheory.RecT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsAStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letterConditionGlobal_of_N1used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.N.LetterConditionGlobal D HW F := by
  first | exact @GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions | exact GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions | (intros; apply GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_heckeRow_good_at_goodPointLocalisation : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  first | exact @GlobalTheory.ExhaustRows.main | exact GlobalTheory.ExhaustRows.main | (intros; apply GlobalTheory.ExhaustRows.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdeleUnitCongrOne
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice

section Gen

variable {F : Type} [Field F] [NumberField F]

def mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F :=
  ⟨g, Filter.Eventually.of_forall hg⟩

theorem evalV_mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf g hg) = g v := rfl

theorem mkAf_mem (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : mkAf g hg ∈ intAf F := fun v => by
  rw [evalV_mkAf]; exact hg v

theorem val_eq_one_of_mul (v : HeightOneSpectrum (𝓞 F)) {a b : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) (hab : Valued.v (a * b) = 1) : Valued.v a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : _) = Valued.v a * Valued.v b := by rw [← map_mul, hab]
    _ ≤ Valued.v a * 1 := mul_le_mul_right hb (Valued.v a)
    _ = Valued.v a := mul_one _

theorem val_le_one {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : a ∈ v.adicCompletionIntegers F) : Valued.v a ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha

theorem mem_of_val {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) : a ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 ha

theorem val_natCast_le (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Valued.v (k : v.adicCompletion F) ≤ 1 :=
  val_le_one (natCast_mem (HeightOneSpectrum.adicCompletionIntegers F v) k)

theorem val_unit_of_rel (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {t q r : v.adicCompletion F}
    (hm : Valued.v (((2 * k + 1 : ℕ) : v.adicCompletion F)) < 1)
    (ht : Valued.v t ≤ 1) (hq : Valued.v q ≤ 1) (hr : Valued.v r ≤ 1)
    (h4 : (4 : v.adicCompletion F) = t * q + ((2 * k + 1 : ℕ) : v.adicCompletion F) * r) :
    Valued.v (-(k : v.adicCompletion F) * t) = 1 := by
  set M : v.adicCompletion F := ((2 * k + 1 : ℕ) : v.adicCompletion F) with hM
  have hk : Valued.v (k : v.adicCompletion F) ≤ 1 := val_natCast_le v k
  have h2k : Valued.v (2 * (k : v.adicCompletion F)) = 1 := by
    have e : 2 * (k : v.adicCompletion F) = -1 + M := by rw [hM]; push_cast; ring
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, map_one]; exact hm),
      Valuation.map_neg, map_one]
  have hsq : (2 * (k : v.adicCompletion F)) ^ 2 = (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) +
      M * ((k : v.adicCompletion F) ^ 2 * r) := by
    linear_combination (k : v.adicCompletion F) ^ 2 * h4
  have hsmall : Valued.v (M * ((k : v.adicCompletion F) ^ 2 * r)) < 1 := by
    rw [map_mul]
    calc Valued.v M * Valued.v ((k : v.adicCompletion F) ^ 2 * r) ≤ Valued.v M * 1 := by
          refine mul_le_mul_right ?_ _
          rw [map_mul, map_pow]
          calc Valued.v (k : v.adicCompletion F) ^ 2 * Valued.v r ≤ 1 * 1 := by
                gcongr
                exact pow_le_one₀ zero_le' hk
            _ = 1 := one_mul 1
      _ < 1 := by rw [mul_one]; exact hm
  have hprod : Valued.v ((-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q)) = 1 := by
    have e : (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) =
        (2 * (k : v.adicCompletion F)) ^ 2 + -(M * ((k : v.adicCompletion F) ^ 2 * r)) := by
      rw [hsq]; ring
    have hv1 : Valued.v ((2 * (k : v.adicCompletion F)) ^ 2) = 1 := by rw [map_pow, h2k, one_pow]
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, hv1]; exact hsmall), hv1]
  refine val_eq_one_of_mul v ?_ ?_ hprod
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v t ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v q ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1

end Gen

end GlobalTheory.UnitRootCong

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice

set_option maxHeartbeats 2000000 in

theorem exists_adele_unit_congr_one : ∀ (D : D7) (m : ℕ), Odd m → ∀ (z y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → (y : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) → (∃ w ∈ intAE D, (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w) → ∃ (b : (Af D.host.F)ˣ) (y' : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y' : Af D.host.F ⊗[D.host.F] D.host.E) = (y : Af D.host.F ⊗[D.host.F] D.host.E) * ((b : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) ∧ (y' : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ((y'⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ∃ w ∈ intAE D, (y' : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w := by
  classical
  intro D m hm z y hyI hyiI hyz hzw
  obtain ⟨w, hwI, hw⟩ := hzw
  obtain ⟨k, rfl⟩ := hm
  have hE := GlobalTheory.AdelicU.isCMExt_host D
  set M : ℕ := 2 * k + 1 with hMdef
  set yv : Af D.host.F ⊗[D.host.F] D.host.E := (y : Af D.host.F ⊗[D.host.F] D.host.E) with hyv
  set yi : Af D.host.F ⊗[D.host.F] D.host.E := ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) with hyi
  have hyy : yv * yi = 1 := y.mul_inv
  set s := sigR (Af D.host.F) D.sp.cm.sig yv with hs
  have hsI : s ∈ intAE D := GlobalTheory.PlaceIdem.sig_mem D hyI
  set T := Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hT
  set ι := algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hι
  have ht : yv + s = ι (T yv) := GlobalTheory.GaussMean.OneVec.add_sigR _ hE yv
  have hw' : (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = (M : Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    rw [hw, nsmul_eq_mul]
  have E3 : 2 * yv = ι (T yv) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s) := by
    linear_combination ht + hyz + s * hw'

  have hιI : ∀ a ∈ intAf D.host.F, ι a ∈ intAE D := fun a ha =>
    AddSubgroup.subset_closure ⟨a, ha, 1, by simp [hι, Algebra.TensorProduct.algebraMap_apply]⟩
  have hmulI : ∀ {a b}, a ∈ intAE D → b ∈ intAE D → a * b ∈ intAE D := fun ha hb =>
    GlobalTheory.HostAdeleIso.intAE_mul_mem D ha hb
  have hoI : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
    simpa using hιI 1 GlobalTheory.SplitHeckeLabel.one_mem_intAf
  have hnI : ∀ n : ℕ, (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := fun n => by
    rw [← nsmul_one]; exact nsmul_mem hoI n
  have hrI : w * s * yi ∈ intAE D := hmulI (hmulI hwI hsI) hyiI

  have hTl : ∀ (a : Af D.host.F) x, T (ι a * x) = a * T x := fun a x => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hT2 : T (ι 2) = 4 := by
    have h1 := GlobalTheory.GaussMean.OneVec.half_trace (Af D.host.F) hE (2 : Af D.host.F)
    have h2 := GlobalTheory.GaussMean.OneVec.half_two (F := D.host.F) (Af D.host.F)
    linear_combination 2 * h1 - T (ι 2) * h2
  have R1 : (4 : Af D.host.F) = T yv * T yi + (M : Af D.host.F) * T (w * s * yi) := by
    have e : ι 2 = ι (T yv) * yi + ι (M : Af D.host.F) * (w * s * yi) := by
      rw [map_ofNat, map_natCast]
      linear_combination yi * E3 - 2 * hyy
    rw [← hT2, e, map_add, hTl, hTl]

  let P : HeightOneSpectrum (𝓞 D.host.F) → Prop := fun v => Valued.v ((M : v.adicCompletion D.host.F)) < 1
  have hunit : ∀ v, P v → Valued.v (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv)) = 1 := fun v hv => by
    refine val_unit_of_rel v k hv (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyiI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hrI v)) ?_
    have := congrArg (evalV D.host.F v) R1
    simp only [map_add, map_mul, map_natCast, map_ofNat] at this
    exact this
  have hMone : ∀ v, ¬ P v → Valued.v ((M : v.adicCompletion D.host.F)) = 1 := fun v hv =>
    le_antisymm (val_natCast_le v M) (not_lt.1 hv)
  have hMne : ∀ v, ¬ P v → (M : v.adicCompletion D.host.F) ≠ 0 := fun v hv h => by
    have := hMone v hv; rw [h, map_zero] at this; exact zero_ne_one this
  let eg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F := fun v => if P v then 1 else 0
  let fg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then 0 else (M : v.adicCompletion D.host.F)⁻¹
  let cg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then -(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv) else 1
  let dg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv))⁻¹ else 1
  have heg : ∀ v, eg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [eg, hv, if_true, if_false] <;> [exact one_mem _; exact zero_mem _]
  have hfg : ∀ v, fg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [fg, hv, if_true, if_false]
    · exact zero_mem _
    · exact mem_of_val (by rw [map_inv₀, hMone v hv, inv_one])
  have hcg : ∀ v, cg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [cg, hv, if_true, if_false]
    · exact mem_of_val (hunit v hv).le
    · exact one_mem _
  have hdg : ∀ v, dg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [dg, hv, if_true, if_false]
    · exact mem_of_val (by rw [map_inv₀, hunit v hv, inv_one])
    · exact one_mem _
  set e := mkAf eg heg
  set f := mkAf fg hfg
  set c := mkAf cg hcg
  set d := mkAf dg hdg
  have hcd : c * d = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_mul, map_one, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [cg, dg, hv, if_true, if_false, mul_one]
    refine mul_inv_cancel₀ fun h0 => ?_
    have := hunit v hv; rw [h0, map_zero] at this; exact zero_ne_one this
  have hef : e + (M : Af D.host.F) * f = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add, map_mul, map_one, map_natCast, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, hv, if_true, if_false, mul_zero, add_zero, zero_add]
    exact mul_inv_cancel₀ (hMne v hv)
  have hce : c = e * (-(k : Af D.host.F) * T yv) + (M : Af D.host.F) * f := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add, map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast, evalV_mkAf, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, cg, hv, if_true, if_false, mul_zero, add_zero, zero_add, one_mul, zero_mul]
    exact (mul_inv_cancel₀ (hMne v hv)).symm
  have E1 : ι e + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f = 1 := by
    have := congrArg ι hef; rwa [map_add, map_mul, map_natCast, map_one] at this
  have E2 : ι c = ι e * (-(k : Af D.host.F ⊗[D.host.F] D.host.E) * ι (T yv)) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f := by
    rw [hce, map_add, map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast]
  have E4 : ι c * ι d = 1 := by rw [← map_mul, hcd, map_one]
  set W := ι e * (yv - (k : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s)) + ι f * (yv - 1) with hW
  have hmain : yv - ι c = (M : Af D.host.F ⊗[D.host.F] D.host.E) * W := by
    have hM : (M : Af D.host.F ⊗[D.host.F] D.host.E) = 2 * (k : Af D.host.F ⊗[D.host.F] D.host.E) + 1 := by
      rw [hMdef]; push_cast; ring
    rw [hW]
    linear_combination (-1 : Af D.host.F ⊗[D.host.F] D.host.E) * E2 - yv * E1 - (k : Af D.host.F ⊗[D.host.F] D.host.E) * ι e * E3 - ι e * yv * hM
  have hWI : W ∈ intAE D := by
    rw [hW]
    refine add_mem (hmulI (hιI _ (mkAf_mem eg heg)) (sub_mem hyI (hmulI (hnI k) (hmulI hwI hsI))))
      (hmulI (hιI _ (mkAf_mem fg hfg)) (sub_mem hyI hoI))
  let b : (Af D.host.F)ˣ := ⟨d, c, by rw [mul_comm]; exact hcd, hcd⟩
  refine ⟨b, y * Units.map ι.toMonoidHom b, ?_, ?_, ?_, W * ι d, ?_, ?_⟩
  · rw [Units.val_mul, Units.coe_map]
    rfl
  · exact hmulI hyI (hιI _ (mkAf_mem dg hdg))
  · rw [mul_inv_rev, Units.val_mul, ← map_inv, Units.coe_map]
    exact hmulI (hιI _ (mkAf_mem cg hcg)) hyiI
  · exact hmulI hWI (hιI _ (mkAf_mem dg hdg))
  · rw [Units.val_mul, Units.coe_map, nsmul_eq_mul]
    show yv * ι d - 1 = _
    linear_combination ι d * hmain + E4

end GlobalTheory.UnitRootCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePlaceValuationCompRingEquivStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePlace_valuation_comp_ringEquiv : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L) (la : HeightOneSpectrum (𝓞 L)), ∃ la' : HeightOneSpectrum (𝓞 K), ∀ y : K, la'.valuation K y = la.valuation L (e y) := by
  first | exact @GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv | exact GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv | (intros; apply GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRefinedFlagChartIntegralPointsInOpenStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_refined_flagChart_integral_points_in_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (S : Set Y.X) (P : PChart Xo c (algebraMap O c.F)) (T : CDVR) (io : c.F →+* T.Fr), IsOpen S → letI := io.toAlgebra; ∀ (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] T.Fr) (z : FrPt Xo c T.Fr), (∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) → FrMap ψ (P.y e he) z → ExtIn Y S T io z.x → ∃ (P' : PChart Xo c (algebraMap O c.F)) (e' : P'.Ω) (he' : e' ∈ P'.es) (ψ' : P'.R e' →ₐ[c.F] T.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T (ψ' g)) ∧ FrMap ψ' (P'.y e' he') z ∧ ∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ a : O, InV T₁ (io₁ (algebraMap O c.F a))) → letI := io₁.toAlgebra; ∀ (ψ₁ : P'.R e' →ₐ[c.F] T₁.Fr) (z₁ : FrPt Xo c T₁.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T₁ (ψ₁ g)) → FrMap ψ₁ (P'.y e' he') z₁ → ExtIn Y S T₁ io₁ z₁.x := by
  first | exact @GlobalTheory.GoodRefine.exists_refine_extIn | exact GlobalTheory.GoodRefine.exists_refine_extIn | (intros; apply GlobalTheory.GoodRefine.exists_refine_extIn <;> assumption)
end

