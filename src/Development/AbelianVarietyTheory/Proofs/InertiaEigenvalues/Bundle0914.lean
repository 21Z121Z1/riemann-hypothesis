import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2TwistSetup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmJumpSetup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MulVecMemLatS
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0904
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2TwistSetupStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG2_twist_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → ∀ i, EmbeddingTypes.admG2 i (X.r i) ep := by
  first | exact @GlobalTheory.JumpShapeAt.main | exact GlobalTheory.JumpShapeAt.main | (intros; apply GlobalTheory.JumpShapeAt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG5SetupStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG5_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admG5 i (X.r i) (X.ρ i) π := by
  first | exact @GlobalTheory.NLinkTameShape.main | exact GlobalTheory.NLinkTameShape.main | (intros; apply GlobalTheory.NLinkTameShape.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmJumpSetupStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admJump_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes X.r ep L := by
  first | exact @GlobalTheory.HostJumpWin.main | exact GlobalTheory.HostJumpWin.main | (intros; apply GlobalTheory.HostJumpWin.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageSecondConditionStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_image_second_condition : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), GlobalTheory.NFacts.Facts D nch → AdmissibleParameterJ.AdmPar L → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG2 i r (fun _ => ρ) π := by
  first | exact @GlobalTheory.AdmGTwoLarge.main | exact GlobalTheory.AdmGTwoLarge.main | (intros; apply GlobalTheory.AdmGTwoLarge.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageThirdConditionStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_image_third_condition : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), GlobalTheory.NFacts.Facts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG3 i r (fun _ => ρ) π := by
  first | exact @GlobalTheory.AdmGThreeRest.main | exact GlobalTheory.AdmGThreeRest.main | (intros; apply GlobalTheory.AdmGThreeRest.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundOfTwistingEigenSeriesFactsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bound_of_twisting_eigen_series_facts : Hypotheses₂ → ∃ CT : ℕ, ∀ (D : D7) (nch : NChoice D), GlobalTheory.NFacts.Facts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → PairedCharacterCondition.aux₃ (D := D) (8 * (CT : ℝ)) CT := by
  first | exact @GlobalTheory.NormFromFacts.main | exact GlobalTheory.NormFromFacts.main | (intros; apply GlobalTheory.NormFromFacts.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiDeRhamWeilDeligneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chi_de_rham_weil_deligne : ∀ (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.IsdRW D.loc D.nbr i w hw (PairedCharacterCondition.chiGL (D := D) i) ∧ D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL (D := D) i)) w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  first | exact @GlobalTheory.ChiOneAbove.main | exact GlobalTheory.ChiOneAbove.main | (intros; apply GlobalTheory.ChiOneAbove.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiTContIsCrysMultV
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section

namespace GlobalTheory.UseLoc

theorem chiT_cont_isCrys_multV : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ), 1 ≤ c → c ≤ D.R.t → TruncatedSeriesCountingIdentities.admG2 i r ρ π → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1)) → IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1)) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) ∧ ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) τ (a + ((c : ℤ) - 1)) = multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ a := by
  intro D i r ρ π w hw C θ c h1 h2 hG2 hθc hθ
  set ψ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ := chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) with hψ
  have hsplit : ∀ g, ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
        ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
    intro g
    simp [tableLineDegreeTwo.charL, chiT, hψ]
  have hent : ∀ g, TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c) g 0 0 =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
    intro g
    change TruncatedSeriesCountingIdentities.CoefExt.inc C (algebraMap _ _ ((D.nbr i w hw).eO
      (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatO_apply]
    rfl
  let f : (Fin 1 → ↥C.LL.1) ≃ₗ[↥C.LL.1] ↥C.LL.1 := LinearEquiv.funUnique (Fin 1) ↥C.LL.1 ↥C.LL.1
  have hf : ∀ g x, f (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c)) g x) =
      Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ) g (f x) := by
    intro g x
    show (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c) g).mulVec x 0 =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) • x 0
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, hent, smul_eq_mul]
  have cψ : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ)) :=
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ f hf (GlobalTheory.RestPtAssembly.chiRat_isCrys D i w hw C c h1 h2)
  have jψ : ∀ τ, IsJumpV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ)) τ ((c : ℤ) - 1) :=
    fun τ => GlobalTheory.HTW.isJumpV_of_injective _ _ _ f.toLinearMap f.injective hf τ _
      ((((hG2 w hw C).1.2.2.2.1 c h1 h2 τ ((c : ℤ) - 1))).2 rfl)
  have tw : IsTwistRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ))
      (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) := by
    refine ⟨LinearEquiv.refl _ _, fun g x => ?_⟩
    simp only [Formalism.WeaklyAdmissibleFiltrations.charRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply,
      LinearEquiv.refl_apply, smul_eq_mul, hsplit]
    ring
  obtain ⟨hcr, hm⟩ := GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL ↥C.LL.1 _ ↥C.LL.1 _ _ tw cψ hθ
  refine ⟨?_, hcr, fun τ a => hm τ a _ (jψ τ)⟩
  have hO : Continuous (fun h : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) h : (D.nd.O i)ˣ) : D.nd.O i)) := by
    have e : (fun h : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) h : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun h => ((D.nd.chi i c h : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i 1 h⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext h
      simp [chiU, map_inv]
    rw [e]
    exact (D.nd.chi_cont i c).mul ((D.nd.chi_cont i 1).comp continuous_inv)
  have hi : Continuous (IntermediateField.inclusion C.le) :=
    continuous_induced_rng.2 continuous_subtype_val
  have hψc : Continuous fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) :=
    hi.comp (continuous_subtype_val.comp ((D.nbr i w hw).eO_cont.comp
      (hO.comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)))))
  have e2 : (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1)) =
      fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
        ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := funext hsplit
  rw [e2]
  exact hψc.mul hθc

end GlobalTheory.UseLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDescentEnlargementCoefficients
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescBD

section Abstract

theorem exists_retr_abs {Z O O' K K' : Type} [CommRing Z] [CommRing O] [CommRing O'] [IsDedekindDomain O]
    [Field K] [Field K'] [Algebra O K] [IsFractionRing O K] [Algebra Z O] [Algebra Z O'] [Module.Finite Z O']
    (f : O →+* O') (hf : ∀ c, algebraMap Z O' c = f (algebraMap Z O c)) (j : O' →+* K') (φ : K →+* K')
    (hc : ∀ a, φ (algebraMap O K a) = j (f a)) (hs : ∀ x : K', ∃ a : K, a ≠ 0 ∧ ∃ y, j y = φ a * x) :
    ∃ R : K' →+ K, (∀ a x, R (φ a * x) = a * R x) ∧ (∀ a, R (φ a) = a) ∧ ∀ x, ∃ y, j y = φ (R (j x)) := by
  letI : Algebra K K' := φ.toAlgebra
  letI : Algebra O K' := (φ.comp (algebraMap O K)).toAlgebra
  letI : Algebra O O' := f.toAlgebra
  letI : Algebra O' K' := j.toAlgebra
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower O O' K' := IsScalarTower.of_algebraMap_eq hc
  haveI : IsScalarTower Z O O' := IsScalarTower.of_algebraMap_eq hf
  haveI : Module.Finite O O' := Module.Finite.of_restrictScalars_finite Z _ _
  let L : Submodule O K' := LinearMap.range (IsScalarTower.toAlgHom O O' K').toLinearMap
  haveI : Module.Finite O L := inferInstance
  have hsp : Submodule.span K (L : Set K') = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, y, hy⟩ := hs x
    have e : x = a⁻¹ • j y := by
      rw [hy]
      change x = φ a⁻¹ * (φ a * x)
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.St.G.Inter.exists_retraction (O := O) (K := K)
    (Algebra.linearMap K K') φ.injective L hsp
  exact ⟨T.toAddMonoidHom, fun a x => T.map_smul a x, hT, fun x => hT' (j x) ⟨x, rfl⟩⟩

theorem mem_BD_iff {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) O) (z : Γ → (Fin k → K) ⧸ stdG O K k) :
    z ∈ BD (stdLatG hinj N) ↔ ∃ m : Fin k → K, ∀ g v, Submodule.Quotient.mk v = z g →
      ∃ u : Fin k → O, ∀ j, algebraMap O K (u j) = ∑ t, algebraMap O K (N g j t) * m t - m j - v j := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨m, fun g v hv => ?_⟩
    have hg := (congrFun hm g).trans hv.symm
    have hg' : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := (Submodule.Quotient.eq _).1 hg
    obtain ⟨u, hu⟩ := hg'
    exact ⟨u, fun j => congrFun hu j⟩
  · rintro ⟨m, hm⟩
    refine ⟨Submodule.Quotient.mk m, funext fun g => ?_⟩
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (z g)
    obtain ⟨u, hu⟩ := hm g v hv
    have key : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := ⟨u, funext hu⟩
    exact ((Submodule.Quotient.eq _).2 key).trans hv

theorem desc_abs {O K O' K' : Type} [CommRing O] [Field K] [Algebra O K] [CommRing O'] [Field K'] [Algebra O' K']
    (hinj : Function.Injective (algebraMap O K)) (hinj' : Function.Injective (algebraMap O' K'))
    (f : O →+* O') (φ : K →+* K') (hc : ∀ a, algebraMap O' K' (f a) = φ (algebraMap O K a))
    (R : K' →+ K) (hR : ∀ a x, R (φ a * x) = a * R x) (hR1 : ∀ a, R (φ a) = a)
    (hRO : ∀ x, ∃ y, algebraMap O K y = R (algebraMap O' K' x))
    {Γ : Type} [Group Γ] {k : ℕ} (N : Γ →* Matrix (Fin k) (Fin k) O)
    (q : (Fin k → K) ⧸ stdG O K k → (Fin k → K') ⧸ stdG O' K' k)
    (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk (fun j => φ (v j)))
    (z : Γ → (Fin k → K) ⧸ stdG O K k) (hz : (fun g => q (z g)) ∈ BD (stdLatG hinj' (mapM f N))) :
    z ∈ BD (stdLatG hinj N) := by
  obtain ⟨m, hm⟩ := (mem_BD_iff hinj' (mapM f N) (fun g => q (z g))).1 hz
  refine (mem_BD_iff hinj N z).2 ⟨fun j => R (m j), fun g v hv => ?_⟩
  obtain ⟨u, hu⟩ := hm g (fun j => φ (v j)) (by rw [← hv, hq])
  choose r hr using hRO
  refine ⟨fun j => r (u j), fun j => ?_⟩
  have hj : algebraMap O' K' (u j) = ∑ t, algebraMap O' K' (f (N g j t)) * m t - m j - φ (v j) := hu j
  rw [hr, hj, map_sub, map_sub, map_sum, hR1]
  simp only [hc, hR]

end Abstract

section Gen
variable {l : ℕ} [Fact l.Prime]

theorem exists_retr {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ R : ↥LL'.1 →+ ↥LL.1, (∀ a x, R (IntermediateField.inclusion h a * x) = a * R x) ∧
      (∀ a, R (IntermediateField.inclusion h a) = a) ∧ ∀ x ∈ OL LL', R x ∈ OL LL := by
  haveI := LL.2
  haveI := LL'.2
  haveI : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL') :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL'.1 (integralClosure ℤ_[l] ↥LL'.1)
  obtain ⟨R, h1, h2, h3⟩ := exists_retr_abs (Z := ℤ_[l]) (O := ↥(OL LL)) (O' := ↥(OL LL')) (K := ↥LL.1)
    (K' := ↥LL'.1) (incO h) (fun _ => rfl) (OL LL').val.toRingHom (IntermediateField.inclusion h).toRingHom
    (fun _ => rfl) (fun x => by
      have hx : IsAlgebraic ℤ_[l] x :=
        (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL'.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
      obtain ⟨y, hy, hi⟩ := hx.exists_integral_multiple
      refine ⟨algebraMap ℤ_[l] ↥LL.1 y, ?_, ⟨y • x, hi⟩, Algebra.smul_def y x⟩
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
      simpa using hy)
  refine ⟨R, h1, h2, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h3 ⟨x, hx⟩
  have hy' : (y : ↥LL'.1) = ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x) := hy
  have : IsIntegral ℤ_[l] (((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x)) := hy' ▸ y.2
  exact (isIntegral_algHom_iff ((IntermediateField.inclusion h).restrictScalars ℤ_[l])
    (IntermediateField.inclusion h).injective).1 this

theorem desc {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) ↥(OL LL))
    (z : Γ → (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k)
    (hz : (fun g => liftQ h k (z g)) ∈
      BD (stdLatG (O := ↥(OL LL')) (LL := ↥LL'.1) Subtype.val_injective (mapM (incO h) N))) :
    z ∈ BD (stdLatG (O := ↥(OL LL)) (LL := ↥LL.1) Subtype.val_injective N) := by
  obtain ⟨R, hR, hR1, hRO⟩ := exists_retr h
  exact desc_abs (O := ↥(OL LL)) (K := ↥LL.1) (O' := ↥(OL LL')) (K' := ↥LL'.1) Subtype.val_injective
    Subtype.val_injective (incO h) (IntermediateField.inclusion h).toRingHom (fun _ => rfl) R hR hR1
    (fun x => ⟨⟨R x, hRO _ x.2⟩, rfl⟩) N (liftQ h k) (liftQ_mk h k) z hz

end Gen

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ BD (latC C (locOC C M)) → z ∈ BD (Br.locLat D.nbr i w hw M) :=
  fun D i w hw C _ M z hz => desc C.le (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w))) z hz

end GlobalTheory.UseLoc.DescBD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorPrimesLtSpecialPrimeThresholdEventuallyStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductorPrimes_lt_specialPrimeThreshold_eventually : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x),
    ((Fm.D x a).host.q : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧ ((Fm.D x a).host.d : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧
      ∀ p ∈ (Fm.D x a).host.small, (p : ℝ) < LevelStarExponents.lStar (Fm.L x a) := by
  first | exact @GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar | exact GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar | (intros; apply GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundExtendedOfRationalBoundStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceBound_extended_of_rationalBound : ∀ (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), π ∈ D.nd.Z i → (∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) → (Br.sFin D.loc D.nbr i (fun _ => ρ) π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i (fun _ => ρ) π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})) → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vCC D i π ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sPi D i π ρ + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.shaSum D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vClass D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.epsQ D i := by
  first | exact @GlobalTheory.Proof.congruenceBound_extended_of_rationalBound.congBound_of_rational | exact GlobalTheory.Proof.congruenceBound_extended_of_rationalBound.congBound_of_rational | (intros; apply GlobalTheory.Proof.congruenceBound_extended_of_rationalBound.congBound_of_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualOfLabelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_dual_of_labels : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), LabAll D P.T → ConjDual D := by
  first | exact @GlobalTheory.ConjPlaceDual.main | exact GlobalTheory.ConjPlaceDual.main | (intros; apply GlobalTheory.ConjPlaceDual.main <;> assumption)
end

