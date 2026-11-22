import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.AdmissibleDesigns.StatementOneBFromUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0768
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0299
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalArtinHasNormGroups
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0376
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import GroundTheory.LocalFields.LocalArtinMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPoint
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.SelmerBoundAtPoint

theorem finCore : Formalism.MainNotions.N.K.H0.FinCore :=
  ⟨fun {D} i r ρ π g2 w hw => GlobalTheory.FiniteTwistInvariants.main D i r ρ π g2 w hw,
   fun {D} i w hw e he => GlobalTheory.FinInvKO.finiteLength_invariants_negTwist_KmodO D i w hw e he⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hA hT hE D i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin tie a51 unr hR hL hTB
  have : Fact ReciprocityTheory.ChartRestriction.T2.Core := ⟨GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler hA hT hE⟩
  have : Fact Formalism.MainNotions.N.K.H0.FinCore := ⟨finCore⟩
  exact Formalism.MainNotions.N.K.Closed.theorem_n5_from_inputs i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin
    tie a51 (Formalism.MainNotions.N.K.StD.unramified_input_of_admitted i dc unr) hR hL hTB

end GlobalTheory.SelmerBoundAtPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationalityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_rationality : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → EvO A M C tp.tup SumRepresentations.hypO := by
  first | exact @GlobalTheory.LargeO.evO_hypO | exact GlobalTheory.LargeO.evO_hypO | (intros; apply GlobalTheory.LargeO.evO_hypO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilDoublingProductRationalTranslateEqFram
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLagTerms
variable {D : D7}

theorem cA_incA_loc (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem adjO_mul_rat (V W : HSp D) (y : Mx D V.rank W.rank) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    GlobalTheory.PairLift.adjO V W (HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (M.map (incA D))) =
      ratMul (hAdj W M) (GlobalTheory.PairLift.adjO V W y) := by
  have e : ((M.map (incA D)).map (cA D))ᵀ = ((M.map star)ᵀ).map (incA D) := by
    ext i j; simp [cA_incA_loc]
  rw [GlobalTheory.AdjLawPf.adjO_eq, GlobalTheory.AdjLawPf.adjO_eq, GlobalTheory.AdjLawPf.conjT_mul, e]
  unfold ratMul hAdj
  rw [Matrix.map_mul, Matrix.map_mul]
  have g1 : (HSpace.gram W).map (incA D) * (HSpace.gram W)⁻¹.map (incA D) = 1 :=
    mul_eq_one_comm.1 (GlobalTheory.AdjLawPf.inv_mul_gram W)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((HSpace.gram W).map (incA D)), g1, Matrix.one_mul]

theorem act_lagr (V W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (hg : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) (y : Mx D V.rank W.rank) :
    actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y) =
      HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D)) := by
  unfold actO
  rw [inv_inv, hg, GlobalTheory.AdjLawPf.mt_one, Matrix.one_mul]

theorem resL_lagr (V W : HSp D) (y : Mx D V.rank W.rank)
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL W V (HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D))) =
      HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (((blk W g₀).toBlocks₁₁ - (blk W g₀).toBlocks₂₁).map (incA D)) := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [GlobalTheory.SiegelFormula.lagr, Matrix.of_apply, GlobalTheory.Doubling.pairVec_inl, GlobalTheory.Doubling.pairVec_inr, blk,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.sub_apply, map_sub, mul_sub,
    Finset.sum_sub_distrib, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  abel

theorem resR_lagr (V W : HSp D) (y : Mx D V.rank W.rank)
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    -GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR W V (HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D))) =
      HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (((blk W g₀).toBlocks₂₂ - (blk W g₀).toBlocks₁₂).map (incA D)) := by
  ext i j
  simp only [Matrix.neg_apply, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [GlobalTheory.SiegelFormula.lagr, Matrix.of_apply, GlobalTheory.Doubling.pairVec_inl, GlobalTheory.Doubling.pairVec_inr, blk,
    Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.sub_apply, map_sub, mul_sub,
    Finset.sum_sub_distrib, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  abel

theorem dbl_actO_lagr : ∀ (D : D7) (V W : HSp D) (f₁ f₂ : WO V W → ℂ) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E),
    Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∀ (y : Mx D V.rank W.rank),
    GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) =
      f₁ (ratMul (frameOf W g₀).1 (GlobalTheory.PairLift.adjO V W y)) * star (f₂ (ratMul (frameOf W g₀).2 (GlobalTheory.PairLift.adjO V W y))) := by
  intro D V W f₁ f₂ γ g₀ hg y
  rw [act_lagr V W γ g₀ hg y, GlobalTheory.SWPairProof.dbl_apply, resL_lagr, resR_lagr, adjO_mul_rat, adjO_mul_rat,
    frameOf_fst, frameOf_snd, starRingEnd_apply, mul_comm]

end GlobalTheory.SWLagTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmoothWeilCharEqOneOfToAbsGaloisAbEqOne
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilCharKer

open GlobalTheory.LocDict GlobalTheory.HeckeGal Neutral.B1

theorem commutator_le_of_dense {Γ W : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [Group W] (ψ : W →* Γ) (hd : ∀ (g : Γ) (H : Subgroup Γ), IsOpen (H : Set Γ) → ∃ σ : W, g⁻¹ * ψ σ ∈ H)
    (F : Subgroup Γ) (hF : IsOpen (F : Set Γ)) (hc : ∀ σ τ : W, ψ (σ * τ * σ⁻¹ * τ⁻¹) ∈ F) :
    commutator Γ ≤ F := by
  have : Finite (Γ ⧸ F) := Subgroup.quotient_finite_of_isOpen F hF
  have : F.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hN : IsOpen (F.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (F.normalCore_isClosed (F.isClosed_of_isOpen hF))
  rw [commutator, Subgroup.commutator_le]
  intro g _ k _
  obtain ⟨σ, hσ⟩ := hd g _ hN
  obtain ⟨τ, hτ⟩ := hd k _ hN
  have e1 : QuotientGroup.mk' F.normalCore g = QuotientGroup.mk' F.normalCore (ψ σ) := QuotientGroup.eq.2 hσ
  have e2 : QuotientGroup.mk' F.normalCore k = QuotientGroup.mk' F.normalCore (ψ τ) := QuotientGroup.eq.2 hτ
  have e3 : QuotientGroup.mk' F.normalCore (ψ (σ * τ * σ⁻¹ * τ⁻¹)) =
      QuotientGroup.mk' F.normalCore (g * k * g⁻¹ * k⁻¹) := by
    simp only [map_mul, map_inv, e1, e2]
  have e4 := F.mul_mem (hc σ τ) (F.normalCore_le (QuotientGroup.eq.1 e3))
  rw [mul_inv_cancel_left] at e4
  exact e4

theorem index_normGroup {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [CharZero K] (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsAbelianGalois K L] :
    (normGroup K L).index = Nat.card (L ≃ₐ[K] L) := by
  have e : normGroup K L = (GroundTheory.LocalField.normUnits K L).range := rfl
  rw [e, ← GroundTheory.LocalField.ker_restrictAb_localArtinMap (Ω := AlgebraicClosure K) L, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (GroundTheory.LocalField.surjective_restrictAb_localArtinMap L), Subgroup.card_top]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem art_inj {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    Function.Injective fun x : (w.adicCompletion E)ˣ => art (localIdele E w x) :=
  GlobalTheory.T.globalArtin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w

theorem exists_inverse (h : IsPlaceOver A w) {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧
      ∀ σ : Weil h, art (localIdele E w (a σ)) = toAb E Ω σ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.LocNormGrp.art_range_weil E Ω A w h art ha
  choose a ha' using h1
  refine ⟨MonoidHom.mk' a fun σ τ => art_inj ha ?_, fun y => ?_, ha'⟩
  · simp only [map_mul, ha', Subgroup.coe_mul]
  · obtain ⟨τ, hτ⟩ := h2 y
    exact ⟨τ, art_inj ha ((ha' τ).trans hτ.symm)⟩

theorem mem_of_toAb_eq_one (h : IsPlaceOver A w) (H : Subgroup (Weil h)) (hfin : H.FiniteIndex)
    (hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H}) (hcomm : ∀ σ τ : Weil h, σ * τ * σ⁻¹ * τ⁻¹ ∈ H)
    (σ : Weil h) (hσ : toAb E Ω σ = 1) : σ ∈ H := by
  obtain ⟨K, hK, hloc, hHK⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hfin hop
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  obtain ⟨W, h'⟩ := GlobalTheory.LocNormGrp.exists_place h K
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb E Ω A w h
  obtain ⟨ι', hι'⟩ := GlobalTheory.LocDict.exists_isLocEmb K Ω A W h'
  obtain ⟨f, b, hf, hb1, hb2, hfE, -, -, -, hNc, hNg⟩ := GlobalTheory.T.local_embeddings_tower_compatible E K Ω A w W h h' hloc ι ι' hι hι'
  letI := f.toAlgebra
  have hN := GlobalTheory.T.completion_embedding_compatible_closures E K w W (fun x : K => ι (algebraMap K Ω x)) f b hf hb1
    (fun x => by rw [hb2, ι'.commutes, IsScalarTower.algebraMap_apply K (W.adicCompletion K)]) hfE
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds E Ω
  obtain ⟨artK, hartK⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  obtain ⟨a, hasurj, ha⟩ := exists_inverse h hart
  let N := Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)
  have key := GlobalTheory.LocNormGrp.art_norm_eq_res E K Ω art artK hart hartK w W
    (GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h') N (Continuous.units_map _ hNc) fun z => Units.ext (hNg z)
  obtain ⟨h1, -⟩ := GlobalTheory.LocNormGrp.art_range_weil K Ω A W h' artK hartK
  set Kw := w.adicCompletion E
  have : CharZero Kw := charZero_of_injective_algebraMap (algebraMap E Kw).injective
  have : IsGalois Kw (Kbar w) := IsAlgClosure.isGalois Kw (Kbar w)
  set L := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hL

  have hHN : H ≤ (normGroup Kw L).comap a := fun s hs => by
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_weil_of_fixes' E K Ω A w W h h' s ((hHK s).1 hs)
    obtain ⟨y, hy⟩ := h1 τ
    rw [Subgroup.mem_comap, hN]
    exact ⟨y, art_inj hart ((key y τ s hτ hy).trans (ha s).symm)⟩

  have hfd : FiniteDimensional Kw L := by
    let pb := Field.powerBasisOfFiniteOfSeparable E K
    let j : K →ₐ[E] Kbar w := ι.comp K.val
    have hfd0 : FiniteDimensional Kw (IntermediateField.adjoin Kw {j pb.gen}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    have hle : L ≤ IntermediateField.adjoin Kw {j pb.gen} := by
      rw [hL, IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      obtain ⟨p, rfl⟩ := pb.exists_eq_aeval' x
      show j (aeval pb.gen p) ∈ IntermediateField.adjoin Kw {j pb.gen}
      rw [← aeval_algHom_apply, ← aeval_map_algebraMap Kw]
      exact IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  obtain ⟨θ, hθ, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hψ : ∀ s : Weil h, Lifts ι (ψ s) (s : G E Ω) := fun s => hl _
  have hψ' : ∀ (s : Weil h) (g : GalLoc w), Lifts ι g s → ψ s = g := fun s g hg => by
    have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) s := by
      have := hl (θ.symm g)
      rw [θ.apply_symm_apply] at this
      exact Subtype.ext (this.eq hg)
    show θ _ = g
    rw [← e, θ.apply_symm_apply]
  have hHL : ∀ s : Weil h, s ∈ H ↔ ψ s ∈ L.fixingSubgroup := fun s => by
    rw [hHK, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, hL, IntermediateField.adjoin_le_iff]
    constructor
    · rintro hs _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      refine (Subgroup.zpowers_le (H := MulAction.stabilizer (GalLoc w) (ι (algebraMap K Ω x)))).2 ?_ hg
      show ψ s (ι x) = ι x
      rw [hψ, hs]
    · intro hs x
      have := (IntermediateField.mem_fixedField_iff _ _).1 (hs ⟨x, rfl⟩) _ (Subgroup.mem_zpowers _)
      rw [hψ] at this
      exact ι.toRingHom.injective this
  have hLo : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := L.fixingSubgroup_isOpen
  have hcl : commutator (GalLoc w) ≤ L.fixingSubgroup :=
    commutator_le_of_dense ψ (fun g U hU => by
      obtain ⟨s, g', h1, h2⟩ := GlobalTheory.LocDec.exists_lifts_mul_mem A w h ι θ hθ hl g U hU
      exact ⟨s, by rwa [hψ' s g' h1]⟩) _ hLo fun s t => (hHL _).1 (hcomm s t)
  have hnorm : L.fixingSubgroup.Normal := Subgroup.Normal.of_commutator_le _ hcl
  have hgal : IsGalois Kw L := (InfiniteGalois.normal_iff_isGalois L).1 hnorm
  have hab : IsAbelianGalois Kw L := GroundTheory.LocalField.isAbelianGalois_of_le_maximalAbelianExtension L (by
    rw [GroundTheory.LocalField.maximalAbelianExtension, IntermediateField.le_iff_le]
    exact Subgroup.topologicalClosure_minimal _ hcl (Subgroup.isClosed_of_isOpen _ hLo))

  have hHker : H = ((AlgEquiv.restrictNormalHom L).comp ψ).ker := by
    ext s
    rw [hHL, ← IntermediateField.restrictNormalHom_ker]; rfl
  have i1 : H.index ≤ Nat.card (L ≃ₐ[Kw] L) := by
    rw [hHker, Subgroup.index_ker]
    exact Subgroup.card_le_card_group _
  have i2 : ((normGroup Kw L).comap a).index = Nat.card (L ≃ₐ[Kw] L) := by
    rw [Subgroup.index_comap_of_surjective _ hasurj, index_normGroup]
  have i3 := Subgroup.relIndex_mul_index hHN
  have i4 : H.relIndex ((normGroup Kw L).comap a) = 1 := by
    have := hfin.index_ne_zero
    rw [i2] at i3
    have hp : 0 < Nat.card (L ≃ₐ[Kw] L) := Nat.card_pos
    generalize H.relIndex ((normGroup Kw L).comap a) = r at i3
    rcases r with _ | _ | r
    · omega
    · rfl
    · nlinarith
  refine Subgroup.relIndex_eq_one.1 i4 ?_
  have : a σ = 1 := art_inj hart (by simp only [ha, hσ, map_one])
  rw [Subgroup.mem_comap, this]
  exact Subgroup.one_mem _

theorem deg_eq_zero_of_toAb_eq_one (h : IsPlaceOver A w) (σ : Weil h) (hσ : toAb E Ω σ = 1) : deg σ = 0 := by
  let n := (deg σ).natAbs + 1
  let r : Weil h →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp (degHom h)
  have hr : ∀ s, s ∈ r.ker ↔ (n : ℤ) ∣ deg s := fun s => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; rfl
  have := mem_of_toAb_eq_one h r.ker inferInstance
    (by simp [hr]) (fun s t => by simp [hr]) σ hσ
  rw [hr] at this
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by simp only [Int.natAbs_natCast]; omega)

theorem apply_eq_one_of_toAb_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ξ : Weil h →* ℂˣ), GlobalTheory.WeilDeligne.IsSmooth ξ → ∀ σ : Weil h, GlobalTheory.HeckeGal.toAb E Ω σ = 1 → ξ σ = 1 := by
  intro E Ω _ _ _ _ _ A w h ξ hξ σ hσ
  let ξ' : Weil h →* ℂˣ := ξ * unrChar h (ξ (frob h))⁻¹
  have h0 : ∀ s, deg s = 0 → ξ' s = ξ s := fun s hs => by simp [ξ', hs]
  have h1 : ξ' (frob h) = 1 := by simp [ξ']
  have hop : IsOpen {s : Ine (F := E) A | ineIncl h s ∈ ξ'.ker} := by
    simp only [MonoidHom.mem_ker, h0 _ (deg_ineIncl _)]
    exact hξ
  have := compactSpace_Ine (E := E) A
  have hq : Finite (Ine (F := E) A ⧸ (ξ'.comp (ineIncl h)).ker) := Subgroup.quotient_finite_of_isOpen _ hop
  have hr : Finite (ξ'.comp (ineIncl h)).range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).toEquiv
  have hle : ξ'.range ≤ (ξ'.comp (ineIncl h)).range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
    refine ⟨t, ?_⟩
    conv_rhs => rw [ht, map_mul, map_zpow, h1, _root_.one_zpow, one_mul]
    rfl
  have hr' : Finite ξ'.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have := mem_of_toAb_eq_one h ξ'.ker inferInstance hop (fun s t => by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (ξ' s) (ξ' t)]
    group) σ hσ
  rw [← h0 σ (deg_eq_zero_of_toAb_eq_one h σ hσ)]
  exact this

end GlobalTheory.WeilCharKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramifiedStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (α : Fin x.1 → ℂˣ), HasSatake x.rep α → IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  first | exact @GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar | exact GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar | (intros; apply GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceComponentUnitaryAdelicDeterminedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_component_unitaryAdelic_determined : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (x y : GAf L n), s.loc n x = s.loc n y → (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) := by
  first | exact @GlobalTheory.SplitCompat.compAt_map_eq_of_loc_eq | exact GlobalTheory.SplitCompat.compAt_map_eq_of_loc_eq | (intros; apply GlobalTheory.SplitCompat.compAt_map_eq_of_loc_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSphericalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), IsUnif L s.v ϖ → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f := by
  first | exact @GlobalTheory.HeckeScalarSph.tN_scalar | exact GlobalTheory.HeckeScalarSph.tN_scalar | (intros; apply GlobalTheory.HeckeScalarSph.tN_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsidePlaceMemDefiniteUnitaryLocalPointsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivOutside_place_mem_definiteUnitaryLocalPoints : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ y : GAf L n, TrivOutside {v} y → F.j y ∈ locU n w := by
  first | exact @GlobalTheory.LocMemTransfer.mem_locU | exact GlobalTheory.LocMemTransfer.mem_locU | (intros; apply GlobalTheory.LocMemTransfer.mem_locU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistGood

theorem ramExactly_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) {M : Type} [CommGroup M]
    (ψ : G D.host.E N.Om →* M) (Q : Set (Pl D.host.E)) (hA : AntiHom X.cc ψ) (hR : RamExactly ψ Q) :
    ∀ P ∈ Q, ∀ P' : Pl D.host.E, IsConjPl D.host P P' → P' ∈ Q := by
  intro P hP P' hPP
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := X.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, X.cc (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E (j.comp (algebraMap D.host.E N.Om)) x).symm
  have hs : ∀ x, X.cc.symm (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hpl : IsPlaceOver (N.plOm.1 P) P := N.plOm.2 P
  obtain ⟨σ, hσ, hne⟩ := (hR P _ hpl).2 hP
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine X.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  refine (hR P' _ (fun y => ?_)).1 ⟨σ', h2, ?_⟩
  · have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs, ← hPP ⟨_, hint⟩ y (hκ _).symm]
    exact hpl ⟨_, hint⟩
  · rw [hA σ σ' h1]
    exact inv_ne_one.2 hne

theorem tw_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ → (ρ.tw i b k Q ψ).Good ∧ (ρ.B i j b).admitted (ρ.tw i b k Q ψ).Q ∧ ∀ x, ∃ u : (X.Ok i k)ˣ, (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) = ρ.eOk i b k u := by
  intro D N X ρ hρ i j b k Q ψ hψ
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D N X ρ hρ i j b Q hsplit hdisj
  let g : (X.Ok i k)ˣ →* Circle := unitPart.comp (Units.map (ρ.eOk i b k).toMonoidHom)
  have hkey : charOf ρ.rc (ρ.eOk i b k) ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : X.zk i k ^ (X.l i ^ k) = 1 := Units.ext (by simpa using (X.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (X.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, hadm, ?_⟩
  · show (⟨half (ρ.ch i) Q, charOf ρ.rc (ρ.eOk i b k) ψ, resOf (charOf ρ.rc (ρ.eOk i b k) ψ)⟩ : Twist D Circle).Good
    rw [hkey]
    refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc Circle (g.comp ψ) (X.l i) (X.lPrime i).out
      (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
    · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        rw [MonoidHom.comp_apply, hx, map_one]) hopen
    · intro x x' hx
      show g (ψ x') = (g (ψ x))⁻¹
      rw [hanti x x' hx, map_inv]
    · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
      exact h3.mono (Finset.subset_union_right.trans h2)
    · intro P hP hl
      exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (X.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (X.l i) from hl))
    · intro v hv hnc B hB σ hσ
      have hvQ : v ∉ Q := by
        intro hvQ
        by_cases hc : v ∈ ρ.ch i
        · exact hv (mem_half.2 ⟨hvQ, hc⟩)
        · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
          have hv'Q : v' ∈ Q := ramExactly_conj X ψ _ hanti hram v hvQ v' hv'
          have hne := ne_of_split (hsplit v hvQ) hv'
          have hv'c : v' ∈ ρ.ch i := by
            by_contra h
            exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
          exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
      have h1 : ψ σ = 1 := by
        by_contra h
        exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
      rw [MonoidHom.comp_apply, h1, map_one]
  · intro x
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
    exact ⟨ψ σ, charOf_eq ρ.rc (ρ.eOk i b k) hopen hσ (pow_ne_zero _ (X.lPrime i).out.ne_zero) (hpow σ)⟩

end GlobalTheory.TwistGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeParameterSquarefree
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.Pass.stepType_proof : StepType := by
  intro D P hDZ h0 h1 h2 h5
  exact GlobalTheory.T.type_local_global D P hDZ h0 (GlobalTheory.T.weil_deligne_above D h0 h1 h2 h5)
end

