import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0710
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0518
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedCompatibleMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef.ChartAbove

theorem specMap_stalkCongr_fromSpecStalk {X : Scheme.{0}} {x y : X} (h : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ X.fromSpecStalk x = X.fromSpecStalk y := by
  subst h
  simp

theorem exists_complete_normal_above (A B R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B]
    [IsIntegrallyClosed B] [CharZero B] [Algebra.EssFiniteType ℤ B] [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : A →+* B) (g : A →+* R) (hA : IsNoetherianRing A) (hf : IsLocalHom f) (hfi : Function.Injective f)
    (hbir : ∀ b : B, ∃ a s : A, f s ≠ 0 ∧ f s * b = f a) (hg : IsLocalHom g) (hR : IsCN R)
    (het : IsEtaleCompletion g) (hfu : ((residue R).comp g).FormallyUnramified) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (φ : R →+* R') (ψ : B →+* R'),
      IsCN R' ∧ IsLocalHom ψ ∧ Function.Injective ψ ∧ IsEtaleCompletion ψ ∧
      ((residue R').comp ψ).FormallyUnramified ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ψ.comp f = φ.comp g := by
  obtain ⟨C, _, _, _, φ0, ψ0, hCn, hφl, hφi, hψl, hψi, hψf, hψm, hψfin, hψfu, hcomm⟩ :=
    GlobalTheory.T.residue_comp_formal_completion A B R f g hA hR.1 inferInstance hf hfi hbir hg het hfu
  obtain ⟨R', _, _, ι, hRn, hRc, hιl, hιi, hιe, hιu⟩ := GlobalTheory.T.exists_complete_unramified_extension B C ψ0 hCn hψl hψf hψm hψfin hψfu
  have hBn : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing ℤ B
  obtain ⟨hd, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed B
  haveI := hιl
  haveI := hψl
  haveI := hφl
  have hloc : IsLocalHom (ι.comp ψ0) := inferInstance
  obtain ⟨hRd, hRi⟩ := GlobalTheory.T.completion_unramified_normal B R' (ι.comp ψ0) hBn hd hic hRn hRc hloc hιe hιu
  have hinj : Function.Injective (ι.comp ψ0) := hιi.comp hψi
  haveI : CharZero R' := charZero_of_injective_ringHom hinj
  refine ⟨R', inferInstance, hRd, inferInstance, ι.comp φ0, ι.comp ψ0, ⟨hRn, hRi, hRc, inferInstance⟩, hloc, hinj,
    hιe, hιu, hιi.comp hφi, inferInstance, ?_⟩
  rw [RingHom.comp_assoc, hcomm, ← RingHom.comp_assoc]

theorem exists_chart_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (z : Z.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ξ (closedPoint R) = π z → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ' : Sp R' ⟶ Z.X) (φ : R →+* R'), IsCN R' ∧ ξ' (closedPoint R') = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom ∧ ((residue R').comp (Scheme.stalkClosedPointTo ξ').hom).FormallyUnramified ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ' ≫ π = spMap φ ≫ ξ ∧ Dense (ξ' ⁻¹' Set.range Z.j) := by
  intro E _ _ _ H D l Xo c X Z π hj hs R _ _ _ ξ z hR het hfu hpt
  haveI := (Z.normal z).1
  haveI := (Z.normal z).2
  haveI := (X.normal (ξ (closedPoint R))).1
  obtain ⟨hcz, hez⟩ := GlobalTheory.T.stalk_charZero_essFiniteType E H D l Xo c Z z
  obtain ⟨-, hexX⟩ := GlobalTheory.T.stalk_charZero_essFiniteType E H D l Xo c X (ξ (closedPoint R))
  have hAn : IsNoetherianRing (X.X.presheaf.stalk (ξ (closedPoint R))) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  obtain ⟨hbi, hbb⟩ := GlobalTheory.T.stalk_map_injective_birational E H D l Xo c X Z π hj hs z
  let e := X.X.presheaf.stalkCongr (Inseparable.of_eq hpt)
  have heb : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  let f : X.X.presheaf.stalk (ξ (closedPoint R)) →+* Z.X.presheaf.stalk z := (π.stalkMap z).hom.comp e.hom.hom
  have hfi : Function.Injective f := hbi.comp heb.1
  have hbir : ∀ b : Z.X.presheaf.stalk z, ∃ a s : X.X.presheaf.stalk (ξ (closedPoint R)), f s ≠ 0 ∧ f s * b = f a := by
    intro b
    obtain ⟨a, s, hs0, hsb⟩ := hbb b
    obtain ⟨a', rfl⟩ := heb.2 a
    obtain ⟨s', rfl⟩ := heb.2 s
    exact ⟨a', s', hs0, hsb⟩
  have hfl : IsLocalHom f := inferInstance
  let g := (Scheme.stalkClosedPointTo ξ).hom
  obtain ⟨R', _, _, _, φ, ψ, hR', hψl, hψi, het', hfu', hφi, hφl, hcomm⟩ :=
    exists_complete_normal_above _ _ R f g hAn hfl hfi hbir inferInstance hR het hfu

  haveI := hψl
  let ψc : Z.X.presheaf.stalk z ⟶ CommRingCat.of R' := CommRingCat.ofHom ψ
  haveI : IsLocalHom ψc.hom := hψl
  let ξ' : Sp R' ⟶ Z.X := (SpecToEquivOfLocalRing Z.X (CommRingCat.of R')).symm ⟨z, ⟨ψc, inferInstance⟩⟩
  have hsym := (SpecToEquivOfLocalRing Z.X (CommRingCat.of R')).apply_symm_apply ⟨z, ⟨ψc, inferInstance⟩⟩
  rw [SpecToEquivOfLocalRing_eq_iff] at hsym
  obtain ⟨h1, h2⟩ := hsym
  have hpt' : ξ' (closedPoint R') = z := h1
  have h2' : (Scheme.stalkClosedPointTo ξ').hom = ψ.comp (Z.X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom.hom := by
    exact congrArg (fun q => q.hom) h2
  refine ⟨R', inferInstance, inferInstance, inferInstance, ξ', φ, hR', hpt', ?_, ?_, hφi, hφl, ?_, ?_⟩
  · rw [h2']
    exact isEtaleCompletion_comp_bij _ (ConcreteCategory.bijective_of_isIso _) ψ het'
  · rw [h2']
    have hsurj : Function.Surjective (Z.X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    have h3 := RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective hsurj) hfu'
    exact h3
  · have hcomm' : Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom φ = e.hom ≫ π.stalkMap z ≫ ψc := by
      ext a
      have := congrArg (fun q : _ →+* R' => q a) hcomm
      exact this.symm
    calc ξ' ≫ π = Spec.map ψc ≫ Z.X.fromSpecStalk z ≫ π := by simp only [ξ', SpecToEquivOfLocalRing_symm_apply, Category.assoc]
      _ = Spec.map ψc ≫ Spec.map (π.stalkMap z) ≫ X.X.fromSpecStalk (π z) := by
          rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
      _ = Spec.map ψc ≫ Spec.map (π.stalkMap z) ≫ Spec.map e.hom ≫ X.X.fromSpecStalk (ξ (closedPoint R)) := by
          rw [specMap_stalkCongr_fromSpecStalk hpt]
      _ = Spec.map (e.hom ≫ π.stalkMap z ≫ ψc) ≫ X.X.fromSpecStalk (ξ (closedPoint R)) := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom φ) ≫ X.X.fromSpecStalk (ξ (closedPoint R)) := by
          rw [hcomm']
      _ = spMap φ ≫ ξ := by
          rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · let η0 : PrimeSpectrum R' := ⟨⊥, Ideal.isPrime_bot⟩
    let η : Sp R' := η0
    have hη : η ∈ ξ' ⁻¹' Set.range Z.j := by
      show ξ' η ∈ Set.range Z.j
      have hxi : ξ' η = Z.X.fromSpecStalk z ((Spec.map ψc) η) := rfl
      rw [hxi]
      apply GlobalTheory.T.generic_stalk_point_in_interior E H D l Xo c Z z
      show Ideal.comap ψ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot ψ).1 hψi
    have hcl0 : closure ({η0} : Set (PrimeSpectrum R')) = Set.univ := by
      rw [PrimeSpectrum.closure_singleton]
      exact PrimeSpectrum.zeroLocus_bot
    have hcl : closure ({η} : Set (Sp R')) = Set.univ := hcl0
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro p
    have hp : p ∈ closure ({η} : Set (Sp R')) := by rw [hcl]; trivial
    exact closure_mono (Set.singleton_subset_iff.2 hη) hp

end GlobalTheory.TorRef.ChartAbove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoordinatesEqRationalMatrixValuesChart
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.ChartCoords

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem co_congr {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f f' g : EigFrame Z φ x}
    (h : ∀ τ i, f'.v τ i = f.v τ i) (τ : E →+* ℂ) : f'.co g τ = f.co g τ :=
  EigFrame.co_eq fun i => by rw [funext (h τ)]; exact f.co_spec g τ i

theorem v_of_isMap_trans {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} {φ₁ : c.F →+* R₁} {x₁ : Sp R₁ ⟶ Z.X} {φ₂ : c.F →+* R₂} {x₂ : Sp R₂ ⟶ Z.X}
    {f : EigFrame Z φ x} {f₁ : EigFrame Z φ₁ x₁} {f₂ f₂' : EigFrame Z φ₂ x₂} {ψ₁ : R →+* R₁} {ψ₂ : R₁ →+* R₂}
    {ψ : R →+* R₂} (h₁ : f.IsMap ψ₁ f₁) (h₂ : f₁.IsMap ψ₂ f₂) (h : f.IsMap ψ f₂') (hψ : ψ₂.comp ψ₁ = ψ)
    (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : f₂.v τ i = f₂'.v τ i := by
  rw [h₂ τ i, h₁ τ i, GlobalTheory.GradedPieces.dual_comp, hψ, h τ i]

end GlobalTheory.LieBase.ChartCoords

open GlobalTheory.ProjVar.Var GlobalTheory.LieBase.ChartCoords

theorem GlobalTheory.LieBase.coords_eq_ratVal_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ A : Mat Dw.mult X.Fn, ∃ M : Mat Dw.mult X.Fn, ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), A ∈ S.S (under z) → ∀ hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1, (∀ τ p q, RegAt (under z) (M τ p q)) ∧ (∃ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g) ∧ ∀ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g → ∀ f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), Φ.IsMap (evHom hz) f → ∀ τ, f.co g τ = (M τ).map (fun r => ratVal r z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ F _ e X j f₀ S A₀ hj _hoi hT V φ Φ hV A
  classical
  have hVa : IsAffineOpen V.1 := V.2
  haveI : Mono (LogKS.chart V) := inferInstanceAs (Mono hVa.fromSpec)
  have hmem : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 →
      under z ∈ j ⁻¹ᵁ V.1 := fun z hz => mem_ptsIn.1 hz
  by_cases hη : genericPoint X.X ∈ j ⁻¹ᵁ V.1
  swap
  · exact ⟨0, fun z _ hz => absurd (gen_mem (hmem z hz)) hη⟩
  have key : ∀ x : X.X, x ∈ j ⁻¹ᵁ V.1 → ∃ ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x,
      spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j := fun x hx =>
    TieBase.exists_affine_factor _ V.2 (by
      show j (X.X.fromSpecStalk x (IsLocalRing.closedPoint _)) ∈ V.1
      rw [Scheme.fromSpecStalk_closedPoint]; exact hx)
  have key' : ∀ (x : X.X) (ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x), spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j →
      spMap ((algebraMap (X.X.presheaf.stalk x) X.X.functionField).comp ψ) ≫ LogKS.chart V = genericPt X ≫ j :=
    fun x ψ h => by rw [TieBase.spMap_trans, Category.assoc, h, TieBase.genericPt_eq X x, Category.assoc]
  obtain ⟨ψη, hψη⟩ := key _ hη
  obtain ⟨ρ, h₀⟩ : ∃ ρ : Γ(gen Z, V.1) →+* X.X.functionField, spMap ρ ≫ LogKS.chart V = genericPt X ≫ j :=
    ⟨_, key' _ ψη hψη⟩
  have hφK : constF e X = ρ.comp φ := EigLoc.spMap_inj (by
    rw [← TieBase.genericPt_str e X j hj, ← h₀, Category.assoc, hV, ← TieBase.spMap_trans])
  obtain ⟨ΦK, hΦK⟩ := Φ.exists_isMap ρ hφK (x' := genericPt X ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← h₀, Category.assoc])
  refine ⟨fun τ => ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹, fun z hA hz => ?_⟩
  have hx := hmem z hz
  obtain ⟨φx, fz, hc⟩ := hT.2 (under z) A hA
  obtain ⟨ψx, hψx⟩ := key _ hx
  have hρx : (algebraMap _ X.X.functionField).comp ψx = ρ :=
    EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 ((key' _ ψx hψx).trans h₀.symm))
  have hφx : φx = ψx.comp φ := RingHom.ext fun a => IsFractionRing.injective (X.X.presheaf.stalk (under z))
    X.X.functionField (by
      have h1 := RingHom.congr_fun hc.2.1 a
      have h2 := RingHom.congr_fun hφK a
      rw [← hρx] at h2
      exact h1.symm.trans h2)
  obtain ⟨Φx, hΦx⟩ := Φ.exists_isMap ψx hφx (x' := stalkPt X (under z) ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← hψx, Category.assoc])
  have hM : ∀ fz' : EigFrame Z φx (stalkPt X (under z) ≫ j ≫ genι Z),
      fz'.Coord (algebraMap (X.X.presheaf.stalk (under z)) X.X.functionField) f₀ (A₀ * A⁻¹) → ∀ τ,
      ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := by
    intro fz' hc' τ
    obtain ⟨k, hk⟩ := fz'.exists_isMap _ hc'.2.1 hc'.1
    obtain ⟨Φk, hΦk⟩ := Φx.exists_isMap _ hc'.2.1 hc'.1
    have h1 : k.co f₀ τ = ((A₀ * A⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk τ)]; exact hc'.2.2 τ i
    have h3 : Φk.co k τ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := hΦk.co τ hk hc'.1
    have h4 : Φk.co f₀ τ = ΦK.co f₀ τ := co_congr (v_of_isMap_trans hΦx hΦk hΦK hρx) τ
    have h5 : f₀.co k τ = (k.co f₀ τ)⁻¹ := (Matrix.inv_eq_right_inv ((k.co_mul f₀ k τ).trans (k.co_self τ))).symm
    rw [← h3, ← Φk.co_mul f₀ k τ, h4, h5, h1]
  have hs : spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) = z.1 :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1
  have hxz : (cxOf e σ hj z).1 ≫ genι Z = spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) ≫ j ≫ genι Z := by
    show (z.1 ≫ j) ≫ genι Z = _
    conv_lhs => rw [← hs]
    simp only [Category.assoc]
  refine ⟨fun τ p q => ?_, ?_, ?_⟩
  · beta_reduce
    rw [hM fz hc τ]
    exact ⟨Φx.co fz τ p q, rfl⟩
  · have hφ : σ = (Scheme.stalkClosedPointTo z.1).hom.comp φx := RingHom.ext fun a => by
      have h3 : φx a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
        ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under z)).commutes _).symm)
      show σ a = evStalk z (φx a)
      rw [h3]
      refine Eq.trans ?_ ((evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
      simp
    obtain ⟨g, hg⟩ := fz.exists_isMap _ hφ hxz
    exact ⟨g, φx, fz, _, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm, hc, hg⟩
  · rintro g ⟨φ', fz', ψ', hψ', hc', hm'⟩ f hf τ
    obtain rfl : ψ' = (Scheme.stalkClosedPointTo z.1).hom :=
      EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under z))).1
        (hψ'.symm.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm))
    obtain rfl : φ' = φx := RingHom.ext fun a => IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc'.2.1 a).symm.trans (RingHom.congr_fun hc.2.1 a))
    have hev : (Scheme.stalkClosedPointTo z.1).hom.comp ψx = evHom hz :=
      EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 (by
        rw [TieBase.spMap_trans, Category.assoc, hψx, LieMet.spMap_evHom hz, ← Category.assoc, hs]
        rfl))
    have hfx : Φx.IsMap (Scheme.stalkClosedPointTo z.1).hom f := fun τ i => by
      rw [hf τ i, hΦx τ i, GlobalTheory.GradedPieces.dual_comp, hev]
    beta_reduce
    rw [hfx.co τ hm' hxz, hM fz' hc' τ]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.map_apply]
    rw [GlobalTheory.TrueGeo.Res.ratVal_eq_valAt z ⟨_, rfl⟩, GlobalTheory.TrueGeo.Res.valAt_algebraMap]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagFramesFlagComponentPullbackBaseFramesStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagFrames_flagComponent_pullback_baseFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z) (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → ∀ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn), Tied e C.Y C.π C.f0 E' A₁ → f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → ∀ z', ∀ A' ∈ E'.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf C.Y).O z').toSubring (A' * (A.map φ)⁻¹) := by
  first | exact @GlobalTheory.LieBase.FlagPull.frames_sub | exact GlobalTheory.LieBase.FlagPull.frames_sub | (intros; apply GlobalTheory.LieBase.FlagPull.frames_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisRepsCuspidalAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem galoisRepsCusp_of_galEx {D : D7} (h : GalEx D) : GlobalTheory.BlockComplement.GaloisRepsCusp D :=
  fun i a ha π hc hr => h (D.nd.l i) (D.naut.iotaQC i) a ha π hc hr

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem galoisRepsCusp_thirdSt : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x,
    GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => GlobalTheory.BlockComplement.GaloisRepsCusp D' := by
  intro hP hL
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ => ?_⟩
  let T' : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { l.a.A.wdT with }
  have cg : CGTrue hL (withLoc L) T' := { l.a.cg with }
  exact galoisRepsCusp_of_galEx (cg.galEx hL hP.what₂.fin hP.what₂.gal)

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricParameterOfReciprocity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.GenRows

set_option maxHeartbeats 4000000 in

theorem goodGeneric_rows : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; ∀ χ ∈ a.x.A3.A.X, chiIdem χ * lvlIdem a.x.F.P0 a.x.F.ψ0 ≠ 0 := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ a
  have hSer : ∀ k : Fin 2, haveI : Fact ((q.w.st q.Z).toD7.host.g k).Prime := ⟨(q.w.st q.Z).toD7.host.g_prime k⟩
      ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod ((q.w.st q.Z).toD7.host.g k)))
        (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod ((q.w.st q.Z).toD7.host.g k)) C),
        ∀ f, (q.w.st q.Z).toD7.ntypes.eSer k f = Formalism.L2.NT.eSerO O (q.w.st q.Z).toD7.R.r f :=
    fun k => ⟨_, q.core.a.all.types.O k, q.core.a.all.types.eSer_def k⟩
  letI := a.x.grp
  letI := a.x.fin
  letI := a.x.alg
  exact (GlobalTheory.T.goodGenericCharacter_of_weakCharacterisation a.x.R a.x.F a.x.pins.char 1 a.intersectionNumber_baseChange.ok hSer).1

end GlobalTheory.Mem.R3.GenRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCopy
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.CopyRead

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

set_option maxHeartbeats 2000000 in

theorem rrT_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) (y₀ : Hd z₀.R.toRealDat) (bb : Bool) (E : Hs)
    (jE : E.T →ₗ[ℂ] (y₀.C z₀.F.lv2).Amb 0) (n : ℕ) (c : Module.Basis (Fin n) ℂ E.T)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (h : RrT z₀.F y₀ bb jE n c Xo) :
    ∀ (y : Hd z.R.toRealDat) (jE' : E.T →ₗ[ℂ] (y.C z.F.lv2).Amb 0), HEq jE' jE → RrT z.F y bb jE' n c Xo := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  intro y jE' hj
  exact (by with_unfolding_all exact (((@rr_eta_tr B C a b _ _ _ _ _ _ _ _ _ z₀.alg _ z₀.R z₀.F).2 y₀ ((y)) bb E jE ((jE')) n c ((Xo)) ((hj)) h) : _))

end Copy

set_option maxHeartbeats 1000000 in

theorem coords {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : RationalReadingWithoutCongruence R F X0 Y) (y : Hd R.toRealDat)
    (heq_eigen_embedding_zero : D.what₂.EE0 →ₗ[ℂ] (y.C F.lv2).Amb 0) (hinj : Function.Injective heq_eigen_embedding_zero) (n : ℕ) (c : Module.Basis (Fin n) ℂ D.what₂.EE0)
    (Xo : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ) (h : RrT F y false (E := ⟨D.what₂.EE0⟩) heq_eigen_embedding_zero n c Xo)
    (hz : ∀ v, HEq (Y.Iz.jE v).1 (heq_eigen_embedding_zero v)) :
    ∃ ε : X0.s.RR.V ≃ₗ[D.what₂.LL] (Fin n → D.what₂.LL), (∀ x, X0.s.jEE x = ∑ i, D.what₂.embLL (ε x i) • c i) ∧
      ∀ v, v ≠ A3.A.v0 → ∀ x x', Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin n)) Xo v (ε x) (ε x') := by
  obtain ⟨rfl, a0, b0⟩ := h
  refine ⟨Z.eRR0.symm, fun x => hinj ?_, fun v hv x x' => ?_⟩
  · have h := Z.jEE0 (Z.eRR0.symm x)
    rw [Z.eRR0.apply_symm_apply] at h
    exact (eq_of_heq (hz _)).symm.trans (h.trans (a0 (Z.eRR0.symm x)).symm)
  · have h := Z.met0 v hv (Z.eRR0.symm x) (Z.eRR0.symm x')
    rw [Z.eRR0.apply_symm_apply, Z.eRR0.apply_symm_apply] at h
    exact h.trans (GoodSideLattices.majAt_cast rfl _ Xo v (b0 v).1 _ _).symm

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}

set_option maxHeartbeats 1000000 in

theorem RRset_two {o o' : q.Over} (s : Side0 o) (s' : Side0 o') (μ : (w.D o.Z).what₂.Tup) :
    s.p0.s.RRset μ = (s'.p0.s.RRset μ) := by
  have h : ∀ k, s.p0.s.downTo μ k = (by with_unfolding_all exact ((s'.p0.s.downTo ((μ)) k) : _)) := by
    intro k
    induction k with
    | zero => exact (by with_unfolding_all exact ((Eq.refl (s.p0.s.downTo μ 0)) :))
    | succ k ih => exact (by with_unfolding_all exact ((congrArg (fun φ : type_of% (s.p0.s.downTo μ k) => φ.comp (s.p0.s.io μ k)) ih) :))
  have hi := congrArg (fun φ : type_of% (s.p0.s.downTo μ (w.D o.Z).R.m) =>
    (s.p0.s.multZero μ).toLinearEquiv.toLinearMap ∘ₗ φ ∘ₗ (s.p0.s.multTop μ).symm.toLinearEquiv.toLinearMap) (h (w.D o.Z).R.m)
  exact (by with_unfolding_all exact ((congrArg (fun φ : s.p0.s.Amb μ →ₗ[ℂ] (w.D o.Z).what₂.EE0 =>
    φ '' ((fun x => (s.p0.s.V0 μ ⊓ (s.p0.s.V0 μ ⊓ LinearMap.ker φ)ᗮ).starProjection x) ''
      ((s.p0.s.Mtilde μ).carrier ∩ (s.p0.s.V0 μ : Set (s.p0.s.Amb μ))))) hi) :))

set_option maxHeartbeats 1000000 in

theorem rrT_moved {o : q.Over} (m : Moved o) (hc : m.Copy) (hco : m.Coh) (b : Bool) {n c Xo}
    (h : RrT z₀.F q.y b (q.t.ch b).jE n c Xo) : RrT m.z.F m.y b (m.t.ch b).jE n c Xo :=
  rrT_copy (B := B) (C := w.C) (a := Z₀) o.Z z₀ m.z m.Xg m.tr ((by with_unfolding_all exact (hc.core :))) ((by with_unfolding_all exact (hc.R :))) q.y b _ _ n c Xo h m.y _ (hco.jE b)

theorem lat_tr {K : Type} [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {n : ℕ} (c : Module.Basis (Fin n) ℂ V) (Xo : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    {ι : Type} (P : ι → HeightOneSpectrum (𝓞 K)) {S S' : ι → Set V} (hS : S = S') {RR RR' : HLat K} (hR : RR' = RR)
    {j : RR.V →ₛₗ[e] V} {j' : RR'.V →ₛₗ[e] V} (hj : HEq j' j)
    (h : ∃ ε : RR.V ≃ₗ[K] (Fin n → K), (∀ x, j x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR.b RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR.V, x ∈ RR.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j z ∈ S u}) :
    ∃ ε : RR'.V ≃ₗ[K] (Fin n → K), (∀ x, j' x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR'.b RR'.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR'.V, x ∈ RR'.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j' z ∈ S' u} := by
  subst hS hR
  cases hj
  exact h

set_option maxHeartbeats 2000000 in

theorem good_copy {K : Ctx} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)) (m : Moved (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) (hc : m.Copy)
    (hco : m.Coh) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) (hR : s.RR = x.s.RR) (hj : HEq s.jEE x.s.jEE) : GoodSideLattices.Good m s := by
  obtain ⟨n, c, Xo, h⟩ := rrT_exists (w.st P.Z₀).toD7 (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T P.Wt))
    (famR (w.st P.Z₀) w.I P.hX (usedOf w.I T P.Wt) P.z.Xg P.z.tr) P.z.core.Q.c.F P.z.R P.z.F P.z.cG P.z.pins P.intersectionNumber_baseChange P.q.y false
    (P.q.p.ch false).EE (P.q.t.ch false).jE (P.q.t.ch false).jE_inj (P.q.t.ch false).jE_range
  have h0 := rrT_moved x.m x.copy x.coh false h
  have h1 := rrT_moved m hc hco false h
  have h2 := coords x.r.Z x.m.y ((by with_unfolding_all exact ((x.m.t.ch false).jE :))) ((by with_unfolding_all exact ((x.m.t.ch false).jE_inj :))) n ((by with_unfolding_all exact (c :))) ((by with_unfolding_all exact (Xo :))) ((by with_unfolding_all exact (h0 :))) ((by with_unfolding_all exact (x.pin.heq_eigen_embedding_zero :)))
  obtain ⟨ε, h2, h3⟩ := h2
  have h4 : (fun u : B.places.Pl => ((by with_unfolding_all exact ((x.s.p0.s.RRset ((w.D x.o.Z).what₂.muAt u)) :)) : Set (P.q.p.ch false).EE.T)) =
      fun u => (by with_unfolding_all exact ((s.p0.s.RRset ((w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).what₂.muAt u)) :)) :=
    funext fun u => (by with_unfolding_all exact ((RRset_two x.s s ((w.D x.o.Z).what₂.muAt u)) :))
  have h5 := lat_tr (K := B.LL) B.embLL c Xo ((by with_unfolding_all exact ((fun u : B.places.Pl => (w.D x.o.Z).plEq u) :))) h4 hR hj
    ⟨(by with_unfolding_all exact (ε :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (x.r.Z.rr0 :))⟩
  obtain ⟨ε', k1, k2, k3⟩ := h5
  exact ⟨n, c, Xo, ε', h1, k1, k2, (by with_unfolding_all exact (k3 :))⟩

end GlobalTheory.Mem.R3.Rw.CopyRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistsThetaLatticesPreservedDivisionChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

set_option maxHeartbeats 4000000 in

theorem goodO_setDiv : ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), GoodO D nch xd → GoodO (setDiv D N h) (nchTr N h nch) (xdTr N h xd) := by
  intro D nch xd N h hg
  obtain ⟨⟨⟨E, N0, S⟩, hE, hA, hC⟩, hsep⟩ := hg
  subst hE
  exact ⟨⟨⟨{ (twEOf xd) with }, N0, S⟩, rfl, hA, hC⟩, hsep⟩

end GlobalTheory.Mem.Top.Bl.WitTr

end
end

