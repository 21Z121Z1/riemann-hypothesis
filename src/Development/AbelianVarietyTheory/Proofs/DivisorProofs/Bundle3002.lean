import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusSpreadOverTraitSpecialisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem isLocalHom_of_map_maximalIdeal {W κ : Type} [CommRing W] [IsLocalRing W] [Field κ] (c : W →+* κ)
    (hc : ∀ x ∈ maximalIdeal W, c x = 0) : IsLocalHom c :=
  ⟨fun a ha => by
    by_contra h
    have hm : a ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal a).2 h
    rw [hc a hm] at ha
    exact not_isUnit_zero ha⟩

theorem exists_common_residue {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] [CommRing V]
    [IsLocalRing V] (ψ : R →+* W) [IsLocalHom ψ] (g : R →+* V) [IsLocalHom g] :
    ∃ (κ : Type) (_ : Field κ) (c : W →+* κ) (b : V →+* κ), (∀ x ∈ maximalIdeal W, c x = 0) ∧
      (∀ x ∈ maximalIdeal V, b x = 0) ∧ c.comp ψ = b.comp g := by
  letI : Algebra (ResidueField R) (ResidueField W) := (ResidueField.map ψ).toAlgebra
  letI : Algebra (ResidueField R) (ResidueField V) := (ResidueField.map g).toAlgebra
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (ResidueField W ⊗[ResidueField R] ResidueField V)
  letI := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  refine ⟨_ ⧸ M, inferInstance, q.comp ((Algebra.TensorProduct.includeLeftRingHom).comp (residue W)),
    q.comp ((Algebra.TensorProduct.includeRight.toRingHom).comp (residue V)), fun x hx => ?_, fun x hx => ?_,
    RingHom.ext fun r => ?_⟩
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp only [RingHom.comp_apply]
    congr 1
    rw [← ResidueField.map_residue ψ r, ← ResidueField.map_residue g r]
    change Algebra.TensorProduct.includeLeftRingHom (algebraMap (ResidueField R) (ResidueField W) (residue R r)) =
      Algebra.TensorProduct.includeRight (algebraMap (ResidueField R) (ResidueField V) (residue R r))
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem spread₂_of_trait {B : Scheme.{0}} (H : Over B) [GrpObj H]
    {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {D₁ : DegData V₁ (maximalIdeal V₁)}
    {A₁ : PolAV (Sp (FractionRing V₁))} {G₁ : Over (Sp V₁)} [GrpObj G₁] [IsCommMonObj G₁]
    {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {D₂ : DegData V₂ (maximalIdeal V₂)}
    {A₂ : PolAV (Sp (FractionRing V₂))} {G₂ : Over (Sp V₂)} [GrpObj G₂] [IsCommMonObj G₂]
    (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left)
    (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left)
    {R : Type} [CommRing R] [IsLocalRing R] (ιB : Sp R ⟶ B) (HR : Over (Sp R)) [GrpObj HR] [IsCommMonObj HR]
    (φR : HR.left ⟶ H.left) (hR : IsGrpPullback HR H ιB φR)
    (g₁ : R →+* V₁) (β₁' : G₁.left ⟶ HR.left) (eβ₁ : β₁' ≫ φR = β₁) (hξ₁ : spMap g₁ ≫ ιB = ξ₁)
    (g₂ : R →+* V₂) (hg₂ : IsLocalHom g₂) (β₂' : G₂.left ⟶ HR.left) (hβ₂ : IsGrpPullback G₂ HR (spMap g₂) β₂')
    (eβ₂ : β₂' ≫ φR = β₂) (hξ₂ : spMap g₂ ≫ ιB = ξ₂)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ψ₀ : R →+* W) (hψ : IsLocalHom ψ₀)
    (Ω : Type) [Field Ω] (α : W →+* Ω) (hα : Function.Injective α) (b₁ : V₁ →+* Ω)
    (hb₁ : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0) (eα : α.comp ψ₀ = b₁.comp g₁)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ ((Over.pullback (spMap ψ₀)).obj HR).left)
    (hn : IsGrpPullback GΩ ((Over.pullback (spMap ψ₀)).obj HR) (spMap α) n)
    (n₁ : GΩ.left ⟶ G₁.left) (hn₁ : IsGrpPullback GΩ G₁ (spMap b₁) n₁)
    (hnn : n ≫ pullback.fst HR.hom (spMap ψ₀) = n₁ ≫ β₁')
    (j : splitTorus (Sp W) D₁.toPre.X ⟶ (Over.pullback (spMap ψ₀)).obj HR) (hj : IsMonHom j)
    (ej : GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb₁ hn₁) :
    ∃ ρ, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  haveI := hψ
  haveI := hg₂
  haveI := hj
  obtain ⟨κ, _, c, b₂, hc0, hb0, ec⟩ := exists_common_residue ψ₀ g₂
  have hcl : IsLocalHom c := isLocalHom_of_map_maximalIdeal c hc0
  have hb₂ := GlobalTheory.TorusPart.map_pow_one_eq_zero hb0
  have hW := isGrpPullback_pullback HR (spMap ψ₀)
  have hm := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap c)
  obtain ⟨m₂, hm₂, em₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₂ (spMap b₂)
    ((hm.comp hW).congr ((GlobalTheory.SpreadTrait.spMap_comp' ψ₀ c).trans
      ((congrArg spMap ec).trans (GlobalTheory.SpreadTrait.spMap_comp' g₂ b₂).symm)) rfl)
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₂.gt 0) hb₂ hm₂).2 _
    (GlobalTheory.TorusPart.pullTorus hm j) inferInstance
  refine ⟨ρ, W, inferInstance, inferInstance, inferInstance, spMap ψ₀ ≫ ιB, (Over.pullback (spMap ψ₀)).obj HR,
    inferInstance, inferInstance, pullback.fst HR.hom (spMap ψ₀) ≫ φR, j, Ω, inferInstance, α, b₁, hb₁, GΩ,
    inferInstance, n, hn, n₁, hn₁, κ, inferInstance, c, b₂, hb₂, _, inferInstance, _, hm, m₂, hm₂, hW.comp hR, hj, hα,
    hcl, ?_, ?_, ?_, ?_, ej, hρ⟩
  · rw [← hξ₁, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', eα]
  · rw [← hξ₂, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', ec]
  · rw [← Category.assoc, hnn, Category.assoc, eβ₁]
  · rw [← eβ₂, ← Category.assoc m₂, em₂, Category.assoc]

theorem exists_spread₂ : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → IsIntegral B → IsLocallyNoetherian B → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → ∃ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ hBi hBn hsp
  haveI := hBi
  haveI := hBn
  let R : Type := B.presheaf.stalk (ξ₂ (closedPoint V₂))
  let ιB : Sp R ⟶ B := B.fromSpecStalk (ξ₂ (closedPoint V₂))
  let HR := (Over.pullback ιB).obj H
  have hHR : IsSemiAbelian HR := IsSemiAbelian.pullback ιB H hH
  haveI : IsCommMonObj HR := hHR.comm
  have hR := isGrpPullback_pullback H ιB
  let g₁ : R →+* V₁ := (B.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ₁).hom
  let g₂ : R →+* V₂ := (Scheme.stalkClosedPointTo ξ₂).hom
  have hg₂ : IsLocalHom g₂ := Scheme.isLocalHom_stalkClosedPointTo' ξ₂
  have hξ₁ : spMap g₁ ≫ ιB = ξ₁ := by
    have e : spMap g₁ = Spec.map (Scheme.stalkClosedPointTo ξ₁) ≫ Spec.map (B.presheaf.stalkSpecializes hsp) := by
      rw [← Spec.map_comp]; rfl
    rw [e, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hξ₂ : spMap g₂ ≫ ιB = ξ₂ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₂
  obtain ⟨β₁', hβ₁', eβ₁⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₁) (hβ₁.congr hξ₁.symm rfl)
  obtain ⟨β₂', hβ₂', eβ₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₂) (hβ₂.congr hξ₂.symm rfl)
  by_cases hl : IsLocalHom g₁
  · haveI := hl
    let κ₁ := ResidueField V₁
    have hC : IsLocalHom (PowerSeries.C (R := κ₁)) :=
      ⟨fun a ha => by simpa using ha.map (PowerSeries.constantCoeff (R := κ₁))⟩
    let c₁ : V₁ →+* PowerSeries κ₁ := (PowerSeries.C (R := κ₁)).comp (residue V₁)
    have hcl : IsLocalHom c₁ := RingHom.isLocalHom_comp _ _
    let ψ₀ : R →+* PowerSeries κ₁ := c₁.comp g₁
    have hψ : IsLocalHom ψ₀ := RingHom.isLocalHom_comp _ _
    let α := algebraMap (PowerSeries κ₁) (FractionRing (PowerSeries κ₁))
    have hα : Function.Injective α := IsFractionRing.injective _ _
    let b₁ : V₁ →+* FractionRing (PowerSeries κ₁) := α.comp c₁
    have hc0 : ∀ x ∈ maximalIdeal V₁, c₁ x = 0 := fun x hx => by
      simp [c₁, (IsLocalRing.residue_eq_zero_iff x).2 hx]
    have hc : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), c₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hc0
    have hb : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := fun x hx => by
      simp [b₁, hc x hx]
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    obtain ⟨mc, hmc, hmcβ⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₁' (spMap c₁)
      (hm₁.congr (GlobalTheory.SpreadTrait.spMap_comp' g₁ c₁).symm rfl)
    have hn := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap α)
    have hn' : IsGrpPullback _ G₁ (spMap b₁) _ := (hn.comp hmc).congr (GlobalTheory.SpreadTrait.spMap_comp' c₁ α) rfl
    have hnn : pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ pullback.fst HR.hom (spMap ψ₀) =
        (pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ mc) ≫ β₁' := by
      rw [Category.assoc, hmcβ]
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      (PowerSeries κ₁) ψ₀ hψ _ α hα b₁ hb rfl _ _ hn _ hn' hnn
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hc hmc) inferInstance
      (GlobalTheory.TorusPart.pullTorus_gtTorus (U₁.gt 0) hc hb hmc hn' hn rfl rfl)
  · obtain ⟨W, _, _, _, ψ₀, Ω, _, αK, b₁, hψ, hb, eα, hT⟩ := GlobalTheory.T.exists_trait_nonlocal_torusExtension' R HR hHR V₁ g₁ hl
    haveI := hψ
    let alg := algebraMap W (FractionRing W)
    have hα : Function.Injective (αK.comp alg) :=
      αK.injective.comp (IsFractionRing.injective W (FractionRing W))
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    have hG₁' : IsSemiAbelian ((Over.pullback (spMap ψ₀)).obj HR) := IsSemiAbelian.pullback _ HR hHR
    obtain ⟨φ₁, hφ₁, -⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap alg)
      ((isGrpPullback_pullback HR (spMap (alg.comp ψ₀))).congr (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ alg).symm rfl)
    have hn' := isGrpPullback_pullback G₁ (spMap b₁)
    obtain ⟨n, hn, hnm⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap (αK.comp alg))
      ((hn'.comp hβ₁').congr ((GlobalTheory.SpreadTrait.spMap_comp' g₁ b₁).trans ((congrArg spMap eα.symm).trans
        (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ (αK.comp alg)).symm)) rfl)
    have hb' : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hb
    obtain ⟨j, hj, ej⟩ := GlobalTheory.T.extend_splitTorus_hom_over_dvr W ((Over.pullback (spMap ψ₀)).obj HR) hG₁' _ φ₁ hφ₁ hT Ω αK _ n hn _
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb' hn') inferInstance
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      W ψ₀ hψ Ω (αK.comp alg) hα b₁ hb' eα _ n hn _ hn' hnm j hj ej

end GlobalTheory.Poinc.Sep.Spz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitSpreadingTorusPartOfSpecialisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_spreading_torusPart_of_specialisation : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (G : Over Y) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ w w' : Y, w ⤳ w' → w ≠ w' → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ξ : Sp V ⟶ Y) (G₁ : Over (Sp V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left) (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Free ℤ X₁) (_ : Module.Finite ℤ X₁) (j : splitTorus (Sp V) X₁ ⟶ G₁) (GK : Over (Sp (FractionRing V))) (_ : GrpObj GK) (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), ξ (closedPoint V) = w' ∧ (spMap (algebraMap V (FractionRing V)) ≫ ξ) (closedPoint (FractionRing V)) = w ∧ IsGrpPullback G₁ G ξ φ₁ ∧ IsMonHom j ∧ IsTorPart (pullTorus hψ j) := by
  first | exact @GlobalTheory.Poinc.FibLat.exists_trait_torusPart | exact GlobalTheory.Poinc.FibLat.exists_trait_torusPart | (intros; apply GlobalTheory.Poinc.FibLat.exists_trait_torusPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficientsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translated_expansion_coefficients : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A), IsMonHom β → ∀ (g : GtPt D (𝟙_ (Over (Sp R)))) (xe : D₂.X ≃+ D.X), (∀ χ : D₂.X, D₂.c χ ≫ β = D.c (xe χ)) → ∀ w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen → ∀ f : ∀ α : D.X, D.SecB 1 α, ∃ f₂ : ∀ α : D₂.X, D₂.SecB 1 α, ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i)) (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  first | exact @GlobalTheory.MumCmp.TrCoef.exists_translated_coef | exact GlobalTheory.MumCmp.TrCoef.exists_translated_coef | (intros; apply GlobalTheory.MumCmp.TrCoef.exists_translated_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupGaloisAutomorphismMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gal_map_maximalIdeal_le {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R'] {ρ : R →+* R'} (σ : Gal ρ) :
    (maximalIdeal R').map (Gal.hom σ) ≤ maximalIdeal R' := by
  refine Ideal.map_le_of_le_comap fun x hx => ?_
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply (mem_nonunits_iff.1 ((mem_maximalIdeal x).1 hx))
  have := hu.map (σ.1.symm : R' ≃+* R')
  simpa [Gal.hom] using this

theorem exists_galMap : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ), ∃ a, GalMap hD U' σ a := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ hG' U' σ
  obtain ⟨hR', hinj, -⟩ := hρ
  have hσi : Function.Injective (Gal.hom σ) := σ.1.injective
  obtain ⟨h, hPO⟩ := GlobalTheory.T.exists_selfPullback_degenerationData_ringAutOver R R' ρ hinj D.toPre D'.toPre hD σ
  obtain ⟨A'', U'', hU''⟩ := GlobalTheory.T.exists_uniformisation_pullback_to_pullDeg R' R' _ _ hR' hR' (Gal.hom σ) hσi (gal_map_maximalIdeal_le σ) D' D' h A' G'
    hG' U'
  obtain ⟨hid, hxe, hem⟩ := GlobalTheory.T.exists_pullDeg_identity_self_admissible R' _ hR' D'
  have hsa : IsSemiAbelian ((Over.pullback (specOf (Gal.hom σ))).obj G') := IsSemiAbelian.pullback _ G' hG'
  obtain ⟨-, bc1, -, -, mbc1, -, hU1, -⟩ :=
    GlobalTheory.T.uniformisation_determined_by_degenerationData_normal R' hR' D' A'' ((Over.pullback (specOf (Gal.hom σ))).obj G') hsa U'' D' A' G' hG' U' hid
  obtain ⟨h', bc, hU, hxe', hem', -, hmon⟩ := GlobalTheory.T.isPullbackUniformisation_comp_id_pullback R' R' _ _ (Gal.hom σ) D' D' D' h hid A' A'' A' G'
    ((Over.pullback (specOf (Gal.hom σ))).obj G') G' (Iso.refl _) bc1 U' U'' U' hU'' hU1
  haveI : IsMonHom bc.hom := hmon (by show IsMonHom (𝟙 _); infer_instance) mbc1
  refine ⟨bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)), ?_, h', bc, rfl, hU, ?_⟩
  · exact ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G' (spMap (Gal.hom σ)))).congr (Category.id_comp _) rfl
  · refine ⟨fun x => by rw [hxe', hxe]; exact hPO.1 x, fun b c hb hc => ?_⟩
    rw [hc, hem', reassoc_of% hem]
    exact hPO.2 b _ hb rfl

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsModelVal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.ModelValGlue

open GlobalTheory.RealMult.RuleDescend (detCorr_comp isPullBy_comp)

theorem exists_spMap_fromSpec {M : Scheme.{0}} {W : M.Opens} (hW : IsAffineOpen W) {T : Type} [CommRing T]
    (f : Sp T ⟶ M) (hf : Set.range f ⊆ (W : Set M)) : ∃ ψ : Γ(M, W) →+* T, spMap ψ ≫ hW.fromSpec = f := by
  have hf' : Set.range f ⊆ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec f hf')).hom, ?_⟩
  change Spec.map (Spec.preimage (IsOpenImmersion.lift hW.fromSpec f hf')) ≫ _ = _
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_span_eq_top {R : Type} [CommRing R] {M : Scheme.{0}} (b : Sp R ⟶ M) (P : M.Opens → Prop)
    (hP : ∀ x : M, ∃ W, P W ∧ x ∈ W) : ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, ∃ W, P W ∧ Set.range (spMap (algebraMap R (Localization.Away g)) ≫ b) ⊆ (W : Set M) := by
  refine ⟨{g | ∃ W, P W ∧ Set.range (spMap (algebraMap R (Localization.Away g)) ≫ b) ⊆ (W : Set M)}, ?_,
    fun g hg ↦ hg⟩
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let p : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  obtain ⟨W, hW, hx⟩ := hP (b p)
  let O : Set (PrimeSpectrum R) := (b ⁻¹ᵁ W).carrier
  have ho : IsOpen O := (b ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ O from hx) ho
  refine hpg (hle (Ideal.subset_span ⟨W, hW, ?_⟩))
  rintro _ ⟨q, rfl⟩
  have hq : PrimeSpectrum.comap (algebraMap R (Localization.Away g)) q ∈
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact ⟨q, rfl⟩
  exact hsub hq

theorem existsUnique_glue {R : Type} [CommRing R] {s : Set R} (hs : Ideal.span s = ⊤)
    (v : ∀ g : s, Localization.Away (g : R))
    (hv : ∀ (g h : s) (T : Type) [CommRing T] (f₁ : Localization.Away (g : R) →+* T)
      (f₂ : Localization.Away (h : R) →+* T), f₁.comp (algebraMap R _) = f₂.comp (algebraMap R _) →
      f₁ (v g) = f₂ (v h)) :
    ∃! x : R, ∀ g : s, algebraMap R (Localization.Away (g : R)) x = v g := by
  refine Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs v fun g h ↦ ?_
  refine hv g h (Localization.Away (g.1 * h.1)) (IsLocalization.Away.awayToAwayRight g.1 h.1)
    (IsLocalization.Away.awayToAwayLeft h.1 g.1) (RingHom.ext fun r ↦ ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq,
    IsLocalization.Away.awayToAwayLeft_eq]

theorem eq_of_loc {R : Type} [CommRing R] {s : Set R} (hs : Ideal.span s = ⊤) {x y : R}
    (h : ∀ g : s, algebraMap R (Localization.Away (g : R)) x = algebraMap R _ y) : x = y :=
  (existsUnique_glue hs (fun _ ↦ algebraMap R _ y) fun _ _ _ _ _ _ e ↦ RingHom.congr_fun e y).unique h fun _ ↦ rfl

theorem tensorEval_comp {R₀ A R R' : Type} [CommRing R₀] [CommRing A] [CommRing R] [Algebra R₀ R] [CommRing R']
    [Algebra R₀ R'] (ψ : A →+* R) (τ : R →ₐ[R₀] R') (h : R₀ ⊗[ℤ] A) :
    tensorEval ((τ : R →+* R').comp ψ) h = τ (tensorEval ψ h) := by
  induction h with
  | zero => simp
  | tmul r a => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem existsUnique_smul {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)} (δ δ' : X.DetGen) :
    ∃! u : R, δ'.1 = u • δ.1 := by
  haveI := X.invertible_detOmega
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : δ'.1 ∈ Submodule.span R {δ.1})
  refine ⟨a, ha.symm, fun c hc ↦ eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : m ∈ Submodule.span R {δ.1})
  rw [smul_comm, ← hc, smul_comm a, ha]

theorem presVal_exists {R₀ : Type} [CommRing R₀] (k : ℕ) {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    (δY : Y.DetGen) (h : R₀ ⊗[ℤ] A) {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)}
    (δ : X.DetGen) {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} (hX : X.IsPullBy Y (spMap ψ) χ) :
    ∃ v, IsPresVal k δY h δ ψ χ v := by
  obtain ⟨δ'', -, hu''⟩ := hX.existsUnique_detGen ψ δY
  obtain ⟨u, -, hu'⟩ := existsUnique_smul δ δ''
  refine ⟨u ^ k * tensorEval ψ h, fun δ₃ u₃ h₃ e₃ ↦ ?_⟩
  obtain rfl := hu'' δ₃ h₃
  obtain rfl := hu' u₃ e₃
  rfl

theorem presVal_unique {R₀ : Type} [CommRing R₀] (k : ℕ) {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    (δY : Y.DetGen) (h : R₀ ⊗[ℤ] A) {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)}
    (δ : X.DetGen) {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} (hX : X.IsPullBy Y (spMap ψ) χ) {v₁ v₂ : R}
    (h₁ : IsPresVal k δY h δ ψ χ v₁) (h₂ : IsPresVal k δY h δ ψ χ v₂) : v₁ = v₂ := by
  obtain ⟨δ'', h'', -⟩ := hX.existsUnique_detGen ψ δY
  obtain ⟨u, hu, -⟩ := existsUnique_smul δ δ''
  rw [h₁ δ'' u h'' hu, h₂ δ'' u h'' hu]

theorem presVal_pull {R₀ : Type} [CommRing R₀] {k : ℕ} {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    {δY : Y.DetGen} {h : R₀ ⊗[ℤ] A} {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)}
    {δ : X.DetGen} {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} {v : R} (hX : X.IsPullBy Y (spMap ψ) χ)
    (hv : IsPresVal k δY h δ ψ χ v) {R' : Type} [CommRing R'] [Algebra R₀ R'] (τ : R →ₐ[R₀] R')
    {X' : Obj F 𝔠 (Sp R')} {θ : X'.A.left ⟶ X.A.left} {δ' : X'.DetGen}
    (hX' : X'.IsPullBy X (spMap (τ : R →+* R')) θ) (hδ' : Obj.DetCorr (τ : R →+* R') θ δ.1 δ'.1) :
    IsPresVal k δY h δ' ((τ : R →+* R').comp ψ) (θ ≫ χ) (τ v) := by
  intro ε' u' hε' hu'
  obtain ⟨ε, hε, -⟩ := hX.existsUnique_detGen ψ δY
  obtain ⟨u, hu, -⟩ := existsUnique_smul δ ε
  have hun : IsUnit (τ u) := (RuleDescend.isUnit_of_eq_smul δ ε u hu).map τ
  let ε'' : X'.DetGen := ⟨τ u • δ'.1, (Submodule.span_singleton_smul_eq hun _).trans δ'.2⟩
  have d : Obj.DetCorr (τ : R →+* R') θ ε.1 ε''.1 := fun w w' hw ↦ by
    change τ u • δ'.1 w' = _
    rw [hδ' w w' hw, hu]
    simp
  obtain rfl : ε' = ε'' :=
    ((isPullBy_comp hX hX').existsUnique_detGen _ δY).unique hε' (detCorr_comp hX hX' hε d)
  obtain rfl : u' = τ u := (existsUnique_smul δ' ε'').unique hu' rfl
  rw [hv ε u hε hu, map_mul, map_pow, tensorEval_comp]

theorem detCorr_cancel {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
    {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {X'' : Obj F 𝔠 (Sp R'')}
    {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (hφ : X'.IsPullBy X (spMap σ) φ) (hψ : X''.IsPullBy X' (spMap τ) ψ)
    {δ : X.DetGen} {δ' : X'.DetGen} {δ'' : X''.DetGen} (h' : Obj.DetCorr σ φ δ.1 δ'.1)
    (h'' : Obj.DetCorr (τ.comp σ) (ψ ≫ φ) δ.1 δ''.1) : Obj.DetCorr τ ψ δ'.1 δ''.1 := by
  obtain ⟨δ₃, h₃, -⟩ := hψ.existsUnique_detGen τ δ'
  obtain rfl : δ'' = δ₃ :=
    ((isPullBy_comp hφ hψ).existsUnique_detGen _ δ).unique h'' (detCorr_comp hφ hψ h' h₃)
  exact h₃

theorem existsUnique_isModelVal : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (N : ℕ) (M : Scheme.{0})
  (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N) (V : M.Opens), IsDPModel N s U α V →
  ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k),
  (∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φY : Y.A.left ⟶ U.A.left),
    Y.IsPullBy U hW.fromSpec φY → ∀ δY : Y.DetGen, ∃ h : R₀ ⊗[ℤ] Γ(M, W), IsChartFun r₀ Y δY h) →
  (∀ (W₁ : M.Opens) (hW₁ : IsAffineOpen W₁) (Y₁ : Obj F 𝔠 (Sp Γ(M, W₁))) (φ₁ : Y₁.A.left ⟶ U.A.left),
    Y₁.IsPullBy U hW₁.fromSpec φ₁ → ∀ (δ₁ : Y₁.DetGen) (h₁ : R₀ ⊗[ℤ] Γ(M, W₁)), IsChartFun r₀ Y₁ δ₁ h₁ →
  ∀ (W₂ : M.Opens) (hW₂ : IsAffineOpen W₂) (Y₂ : Obj F 𝔠 (Sp Γ(M, W₂))) (φ₂ : Y₂.A.left ⟶ U.A.left),
    Y₂.IsPullBy U hW₂.fromSpec φ₂ → ∀ (δ₂ : Y₂.DetGen) (h₂ : R₀ ⊗[ℤ] Γ(M, W₂)), IsChartFun r₀ Y₂ δ₂ h₂ →
  ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (ψ₁ : Γ(M, W₁) →+* R) (χ₁ : X.A.left ⟶ Y₁.A.left) (ψ₂ : Γ(M, W₂) →+* R) (χ₂ : X.A.left ⟶ Y₂.A.left),
    X.IsPullBy Y₁ (spMap ψ₁) χ₁ → X.IsPullBy Y₂ (spMap ψ₂) χ₂ →
    ∀ v₁ v₂ : R, IsPresVal k δ₁ h₁ δ ψ₁ χ₁ v₁ → IsPresVal k δ₂ h₂ δ ψ₂ χ₂ v₂ → v₁ = v₂) →
  ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), levObj 𝔠 N R X → ∀ δ : X.DetGen,
    ∃! v : R, IsModelVal r₀ U X δ v := by
  intro F _ _ 𝔠 N M s U α V hDP R₀ _ k r₀ H1 H2 R _ _ X hlev δ
  have hN : IsUnit (N : R) := hlev.1
  obtain ⟨β⟩ := hlev.2
  have hNu : IsUnit (algebraMap ℤ R (N : ℤ)) := by simpa using hN
  obtain ⟨b, -, φb, hb, -⟩ :=
    (hDP.1 (Sp R) (spMap (IsLocalization.Away.lift (S := Localization.Away (N : ℤ)) (N : ℤ) hNu)) X β).exists
  obtain ⟨S, hS, hSW⟩ := exists_span_eq_top b (fun W ↦ ∃ (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W)))
      (φY : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φY ∧ Nonempty Y.DetGen) (fun x ↦ by
    obtain ⟨W, hW, hx, Y, φY, hY, hδ⟩ := Obj.exists_affine_nbhd_detGen F 𝔠 M U x
    exact ⟨W, ⟨hW, Y, φY, hY, hδ⟩, hx⟩)

  have hloc : ∀ g : S, ∃ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W)))
      (φY : Y.A.left ⟶ U.A.left) (_ : Y.IsPullBy U hW.fromSpec φY) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W))
      (_ : IsChartFun r₀ Y δY h) (ψ : Γ(M, W) →+* Localization.Away (g : R))
      (Xg : Obj F 𝔠 (Sp (Localization.Away (g : R)))) (φg : Xg.A.left ⟶ X.A.left)
      (_ : Xg.IsPullBy X (spMap (algebraMap R _)) φg) (δg : Xg.DetGen)
      (_ : Obj.DetCorr (algebraMap R _) φg δ.1 δg.1) (χ : Xg.A.left ⟶ Y.A.left)
      (_ : Xg.IsPullBy Y (spMap ψ) χ) (v : Localization.Away (g : R)), IsPresVal k δY h δg ψ χ v := by
    intro g
    obtain ⟨W, ⟨hW, Y, φY, hY, ⟨δY⟩⟩, hsub⟩ := hSW g g.2
    obtain ⟨ψ, hψ⟩ := exists_spMap_fromSpec hW _ hsub
    obtain ⟨h, hh⟩ := H1 W hW Y φY hY δY
    obtain ⟨Xg, φg, hXg⟩ := Obj.exists_isPullBy X (spMap (algebraMap R (Localization.Away (g : R))))
    obtain ⟨δg, hδg, -⟩ := hXg.existsUnique_detGen _ δ
    have h1 : Xg.IsPullBy U (spMap ψ ≫ hW.fromSpec) (φg ≫ φb) := by rw [hψ]; exact hXg.comp hb
    obtain ⟨χ, hχ, -⟩ := h1.cancel hY
    obtain ⟨v, hv⟩ := presVal_exists k δY h δg hχ
    exact ⟨W, hW, Y, φY, hY, δY, h, hh, ψ, Xg, φg, hXg, δg, hδg, χ, hχ, v, hv⟩
  choose W hW Y φY hY δY hc hhc ψ Xg φg hXg δg hδg χ hχ vg hvg using hloc

  have side : ∀ (T : Type) [CommRing T] [Algebra R₀ T] (ρ : R →+* T), ρ.comp (algebraMap R₀ R) = algebraMap R₀ T →
      ∀ (XT : Obj F 𝔠 (Sp T)) (φT : XT.A.left ⟶ X.A.left), XT.IsPullBy X (spMap ρ) φT →
      ∀ δT : XT.DetGen, Obj.DetCorr ρ φT δ.1 δT.1 →
      ∀ (g : S) (f : Localization.Away (g : R) →+* T), f.comp (algebraMap R _) = ρ →
      ∃ θ, XT.IsPullBy (Y g) (spMap (f.comp (ψ g))) θ ∧
        IsPresVal k (δY g) (hc g) δT (f.comp (ψ g)) θ (f (vg g)) := by
    intro T _ _ ρ hρ XT φT hXT δT hδT g f ef
    subst ef
    have hXT' := hXT
    rw [spMap_comp] at hXT'
    obtain ⟨θ, hθ, hθφ⟩ := hXT'.cancel (hXg g)
    have hd : Obj.DetCorr f θ (δg g).1 δT.1 := detCorr_cancel (hXg g) hθ (hδg g) (hθφ ▸ hδT)
    let fA : Localization.Away (g : R) →ₐ[R₀] T :=
      { f with
        commutes' := fun r ↦ by
          rw [IsScalarTower.algebraMap_apply R₀ R (Localization.Away (g : R)), ← hρ]
          rfl }
    refine ⟨θ ≫ χ g, by rw [spMap_comp]; exact hθ.comp (hχ g), ?_⟩
    exact presVal_pull (hχ g) (hvg g) fA hθ hd
  obtain ⟨v, hv, huniq⟩ := existsUnique_glue hS vg (by
    intro g g' T _ f₁ f₂ e
    letI : Algebra R₀ T := ((f₁.comp (algebraMap R _)).comp (algebraMap R₀ R)).toAlgebra
    obtain ⟨XT, φT, hXT⟩ := Obj.exists_isPullBy X (spMap (f₁.comp (algebraMap R _)))
    obtain ⟨δT, hδT, -⟩ := hXT.existsUnique_detGen _ δ
    obtain ⟨θ₁, hθ₁, hv₁⟩ := side T _ rfl XT φT hXT δT hδT g f₁ rfl
    obtain ⟨θ₂, hθ₂, hv₂⟩ := side T _ rfl XT φT hXT δT hδT g' f₂ e.symm
    exact H2 (W g) (hW g) (Y g) (φY g) (hY g) (δY g) (hc g) (hhc g) (W g') (hW g') (Y g') (φY g') (hY g')
      (δY g') (hc g') (hhc g') T XT δT _ θ₁ _ θ₂ hθ₁ hθ₂ _ _ hv₁ hv₂)
  refine ⟨v, ?_, fun v' hv' ↦ huniq v' fun g ↦ ?_⟩
  · intro R' _ _ σ X' φ' δ' hX' hδ' W' hW' Y' φY' hY' δY' h' hh' ψ' χ' hχ'
    obtain ⟨w, hw⟩ := presVal_exists k δY' h' δ' hχ'
    suffices e : σ v = w by rw [e]; exact hw
    have hS' : Ideal.span ((σ : R →+* R') '' S) = ⊤ := by rw [← Ideal.map_span, hS, Ideal.map_top]
    refine eq_of_loc hS' ?_
    rintro ⟨_, g, hg, rfl⟩
    let T := Localization.Away ((σ : R →+* R') g)
    obtain ⟨XT, θ, hθ⟩ := Obj.exists_isPullBy X' (spMap (algebraMap R' T))
    obtain ⟨δT, hδT, -⟩ := hθ.existsUnique_detGen _ δ'
    have e1 : IsPresVal k δY' h' δT ((algebraMap R' T).comp ψ') (θ ≫ χ') (algebraMap R' T w) :=
      presVal_pull hχ' hw (IsScalarTower.toAlgHom R₀ R' T) hθ hδT
    have p1 : XT.IsPullBy Y' (spMap ((algebraMap R' T).comp ψ')) (θ ≫ χ') := by
      rw [spMap_comp]; exact hθ.comp hχ'
    have ef : (Localization.awayMap (σ : R →+* R') g).comp (algebraMap R _) =
        (algebraMap R' T).comp (σ : R →+* R') := IsLocalization.map_comp _
    obtain ⟨θ₁, hθ₁, hv₁⟩ := side T ((algebraMap R' T).comp (σ : R →+* R'))
      (by rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, ← IsScalarTower.algebraMap_eq]) XT (θ ≫ φ')
      (by rw [spMap_comp]; exact hθ.comp hX') δT
      (detCorr_comp hX' hθ hδ' hδT) ⟨g, hg⟩ _ ef
    have e2 := H2 _ (hW _) _ _ (hY _) _ _ (hhc _) W' hW' Y' φY' hY' δY' h' hh' T XT δT _ θ₁ _ _ hθ₁ p1 _ _ hv₁ e1
    rw [← hv ⟨g, hg⟩] at e2
    exact (RingHom.congr_fun ef v).symm.trans e2
  · exact presVal_unique k _ _ _ (hχ g)
      (hv' _ (IsScalarTower.toAlgHom R₀ R (Localization.Away (g : R))) (Xg g) (φg g) (δg g) (hXg g) (hδg g)
        (W g) (hW g) (Y g) (φY g) (hY g) (δY g) (hc g) (hhc g) (ψ g) (χ g) (hχ g)) (hvg g)

end GlobalTheory.RealMult.ModelValGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKillingSquareTripleFibreCocycleMulTwoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_killing_square_tripleFibreCocycle_mulTwo : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsFinite ((𝟙 A) ^ 2 : A ⟶ A).left → ∀ D : Γ(Triple ((𝟙 A) ^ 2 : A ⟶ A).left, ⊤)ˣ, TriCocycle ((𝟙 A) ^ 2 : A ⟶ A).left D → ∃ u, KillsSq ((𝟙 A) ^ 2 : A ⟶ A).left D u := by
  first | exact @GlobalTheory.TwoTors.killsSq_of_triCocycle | exact GlobalTheory.TwoTors.killsSq_of_triCocycle | (intros; apply GlobalTheory.TwoTors.killsSq_of_triCocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorNormalisedZeroSectiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_normalised_zeroSection : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → ∃ u' : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u' (r ≫ zero2 P₀.A) z J = 1 := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | exact GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm <;> assumption)
end

