import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueModulesStar
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PIsoGlueTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace IsoGlueTwo

lemma isIso_app_sup {T : TopCat.{0}} {F G : TopCat.Presheaf AddCommGrpCat.{0} T} (hF : F.IsSheaf)
    (hG : G.IsSheaf) (η : F ⟶ G) (U V : Opens T) (hU : IsIso (η.app (op U)))
    (hV : IsIso (η.app (op V))) (hUV : IsIso (η.app (op (U ⊓ V)))) :
    IsIso (η.app (op (U ⊔ V))) := by
  have lF := TopCat.Sheaf.isLimitPullbackCone ⟨F, hF⟩ U V
  have lG := TopCat.Sheaf.isLimitPullbackCone ⟨G, hG⟩ U V
  have n : ∀ {W W' : Opens T} (i : W ⟶ W') [IsIso (η.app (op W'))] [IsIso (η.app (op W))],
      inv (η.app (op W')) ≫ F.map i.op = G.map i.op ≫ inv (η.app (op W)) := by
    intro W W' i _ _
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← η.naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hw : (G.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op ≫ inv (η.app (op U))) ≫
      F.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op =
      (G.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op ≫ inv (η.app (op V))) ≫
      F.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op := by
    rw [Category.assoc, Category.assoc, n, n, ← G.map_comp_assoc, ← G.map_comp_assoc]
    rfl
  have l₁ := PullbackCone.IsLimit.lift_fst lF _ _ hw
  have l₂ := PullbackCone.IsLimit.lift_snd lF _ _ hw
  change PullbackCone.IsLimit.lift lF _ _ hw ≫ F.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op = _ at l₁
  change PullbackCone.IsLimit.lift lF _ _ hw ≫ F.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op = _ at l₂
  have key : ∀ {W : Opens T} (r : W ⟶ U ⊔ V) (_ : IsIso (η.app (op W)))
      (L : G.obj (op (U ⊔ V)) ⟶ F.obj (op (U ⊔ V)))
      (_ : L ≫ F.map r.op = G.map r.op ≫ inv (η.app (op W))),
      (η.app _ ≫ L) ≫ F.map r.op = 𝟙 _ ≫ F.map r.op ∧
        (L ≫ η.app _) ≫ G.map r.op = 𝟙 _ ≫ G.map r.op := by
    intro W r _ L hL
    constructor
    · rw [Category.assoc, hL, ← Category.assoc, ← η.naturality, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, ← η.naturality, ← Category.assoc, hL, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, Category.id_comp]
  refine ⟨⟨PullbackCone.IsLimit.lift lF _ _ hw, ?_, ?_⟩⟩
  · apply PullbackCone.IsLimit.hom_ext lF
    · exact (key _ hU _ l₁).1
    · exact (key _ hV _ l₂).1
  · apply PullbackCone.IsLimit.hom_ext lG
    · exact (key _ hU _ l₁).2
    · exact (key _ hV _ l₂).2

open Scheme.Modules GlueModulesStar

section Glue

variable {X Z₁ Z₂ T : Scheme.{0}}

def restrictOverlap (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k) (M : X.Modules) :
    (pushforward f).obj ((Scheme.Modules.pullback f).obj M) ⟶
      (pushforward k).obj ((Scheme.Modules.pullback k).obj M) :=
  transMap g f e (pullbackCompIso e (Iso.refl _)).inv

lemma unit_restrictOverlap (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k) (M : X.Modules) :
    (pullbackPushforwardAdjunction f).unit.app M ≫ restrictOverlap g f e M =
      (pullbackPushforwardAdjunction k).unit.app M := by
  have h := homEquiv_pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback f).obj M))
    (pullbackCompIso e (Iso.refl _)).inv
  rw [Iso.hom_inv_id, Iso.refl_hom, Adjunction.homEquiv_id, Adjunction.homEquiv_id] at h
  exact h.symm

lemma transMap_pullback_map (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {M M' : Z₁.Modules} {N : T.Modules} (a : M ⟶ M') (χ : (Scheme.Modules.pullback g).obj M' ⟶ N) :
    transMap g f e ((Scheme.Modules.pullback g).map a ≫ χ) = (pushforward f).map a ≫ transMap g f e χ := by
  simp only [transMap, Adjunction.homEquiv_naturality_left, Functor.map_comp, Category.assoc]

lemma homEquiv_pullbackIsoAlong (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {A B : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) :
    (pullbackPushforwardAdjunction k).homEquiv _ _ (pullbackIsoAlong e φ).hom =
      (pullbackPushforwardAdjunction f).homEquiv _ _ φ.hom ≫ restrictOverlap g f e B := by
  have h := homEquiv_pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback f).obj A))
    ((Scheme.Modules.pullback g).map φ.hom ≫ (pullbackCompIso e (Iso.refl _)).inv)
  have h2 : (pullbackPushforwardAdjunction f).homEquiv _ _ (𝟙 _) ≫ (pushforward f).map φ.hom =
      (pullbackPushforwardAdjunction f).homEquiv _ _ φ.hom := by
    rw [← Adjunction.homEquiv_naturality_right, Category.id_comp]
  rw [transMap_pullback_map, Iso.refl_hom] at h
  rw [restrictOverlap, ← h2, Category.assoc, ← h]
  simp only [pullbackIsoAlong, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]

lemma pullbackIsoAlong_symm (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {A B : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) :
    pullbackIsoAlong e φ.symm = (pullbackIsoAlong e φ).symm := by
  ext1
  simp only [pullbackIsoAlong, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]

variable (f₁ : Z₁ ⟶ X) (f₂ : Z₂ ⟶ X) [IsOpenImmersion f₁] [IsOpenImmersion f₂]
  (g₁ : T ⟶ Z₁) (g₂ : T ⟶ Z₂) [IsOpenImmersion g₁] [IsOpenImmersion g₂] {k : T ⟶ X}
  (e₁ : g₁ ≫ f₁ = k) (e₂ : g₂ ≫ f₂ = k)

omit [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion g₁] [IsOpenImmersion g₂] in

lemma unit_condition (M : X.Modules) :
    (pullbackPushforwardAdjunction f₁).unit.app M ≫ restrictOverlap g₁ f₁ e₁ M =
      (pullbackPushforwardAdjunction f₂).unit.app M ≫ restrictOverlap g₂ f₂ e₂ M := by
  rw [unit_restrictOverlap, unit_restrictOverlap]

def isLimit (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) (M : X.Modules) :
    IsLimit (PullbackCone.mk _ _ (unit_condition f₁ f₂ g₁ g₂ e₁ e₂ M)) := by
  set τ₁ := restrictOverlap g₁ f₁ e₁ M
  set τ₂ := restrictOverlap g₂ f₂ e₂ M
  have w := unit_condition f₁ f₂ g₁ g₂ e₁ e₂ M
  suffices hc : IsIso (pullback.lift _ _ w) by
    haveI : IsIso ((limit.isLimit (cospan τ₁ τ₂)).lift (PullbackCone.mk _ _ w)) := hc
    exact IsLimit.ofPointIso (limit.isLimit _)
  have loc : ∀ (W : X.Opens) (a : Bool),
      (W ≤ (if a then f₁.opensRange else f₂.opensRange)) →
      IsIso ((pullback.lift _ _ w).app W) := by
    intro W a hW
    let Fw : X.Modules ⥤ AddCommGrpCat.{0} :=
      toPresheaf X ⋙ (evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{0}).obj (op W)
    have : PreservesLimitsOfShape WalkingCospan
        ((evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{0}).obj (op W)) :=
      evaluation_preservesLimitsOfShape _
    have : PreservesLimitsOfShape WalkingCospan Fw := comp_preservesLimitsOfShape _ _
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte] at hW
      have : IsIso (Fw.map τ₁) := isIso_transMap_app g₁ f₁ e₁ _ W (h₂₁ W hW)
      have : IsIso (Fw.map (pullback.snd τ₁ τ₂)) := by
        rw [← PreservesPullback.iso_hom_snd Fw]; infer_instance
      have : IsIso (Fw.map ((pullbackPushforwardAdjunction f₂).unit.app M)) :=
        isIso_unit_app f₂ M W hW
      have hc : Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.snd τ₁ τ₂) =
          Fw.map ((pullbackPushforwardAdjunction f₂).unit.app M) := by
        rw [← Fw.map_comp, pullback.lift_snd]
      have : IsIso (Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.snd τ₁ τ₂)) := by
        rw [hc]; infer_instance
      exact IsIso.of_isIso_comp_right (Fw.map (pullback.lift _ _ w)) (Fw.map (pullback.snd τ₁ τ₂))
    · simp only [↓reduceIte] at hW
      have : IsIso (Fw.map τ₂) := isIso_transMap_app g₂ f₂ e₂ _ W (h₁₂ W hW)
      have : IsIso (Fw.map (pullback.fst τ₁ τ₂)) := by
        rw [← PreservesPullback.iso_hom_fst Fw]; infer_instance
      have : IsIso (Fw.map ((pullbackPushforwardAdjunction f₁).unit.app M)) :=
        isIso_unit_app f₁ M W hW
      have hc : Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.fst τ₁ τ₂) =
          Fw.map ((pullbackPushforwardAdjunction f₁).unit.app M) := by
        rw [← Fw.map_comp, pullback.lift_fst]
      have : IsIso (Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.fst τ₁ τ₂)) := by
        rw [hc]; infer_instance
      exact IsIso.of_isIso_comp_right (Fw.map (pullback.lift _ _ w)) (Fw.map (pullback.fst τ₁ τ₂))
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  have hW : W ⊓ f₁.opensRange ⊔ W ⊓ f₂.opensRange = W := by
    rw [← inf_sup_left]; exact inf_eq_left.mpr (le_top.trans hcov)
  rw [← hW]
  exact isIso_app_sup M.isSheaf (pullback τ₁ τ₂).isSheaf (pullback.lift _ _ w).mapPresheaf _ _
    (loc _ true inf_le_right) (loc _ false inf_le_right)
    (loc _ true (inf_le_left.trans inf_le_right))

lemma comp_unit {Z : Scheme.{0}} (f : Z ⟶ X) {A B : X.Modules} (α : A ⟶ B) :
    α ≫ (pullbackPushforwardAdjunction f).unit.app B =
      (pullbackPushforwardAdjunction f).homEquiv _ _ ((Scheme.Modules.pullback f).map α) := by
  rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]

include e₁ e₂ in

lemma hom_ext (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) {A B : X.Modules} (α β : A ⟶ B)
    (h₁ : (Scheme.Modules.pullback f₁).map α = (Scheme.Modules.pullback f₁).map β)
    (h₂ : (Scheme.Modules.pullback f₂).map α = (Scheme.Modules.pullback f₂).map β) : α = β := by
  apply PullbackCone.IsLimit.hom_ext (isLimit f₁ f₂ g₁ g₂ e₁ e₂ hcov h₁₂ h₂₁ B)
  · exact (comp_unit f₁ α).trans ((congrArg _ h₁).trans (comp_unit f₁ β).symm)
  · exact (comp_unit f₂ α).trans ((congrArg _ h₂).trans (comp_unit f₂ β).symm)

lemma exists_hom (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) {A B : X.Modules}
    (φ₁ : (Scheme.Modules.pullback f₁).obj A ⟶ (Scheme.Modules.pullback f₁).obj B)
    (φ₂ : (Scheme.Modules.pullback f₂).obj A ⟶ (Scheme.Modules.pullback f₂).obj B)
    (h : (pullbackPushforwardAdjunction f₁).homEquiv _ _ φ₁ ≫ restrictOverlap g₁ f₁ e₁ B =
      (pullbackPushforwardAdjunction f₂).homEquiv _ _ φ₂ ≫ restrictOverlap g₂ f₂ e₂ B) :
    ∃ α : A ⟶ B, (Scheme.Modules.pullback f₁).map α = φ₁ ∧
      (Scheme.Modules.pullback f₂).map α = φ₂ := by
  have l := isLimit f₁ f₂ g₁ g₂ e₁ e₂ hcov h₁₂ h₂₁ B
  refine ⟨PullbackCone.IsLimit.lift l _ _ h, ?_, ?_⟩
  · apply ((pullbackPushforwardAdjunction f₁).homEquiv _ _).injective
    exact (comp_unit f₁ _).symm.trans (PullbackCone.IsLimit.lift_fst l _ _ h)
  · apply ((pullbackPushforwardAdjunction f₂).homEquiv _ _).injective
    exact (comp_unit f₂ _).symm.trans (PullbackCone.IsLimit.lift_snd l _ _ h)

end Glue

end IsoGlueTwo

theorem IsoGlueTwo.proof : IsoGlueTwo.Statement := by
  intro Y P₁ P₂ P P₁₂ h₁ h₂ hP k₁ k₂ hk A B φ₁ φ₂ hφ
  have e₁ : Y.homOfLE k₁ ≫ Y.homOfLE h₁ = Y.homOfLE (k₁.trans h₁) := Y.homOfLE_homOfLE k₁ h₁
  have e₂ : Y.homOfLE k₂ ≫ Y.homOfLE h₂ = Y.homOfLE (k₁.trans h₁) := Y.homOfLE_homOfLE k₂ h₂
  have hφ' : pullbackIsoAlong e₁ φ₁ = pullbackIsoAlong e₂ φ₂ := hφ
  have hcov : ⊤ ≤ (Y.homOfLE h₁).opensRange ⊔ (Y.homOfLE h₂).opensRange := by
    rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.preimage_sup,
      ← P.ι_preimage_self]
    exact Scheme.Hom.preimage_mono _ hP
  have h₁₂ : ∀ O : (P : Scheme.{0}).Opens, O ≤ (Y.homOfLE h₁).opensRange →
      (Y.homOfLE h₂) ⁻¹ᵁ O ≤ (Y.homOfLE k₂).opensRange := by
    intro O hO
    rw [Scheme.opensRange_homOfLE] at hO ⊢
    refine (Scheme.Hom.preimage_mono _ hO).trans ?_
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
    intro x hx
    have hx2 : P₂.ι x ∈ P₂ := x.2
    exact hk ⟨hx, hx2⟩
  have h₂₁ : ∀ O : (P : Scheme.{0}).Opens, O ≤ (Y.homOfLE h₂).opensRange →
      (Y.homOfLE h₁) ⁻¹ᵁ O ≤ (Y.homOfLE k₁).opensRange := by
    intro O hO
    rw [Scheme.opensRange_homOfLE] at hO ⊢
    refine (Scheme.Hom.preimage_mono _ hO).trans ?_
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
    intro x hx
    have hx1 : P₁.ι x ∈ P₁ := x.2
    exact hk ⟨hx1, hx⟩
  have hhom := congrArg (fun ψ => (Scheme.Modules.pullbackPushforwardAdjunction
    (Y.homOfLE (k₁.trans h₁))).homEquiv _ _ ψ.hom) hφ'
  have hinv := congrArg (fun ψ => (Scheme.Modules.pullbackPushforwardAdjunction
    (Y.homOfLE (k₁.trans h₁))).homEquiv _ _ ψ.symm.hom) hφ'
  simp only [← IsoGlueTwo.pullbackIsoAlong_symm] at hinv
  simp only [IsoGlueTwo.homEquiv_pullbackIsoAlong] at hhom hinv
  obtain ⟨α, hα₁, hα₂⟩ := IsoGlueTwo.exists_hom _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ φ₁.hom φ₂.hom hhom
  obtain ⟨β, hβ₁, hβ₂⟩ := IsoGlueTwo.exists_hom _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ φ₁.inv φ₂.inv hinv
  refine ⟨⟨α, β, ?_, ?_⟩, ?_, ?_⟩
  · apply IsoGlueTwo.hom_ext _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ <;> simp [hα₁, hα₂, hβ₁, hβ₂]
  · apply IsoGlueTwo.hom_ext _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ <;> simp [hα₁, hα₂, hβ₁, hβ₂]
  · ext1; exact hα₁
  · ext1; exact hα₂

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadGlue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

theorem isVectorBundle_of_two {X : Scheme.{0}} {O₁ O₂ O : X.Opens} (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O)
    (hO : O ≤ O₁ ⊔ O₂) {F : (O : Scheme.{0}).Modules}
    (H₁ : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE h₁)).obj F))
    (H₂ : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE h₂)).obj F)) : IsVectorBundle F := by
  have key : ∀ {S : Scheme.{0}} (j : S ⟶ (O : Scheme.{0})) [IsOpenImmersion j],
      IsVectorBundle ((Scheme.Modules.pullback j).obj F) →
        IsVectorBundle ((Scheme.Modules.pullback j.opensRange.ι).obj F) := by
    intro S j _ H
    have e : j.isoOpensRange.inv ≫ j = j.opensRange.ι :=
      (Iso.inv_comp_eq _).2 (Scheme.Hom.isoOpensRange_hom_ι j).symm
    exact (H.pullback_of_isOpenImmersion j.isoOpensRange.inv).of_iso
      (pullbackCompIso e (Iso.refl _)).symm
  refine VectorBundleLocal.proof (O : Scheme.{0}) Bool
    (fun b => bif b then (X.homOfLE h₁).opensRange else (X.homOfLE h₂).opensRange) ?_ F ?_
  · rw [eq_top_iff]
    rintro x -
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases hO x.2 with h | h
    · exact ⟨true, ⟨x.1, h⟩, Scheme.homOfLE_apply' h₁ x.1 h⟩
    · exact ⟨false, ⟨x.1, h⟩, Scheme.homOfLE_apply' h₂ x.1 h⟩
  · intro b
    cases b
    · exact key _ H₂
    · exact key _ H₁

lemma pullbackCompIso_rfl {T Y Z : Scheme.{0}} (g : T ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    pullbackCompIso (rfl : g ≫ h = g ≫ h) (Iso.refl ((Scheme.Modules.pullback h).obj M)) =
      ((Scheme.Modules.pullbackComp g h).app M).symm := by
  ext1
  simp [pullbackCompIso, Scheme.Modules.pullbackCongr]

lemma restrictSpread_eq {X : Scheme.{0}} (f : X ⟶ SpecZ) (R : Type) [CommRing R]
    (E : (baseChange f R).Modules) {V W : X.Opens} (h : V ≤ W) {E' : (W : Scheme.{0}).Modules}
    (α : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj E' ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj E) :
    restrictSpread f R E h α =
      (pullbackCompIso (morphismRestrict_homOfLE (baseChangeMap f R) V W h) (Iso.refl _)).symm ≪≫
        pullbackCompIso rfl α ≪≫
        (pullbackCompIso (Scheme.homOfLE_ι _ ((baseChangeMap f R).preimage_mono h)) (Iso.refl _)).symm := by
  rw [restrictSpread, ← Iso.trans_assoc, pullbackComp_trans_congr, pullbackComp_trans_congr,
    pullbackCompIso_eq_refl_trans _ α, pullbackCompIso_rfl, Iso.trans_assoc]

lemma res_spread {T' T V W Q Y : Scheme.{0}} (u : T' ⟶ T) {g : T ⟶ V} {ℓ : V ⟶ W} {t : T ⟶ Q}
    {gW : Q ⟶ W} {ιQ : Q ⟶ Y} {ι : T ⟶ Y} (mRh : g ≫ ℓ = t ≫ gW) (hιQ : t ≫ ιQ = ι)
    {g' : T' ⟶ V} {s : T' ⟶ Q} {ι' : T' ⟶ Y} (eg : u ≫ g = g') (es : u ≫ t = s) (eι : u ≫ ι = ι')
    (A : g' ≫ ℓ = s ≫ gW) (B : s ≫ ιQ = ι') {E' : W.Modules} {E : Y.Modules}
    (α : (Scheme.Modules.pullback gW).obj E' ≅ (Scheme.Modules.pullback ιQ).obj E) :
    pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback ℓ).obj E'))) ≪≫
      (Scheme.Modules.pullback u).mapIso ((pullbackCompIso mRh (Iso.refl _)).symm ≪≫
        pullbackCompIso (rfl : t ≫ gW = t ≫ gW) α ≪≫ (pullbackCompIso hιQ (Iso.refl _)).symm) ≪≫
      (pullbackCompIso eι (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm =
    (pullbackCompIso A (Iso.refl _)).symm ≪≫ pullbackCompIso (rfl : s ≫ gW = s ≫ gW) α ≪≫
      (pullbackCompIso B (Iso.refl _)).symm := by
  have k1 : u ≫ t ≫ gW = s ≫ gW := by rw [← Category.assoc, es]
  have h1 := mapIso_pullbackCompIso_refl u mRh eg k1 A E'
  have h2 := pullbackCompIso_comp' u (rfl : t ≫ gW = t ≫ gW) es k1 rfl α
  have h2' : (Scheme.Modules.pullback u).mapIso (pullbackCompIso (rfl : t ≫ gW = t ≫ gW) α) =
      (pullbackCompIso k1 (Iso.refl _)).symm ≪≫ pullbackCompIso (rfl : s ≫ gW = s ≫ gW) α ≪≫
        pullbackCompIso es (Iso.refl _) := by
    rw [h2]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  have h3 := mapIso_pullbackCompIso_refl u hιQ es eι B E
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, h1, h2', h3]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.self_symm_id, Iso.trans_refl]

lemma res_phi {T' T P O O₁ O' Y : Scheme.{0}} {u : T' ⟶ T} {a : T ⟶ P} {c : T' ⟶ P} (E1 : u ≫ a = c)
    {gO : P ⟶ O} {gO₁ : T ⟶ O₁} {j : O₁ ⟶ O} (sq1 : gO₁ ≫ j = a ≫ gO)
    {ιP : P ⟶ Y} {ι₁ : T ⟶ Y} (hι : a ≫ ιP = ι₁)
    {gO' : T' ⟶ O'} {k : O' ⟶ O₁} (eg : u ≫ gO₁ = gO' ≫ k) {ι' : T' ⟶ Y} (eι : u ≫ ι₁ = ι')
    (e'ι : c ≫ ιP = ι') (e' : (gO' ≫ k) ≫ j = c ≫ gO)
    {F : O.Modules} {F₁ : O₁.Modules} {E : Y.Modules} (e : (Scheme.Modules.pullback j).obj F ≅ F₁)
    (Rs : (Scheme.Modules.pullback gO₁).obj F₁ ≅ (Scheme.Modules.pullback ι₁).obj E) :
    pullbackIsoAlong E1 ((pullbackCompIso (rfl : a ≫ gO = a ≫ gO) (Iso.refl _)).symm ≪≫
        pullbackCompIso sq1 e ≪≫ Rs ≪≫ pullbackCompIso hι (Iso.refl _)) =
      (pullbackCompIso (rfl : c ≫ gO = c ≫ gO) (Iso.refl _)).symm ≪≫ pullbackCompIso e' e ≪≫
        (pullbackCompIso eg (Iso.refl _) ≪≫ (Scheme.Modules.pullback u).mapIso Rs ≪≫
          (pullbackCompIso eι (Iso.refl _)).symm) ≪≫
        pullbackCompIso e'ι (Iso.refl _) := by
  have ek : u ≫ a ≫ gO = c ≫ gO := by rw [← Category.assoc, E1]
  have h1 := mapIso_pullbackCompIso_refl u (rfl : a ≫ gO = a ≫ gO) E1 ek rfl F
  have h2 := pullbackCompIso_comp' u sq1 eg ek e' e
  have h2' : (Scheme.Modules.pullback u).mapIso (pullbackCompIso sq1 e) =
      (pullbackCompIso ek (Iso.refl _)).symm ≪≫ pullbackCompIso e' e ≪≫ pullbackCompIso eg (Iso.refl _) := by
    rw [h2]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  have h3 := mapIso_pullbackCompIso_refl u hι E1 eι e'ι E
  simp only [pullbackIsoAlong, Functor.mapIso_trans, Functor.mapIso_symm, h1, h2', h3]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.self_symm_id, Iso.trans_refl]

theorem SpreadGlue.proof (hG : GlueTwo.Statement) (hI : IsoGlueTwo.Statement) :
    SpreadGlue.Statement := by
  intro X f R _ E W₁ W₂ E₁ E₂ hE₁ hE₂ α₁ α₂ V _ θ hθ
  have h₁ : W₁ ⊓ V ≤ (W₁ ⊔ W₂) ⊓ V := inf_le_inf_right V le_sup_left
  have h₂ : W₂ ⊓ V ≤ (W₁ ⊔ W₂) ⊓ V := inf_le_inf_right V le_sup_right
  have hO : (W₁ ⊔ W₂) ⊓ V ≤ W₁ ⊓ V ⊔ W₂ ⊓ V := inf_sup_right W₁ W₂ V ▸ le_rfl
  have k₁ : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ V := inf_le_inf_right V inf_le_left
  have k₂ : W₁ ⊓ W₂ ⊓ V ≤ W₂ ⊓ V := inf_le_inf_right V inf_le_right
  have hk : W₁ ⊓ V ⊓ (W₂ ⊓ V) ≤ W₁ ⊓ W₂ ⊓ V := fun x hx => ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
  have l₁ : W₁ ⊓ V ≤ W₁ := inf_le_left
  have l₂ : W₂ ⊓ V ≤ W₂ := inf_le_left
  have m : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ W₂ := inf_le_left
  obtain ⟨F, e₁, e₂, he⟩ := hG X _ _ _ _ h₁ h₂ hO k₁ k₂ hk _ _
    ((pullbackCompIso (X.homOfLE_homOfLE k₁ l₁) (Iso.refl _)).symm ≪≫
      pullbackCompIso (X.homOfLE_homOfLE m (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) (Iso.refl _) ≪≫ θ ≪≫
      (pullbackCompIso (X.homOfLE_homOfLE m (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) (Iso.refl _)).symm ≪≫
      pullbackCompIso (X.homOfLE_homOfLE k₂ l₂) (Iso.refl _))
  have hF : IsVectorBundle F := isVectorBundle_of_two h₁ h₂ hO
    ((hE₁.pullback_of_isOpenImmersion _).of_iso e₁.symm)
    ((hE₂.pullback_of_isOpenImmersion _).of_iso e₂.symm)
  have hP₁ := (baseChangeMap f R).preimage_mono h₁
  have hP₂ := (baseChangeMap f R).preimage_mono h₂
  have hP : baseChangeMap f R ⁻¹ᵁ ((W₁ ⊔ W₂) ⊓ V) ≤ baseChangeMap f R ⁻¹ᵁ (W₁ ⊓ V) ⊔ baseChangeMap f R ⁻¹ᵁ (W₂ ⊓ V) := fun x hx => hO hx
  have kP₁ := (baseChangeMap f R).preimage_mono k₁
  have kP₂ := (baseChangeMap f R).preimage_mono k₂
  have hkP : baseChangeMap f R ⁻¹ᵁ (W₁ ⊓ V) ⊓ baseChangeMap f R ⁻¹ᵁ (W₂ ⊓ V) ≤ baseChangeMap f R ⁻¹ᵁ (W₁ ⊓ W₂ ⊓ V) := fun x hx => hk hx
  have sq1 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ V) ((W₁ ⊔ W₂) ⊓ V) h₁
  have sq2 := morphismRestrict_homOfLE (baseChangeMap f R) (W₂ ⊓ V) ((W₁ ⊔ W₂) ⊓ V) h₂
  have hι1 := (baseChange f R).homOfLE_ι hP₁
  have hι2 := (baseChange f R).homOfLE_ι hP₂
  refine ⟨F, hF, ⟨(hI (baseChange f R) _ _ _ _ hP₁ hP₂ hP kP₁ kP₂ hkP _ _
    ((pullbackCompIso (rfl : (baseChange f R).homOfLE hP₁ ≫ baseChangeMap f R ∣_ ((W₁ ⊔ W₂) ⊓ V) = _) (Iso.refl _)).symm ≪≫
      pullbackCompIso sq1 e₁ ≪≫ restrictSpread f R E l₁ α₁ ≪≫ pullbackCompIso hι1 (Iso.refl _))
    ((pullbackCompIso (rfl : (baseChange f R).homOfLE hP₂ ≫ baseChangeMap f R ∣_ ((W₁ ⊔ W₂) ⊓ V) = _) (Iso.refl _)).symm ≪≫
      pullbackCompIso sq2 e₂ ≪≫ restrictSpread f R E l₂ α₂ ≪≫ pullbackCompIso hι2 (Iso.refl _))
    ?_).choose⟩⟩

  have E1 : (baseChange f R).homOfLE kP₁ ≫ (baseChange f R).homOfLE hP₁ = (baseChange f R).homOfLE (kP₁.trans hP₁) :=
    (baseChange f R).homOfLE_homOfLE _ _
  have E2 : (baseChange f R).homOfLE kP₂ ≫ (baseChange f R).homOfLE hP₂ = (baseChange f R).homOfLE (kP₁.trans hP₁) :=
    (baseChange f R).homOfLE_homOfLE _ _
  have eg1 := (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ V) k₁).symm
  have eg2 := (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₂ ⊓ V) k₂).symm
  have eι1 := (baseChange f R).homOfLE_ι kP₁
  have eι2 := (baseChange f R).homOfLE_ι kP₂
  have eιc := (baseChange f R).homOfLE_ι (kP₁.trans hP₁)
  have e'1 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE k₁) ≫ X.homOfLE h₁ = (baseChange f R).homOfLE (kP₁.trans hP₁) ≫ baseChangeMap f R ∣_ ((W₁ ⊔ W₂) ⊓ V) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have e'2 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE k₂) ≫ X.homOfLE h₂ = (baseChange f R).homOfLE (kP₁.trans hP₁) ≫ baseChangeMap f R ∣_ ((W₁ ⊔ W₂) ⊓ V) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have mRh1 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ V) W₁ l₁
  have mRh2 := morphismRestrict_homOfLE (baseChangeMap f R) (W₂ ⊓ V) W₂ l₂
  have hιQ1 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono l₁)
  have hιQ2 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono l₂)
  have es1 : (baseChange f R).homOfLE kP₁ ≫ (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono l₁) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) := (baseChange f R).homOfLE_homOfLE _ _
  have es2 : (baseChange f R).homOfLE kP₂ ≫ (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono l₂) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) := (baseChange f R).homOfLE_homOfLE _ _
  have A1 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE k₁) ≫ X.homOfLE l₁ =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) ≫ baseChangeMap f R ∣_ W₁ := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have A2 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE k₂) ≫ X.homOfLE l₂ =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) ≫ baseChangeMap f R ∣_ W₂ := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have B1 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono (k₁.trans l₁))
  have B2 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono (k₂.trans l₂))
  rw [res_phi E1 sq1 hι1 eg1 eι1 eιc e'1 e₁, res_phi E2 sq2 hι2 eg2 eι2 eιc e'2 e₂,
    restrictSpread_eq, restrictSpread_eq, res_spread _ mRh1 hιQ1 eg1 es1 eι1 A1 B1,
    res_spread _ mRh2 hιQ2 eg2 es2 eι2 A2 B2]

  have ekO := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) ((W₁ ⊔ W₂) ⊓ V) (k₁.trans h₁)
  have c1 := pullbackCompIso_comp' (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) (X.homOfLE_homOfLE k₁ h₁) rfl ekO e'1 e₁
  have c2 := pullbackCompIso_comp' (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) (X.homOfLE_homOfLE k₂ h₂) rfl ekO e'2 e₂
  rw [c2, he, c1]

  have ek1 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) W₁ (k₁.trans l₁)
  have ek2 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) W₂ (k₂.trans l₂)
  have Am1 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE m) ≫ X.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) ≫ baseChangeMap f R ∣_ W₁ := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have Am2 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE m) ≫ X.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) ≫ baseChangeMap f R ∣_ W₂ := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have hk1' := mapIso_pullbackCompIso_refl (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) (X.homOfLE_homOfLE k₁ l₁) rfl ek1 A1 E₁
  have hk2' := mapIso_pullbackCompIso_refl (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) (X.homOfLE_homOfLE k₂ l₂) rfl ek2 A2 E₂
  have hm1' := mapIso_pullbackCompIso_refl (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V))
    (X.homOfLE_homOfLE m (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) rfl ek1 Am1 E₁
  have hm2' := mapIso_pullbackCompIso_refl (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V))
    (X.homOfLE_homOfLE m (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) rfl ek2 Am2 E₂
  have hθ' : (Scheme.Modules.pullback (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V))).mapIso θ =
      (pullbackCompIso (rfl : baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE m = _) (Iso.refl _)).symm ≪≫
        pullbackIsoAlong (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂) m).symm
          (overlapIso f R E α₁ α₂) ≪≫
        pullbackCompIso (rfl : baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE m = _) (Iso.refl _) := by
    rw [← hθ]
    simp only [pullbackIsoAlong, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id,
      Iso.trans_refl]

  have mRh'1 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂) W₁ inf_le_left
  have mRh'2 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂) W₂ inf_le_right
  have hιQ'1 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono (inf_le_left : W₁ ⊓ W₂ ≤ W₁))
  have hιQ'2 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono (inf_le_right : W₁ ⊓ W₂ ≤ W₂))
  have es'1 : (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono m) ≫
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) := (baseChange f R).homOfLE_homOfLE _ _
  have es'2 : (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono m) ≫
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) := (baseChange f R).homOfLE_homOfLE _ _
  have eιs := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono m)
  have r1 := res_spread _ mRh'1 hιQ'1 (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂) m).symm
    es'1 eιs Am1 B1 α₁
  have r2 := res_spread _ mRh'2 hιQ'2 (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂) m).symm
    es'2 eιs Am2 B2 α₂
  have hov : pullbackIsoAlong (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂) m).symm
      (overlapIso f R E α₁ α₂) =
      ((pullbackCompIso Am1 (Iso.refl _)).symm ≪≫
        pullbackCompIso (rfl : (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) ≫ baseChangeMap f R ∣_ W₁ = _) α₁ ≪≫
        (pullbackCompIso B1 (Iso.refl _)).symm) ≪≫
      ((pullbackCompIso Am2 (Iso.refl _)).symm ≪≫
        pullbackCompIso (rfl : (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) ≫ baseChangeMap f R ∣_ W₂ = _) α₂ ≪≫
        (pullbackCompIso B2 (Iso.refl _)).symm).symm := by
    rw [← r1, ← r2, overlapIso, restrictSpread_eq, restrictSpread_eq]
    simp only [pullbackIsoAlong, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm,
      Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm]
  rw [hk1', hm1', hθ', hov, hm2', hk2']
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl]

end

end GroundTheory.Heights₂.Heights.Model
end

