import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairPreimageBaseChangeFstIsBasis
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem exists_affineOpen_nhds_le {X : Scheme.{0}} (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (W : Set X) from hx) W.isOpen
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

theorem pairBC_fst_basis : ∀ (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (e : f₁ ≫ pr = pr' ≫ f₀), (∀ U : Y₁.Opens, ∃ V : Y₀.Opens, pr' ⁻¹ᵁ V = U) → (∀ (x : Y₁) (U : Y₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : Y₁) (U : Y₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ Y₀ Y₁ pr pr' _ _ f₀ f₁ e hsurj
  constructor
  · intro x U hx
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    obtain ⟨V, hfV, -⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) ⊤ trivial
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x) (W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨hy, hfV⟩
    refine ⟨Opposite.op (⟨(U', V), hU'le.trans inf_le_right⟩ : Pair f₀), ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans inf_le_left)
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    have hy₁ : pr' x ∈ t₁.unop.1.1.1 := h₁
    have hy₂ : pr' x ∈ t₂.unop.1.1.1 := h₂
    have hf₁ : f₀ (pr' x) ∈ t₁.unop.1.2.1 := t₁.unop.2 hy₁
    have hf₂ : f₀ (pr' x) ∈ t₂.unop.1.2.1 := t₂.unop.2 hy₂
    obtain ⟨V, hfV, hVle⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) (t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨hf₁, hf₂⟩
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x)
      (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1 ⊓ W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨⟨⟨hy₁, hy₂⟩, hy⟩, hfV⟩
    let p : Pair f₀ := ⟨(U', V), hU'le.trans inf_le_right⟩
    have hp₁ : p ≤ t₁.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)), hVle.trans inf_le_left⟩)
    have hp₂ : p ≤ t₂.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)), hVle.trans inf_le_right⟩)
    refine ⟨Opposite.op p, ⟨(homOfLE hp₁).op⟩, ⟨(homOfLE hp₂).op⟩, ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans (inf_le_left.trans inf_le_right))

end GlobalTheory.Obs.BC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPairsCommaAcyclicDegreeLeTwo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CatCoh.Desc

universe v u

section Retract

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
  {T : C} (P : ∀ S, (T ⟶ S) → Prop) (Q : C → Prop) (hQ : ∀ S, (T ⟶ S) → Q S)
  (G : ∀ S, Q S → C) (θ : ∀ S h, S ⟶ G S h)
  (p : ∀ S (u : T ⟶ S), G T (hQ T (𝟙 T)) ⟶ G S (hQ S u))
  (m : ∀ S S' (h : Q S) (h' : Q S'), (S ⟶ S') → (G S h ⟶ G S' h'))
  (hp : ∀ S u, θ T (hQ T (𝟙 T)) ≫ p S u = u ≫ θ S (hQ S u))
  (hθ : ∀ S S' h h' (ψ : S ⟶ S'), θ S h ≫ m S S' h h' ψ = ψ ≫ θ S' h')
  (hpm : ∀ S S' u (ψ : S ⟶ S'), p S u ≫ m S S' _ _ ψ = p S' (u ≫ ψ))
  (hmm : ∀ S S' S'' h h' h'' (ψ : S ⟶ S') (χ : S' ⟶ S''),
    m S S' h h' ψ ≫ m S' S'' h' h'' χ = m S S'' h h'' (ψ ≫ χ))
  (bij : ∀ S h, Function.Bijective (mp F (θ S h)))
  (h0 : P _ (θ T (hQ T (𝟙 T))))

include hQ bij h0 in

theorem sep_of_retract : Sep F P := by
  intro x hx
  refine (bij T (hQ T (𝟙 T))).1 ?_
  rw [hx _ _ h0, map_zero]

include hp bij h0 in

theorem glue_of_retract : Glue F P := by
  intro s hs
  obtain ⟨x, hx⟩ := (bij T (hQ T (𝟙 T))).2 (s _ (θ T (hQ T (𝟙 T))))
  refine ⟨x, fun S u hu ↦ (bij S (hQ S u)).1 ?_⟩
  rw [← mp_comp, ← hp, mp_comp, hx, ← hs _ _ _ _ h0, hp, hs _ _ _ _ hu]

include hp hθ hpm bij h0 in

theorem cocycleOne_vanishing_of_natural_additive_retract : Van1 F P := by
  intro a ha
  have e : ∀ S (h : Q S) y, mp F (θ S h) (Function.surjInv (bij S h).2 y) = y :=
    fun S h y ↦ Function.surjInv_eq (bij S h).2 y
  refine ⟨fun S u ↦ Function.surjInv (bij S (hQ S u)).2
    (a _ _ (θ T (hQ T (𝟙 T))) (p S u) - a _ _ u (θ S (hQ S u))), fun S S' u ψ hu ↦ ?_⟩
  refine (bij S' (hQ S' (u ≫ ψ))).1 ?_
  rw [map_sub, e, ← mp_comp, ← hθ S S' (hQ S u) (hQ S' (u ≫ ψ)) ψ, mp_comp, e]
  have k1 := ha _ _ _ _ (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ) h0
  have k2 := ha _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) hu
  have k3 := ha _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ) hu
  rw [hpm, hp] at k1
  rw [hθ] at k3
  simp only [map_sub]
  linear_combination k1 - k3 + k2

include hp hθ hpm hmm bij h0 in

theorem cocycleTwo_vanishing_of_natural_additive_retract : Van2 F P := by
  intro z hz
  have e : ∀ S (h : Q S) y, mp F (θ S h) (Function.surjInv (bij S h).2 y) = y :=
    fun S h y ↦ Function.surjInv_eq (bij S h).2 y
  refine ⟨fun S S' u ψ ↦ Function.surjInv (bij S' (hQ S' (u ≫ ψ))).2
    (z _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) - z _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ) +
      z _ _ _ (θ T (hQ T (𝟙 T))) (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ)),
    fun S S' S'' u ψ χ hu ↦ ?_⟩
  refine (bij S'' (hQ S'' (u ≫ ψ ≫ χ))).1 ?_
  rw [map_add, map_sub, e, e, ← mp_comp,
    ← hθ S' S'' (hQ S' (u ≫ ψ)) (hQ S'' (u ≫ ψ ≫ χ)) χ, mp_comp, e]
  have c1 := hz _ _ _ _ _ (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ)
    (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) h0
  have c2 := hz _ _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ)
    (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) hu
  have c3 := hz _ _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) hu
  have c4 := hz _ _ _ _ u ψ χ (θ S'' (hQ S'' (u ≫ ψ ≫ χ))) hu
  rw [hpm, hmm, hp] at c1
  rw [hθ, hmm] at c2
  rw [hθ] at c3
  simp only [map_add, map_sub]
  linear_combination c3 - c4 - c2 + c1

end Retract

end GlobalTheory.CatCoh.Desc

namespace GlobalTheory.PDForm

open KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
  GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.SmoothLift GlobalTheory.CatCoh.Desc

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  {Y : Scheme.{0}} {i : X ⟶ Y}

theorem le_preimage_of_hom {T S : (IsSm κ t i).FullSubcategory} (u : T ⟶ S) {V : Y.Opens}
    (hV : ⊤ ≤ (T.obj.T.x ≫ i) ⁻¹ᵁ V) : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V := by
  intro z _
  rw [← u.hom.1.pt, Category.assoc, Scheme.Hom.comp_preimage]
  exact hV trivial

def cutPr (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (V : Y.affineOpens) (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1) :
    (IsSm κ t i).FullSubcategory :=
  ⟨⟨S.obj.T, S.obj.U ⊓ V.1, Or.inl (by
    rcases S.obj.hU with hU | hU
    · exact hY _ _ hU V.2
    · rw [hU, top_inf_eq]; exact V.2), fun z _ ↦ ⟨S.obj.mem trivial, h trivial⟩⟩, ⟨V, h⟩⟩

theorem cutPr_aff (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (V : Y.affineOpens) (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1) :
    IsAffineOpen (cutPr hY V S h).obj.U := by
  rcases S.obj.hU with hU | hU
  · exact hY _ _ hU V.2
  · change IsAffineOpen (S.obj.U ⊓ V.1)
    rw [hU, top_inf_eq]; exact V.2

def prHom {S S' : (IsSm κ t i).FullSubcategory} (φ : S.obj.T ⟶ S'.obj.T) (h : S'.obj.U ≤ S.obj.U) :
    S ⟶ S' :=
  ObjectProperty.homMk ⟨φ, h⟩

theorem prHom_ext {S S' : (IsSm κ t i).FullSubcategory} {f g : S ⟶ S'} (h : f.hom.1 = g.hom.1) :
    f = g :=
  ObjectProperty.hom_ext _ (Subtype.ext h)

theorem isSm_acyclic (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (T : (IsSm κ t i).FullSubcategory) :
    Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) := by
  obtain ⟨V, hV⟩ := T.property
  have hQ : ∀ S (u : T ⟶ S), ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1 := fun S u ↦ le_preimage_of_hom u hV
  let θ : ∀ (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1), S ⟶ cutPr hY V S h := fun S h ↦ prHom (𝟙 S.obj.T) inf_le_left
  let p : ∀ S (u : T ⟶ S), cutPr hY V T (hQ T (𝟙 T)) ⟶ cutPr hY V S (hQ S u) :=
    fun S u ↦ prHom u.hom.1 (inf_le_inf_right _ u.hom.2)
  let m : ∀ (S S' : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1)
      (h' : ⊤ ≤ (S'.obj.T.x ≫ i) ⁻¹ᵁ V.1), (S ⟶ S') → (cutPr hY V S h ⟶ cutPr hY V S' h') :=
    fun S S' h h' ψ ↦ prHom ψ.hom.1 (inf_le_inf_right _ ψ.hom.2)
  have hp : ∀ S u, θ T (hQ T (𝟙 T)) ≫ p S u = u ≫ θ S (hQ S u) :=
    fun S u ↦ prHom_ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hθ : ∀ S S' h h' (ψ : S ⟶ S'), θ S h ≫ m S S' h h' ψ = ψ ≫ θ S' h' :=
    fun S S' h h' ψ ↦ prHom_ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hpm : ∀ S S' u (ψ : S ⟶ S'), p S u ≫ m S S' _ _ ψ = p S' (u ≫ ψ) :=
    fun S S' u ψ ↦ prHom_ext rfl
  have hmm : ∀ S S' S'' h h' h'' (ψ : S ⟶ S') (χ : S' ⟶ S''),
      m S S' h h' ψ ≫ m S' S'' h' h'' χ = m S S'' h h'' (ψ ≫ χ) :=
    fun S S' S'' h h' h'' ψ χ ↦ prHom_ext rfl
  have bij : ∀ S h, Function.Bijective (mp ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (θ S h)) :=
    fun S h ↦ ⟨fun a b hab ↦ hab, fun y ↦ ⟨y, rfl⟩⟩
  have h0 := cutPr_aff hY V T (hQ T (𝟙 T))
  exact ⟨sep_of_retract _ _ _ hQ _ θ bij h0, glue_of_retract _ _ _ hQ _ θ p hp bij h0,
    cocycleOne_vanishing_of_natural_additive_retract _ _ _ hQ _ θ p m hp hθ hpm bij h0,
    cocycleTwo_vanishing_of_natural_additive_retract _ _ _ hQ _ θ p m hp hθ hpm hmm bij h0⟩

theorem isSm_acyclic_two : (∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ∀ T : (IsSm κ t i).FullSubcategory,
      Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
      Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
      Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U)) ∧
    ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R)
      (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ∀ T : (IsSm κ t i).FullSubcategory,
      Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) :=
  ⟨fun _ _ _ _ _ _ _ _ hY T ↦ ⟨(isSm_acyclic hY T).1, (isSm_acyclic hY T).2.1, (isSm_acyclic hY T).2.2.1⟩,
    fun _ _ _ _ _ _ _ _ hY T ↦ (isSm_acyclic hY T).2.2.2⟩

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicEndomorphismCorankDeRham
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescRank

open TensorProduct

variable {K L : Type} [Field K] [Field L] [Algebra K L] {P P' : Type*} [AddCommGroup P] [Module K P]
  [AddCommGroup P'] [Module L P'] (mp : P →ₛₗ[algebraMap K L] P') (hbc : Function.Bijective (liftSemi mp))
include hbc

theorem ext_of_bc {φ₁ φ₂ : Module.Dual L P'} (h : ∀ c, φ₁ (mp c) = φ₂ (mp c)) : φ₁ = φ₂ := by
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨z, rfl⟩ := hbc.2 y
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

def extForm (v : Module.Dual K P) : Module.Dual L P' :=
  liftSemi ({ toFun := fun c ↦ algebraMap K L (v c), map_add' := by simp, map_smul' := by simp } :
      P →ₛₗ[algebraMap K L] L) ∘ₗ (LinearEquiv.ofBijective _ hbc).symm.toLinearMap

theorem extForm_apply (v : Module.Dual K P) (c : P) : extForm mp hbc v (mp c) = algebraMap K L (v c) := by
  have : mp c = LinearEquiv.ofBijective _ hbc (1 ⊗ₜ c) := (one_smul L (mp c)).symm
  rw [extForm, this, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, liftSemi_tmul, one_smul]
  rfl

theorem extForm_zero : extForm mp hbc 0 = 0 :=
  ext_of_bc mp hbc fun c ↦ by rw [extForm_apply]; simp

theorem extForm_injective : Function.Injective (extForm mp hbc) := by
  intro v w h
  refine LinearMap.ext fun c ↦ (algebraMap K L).injective ?_
  rw [← extForm_apply mp hbc, ← extForm_apply mp hbc, h]

variable (g₀ : P →ₗ[K] P) (g : P' →ₗ[L] P') (hg : ∀ c, g (mp c) = mp (g₀ c))
include hg

theorem extForm_dualMap (w : Module.Dual K P) :
    extForm mp hbc (g₀.dualMap w) = g.dualMap (extForm mp hbc w) :=
  ext_of_bc mp hbc fun c ↦ by
    rw [extForm_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, hg, extForm_apply]

theorem disjoint_desc (h : Disjoint (LinearMap.ker g.dualMap) (LinearMap.range g.dualMap)) :
    Disjoint (LinearMap.ker g₀.dualMap) (LinearMap.range g₀.dualMap) := by
  rw [Submodule.disjoint_def] at h ⊢
  rintro v hv ⟨w, rfl⟩
  have e := h (extForm mp hbc (g₀.dualMap w))
    (by rw [LinearMap.mem_ker, ← extForm_dualMap mp hbc g₀ g hg, LinearMap.mem_ker.1 hv, extForm_zero])
    ⟨extForm mp hbc w, (extForm_dualMap mp hbc g₀ g hg w).symm⟩
  exact extForm_injective mp hbc (e.trans (extForm_zero mp hbc).symm)

end GlobalTheory.DescRank

namespace GlobalTheory.DescRank

open TensorProduct

theorem rank_quot_range_dualMap {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) : Module.rank k (Module.Dual k V ⧸ LinearMap.range f.dualMap) = Module.finrank k (LinearMap.ker f) := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, (Subspace.quotAnnihilatorEquiv _).rank_eq, ← Module.finrank_eq_rank,
    Subspace.dual_finrank_eq]

variable {K L : Type} [Field K] [Field L] [Algebra K L] {P P' : Type*} [AddCommGroup P] [Module K P]
  [AddCommGroup P'] [Module L P'] (mp : P →ₛₗ[algebraMap K L] P') (hbc : Function.Bijective (liftSemi mp))
  (g₀ : P →ₗ[K] P) (g : P' →ₗ[L] P') (hg : ∀ c, g (mp c) = mp (g₀ c))
include hbc hg

theorem rank_coker_desc [FiniteDimensional K P]
    (h : Module.rank L (Module.Dual L P' ⧸ LinearMap.range g.dualMap) ≤ 2) :
    Module.rank K (Module.Dual K P ⧸ LinearMap.range g₀.dualMap) ≤ 2 := by
  haveI : FiniteDimensional L P' := Module.Finite.equiv (LinearEquiv.ofBijective _ hbc)
  rw [rank_quot_range_dualMap] at h ⊢
  let j₀ : L ⊗[K] LinearMap.ker g₀ →ₗ[L] P' := liftSemi mp ∘ₗ (LinearMap.ker g₀).subtype.baseChange L
  have hj₀ : Function.Injective j₀ := by
    refine hbc.1.comp ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have hmem : ∀ z, j₀ z ∈ LinearMap.ker g := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul x c =>
      simp only [j₀, LinearMap.comp_apply, LinearMap.baseChange_tmul, Submodule.coe_subtype, liftSemi_tmul,
        LinearMap.mem_ker, map_smul, hg, LinearMap.mem_ker.1 c.2, map_zero, smul_zero]
  let j : L ⊗[K] LinearMap.ker g₀ →ₗ[L] LinearMap.ker g := LinearMap.codRestrict _ j₀ hmem
  have hj : Function.Injective j := fun x y e ↦ hj₀ (congrArg Subtype.val e)
  have hle := LinearMap.finrank_le_finrank_of_injective hj
  rw [Module.finrank_baseChange] at hle
  have h' : Module.finrank L (LinearMap.ker g) ≤ 2 := by exact_mod_cast h
  exact_mod_cast hle.trans h'

end GlobalTheory.DescRank

namespace GlobalTheory.DescRank

theorem desc_of_baseChange : GlobalTheory.Published.AbelianDeRham →
    ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X₀ : Obj F 𝔠 (Sp Qb)) (X : Obj F 𝔠 (Sp ℂ))
      (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (b : 𝓞 F) (β : Qb),
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) ≤ 2 →
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) →
      Module.rank Qb (HdR X₀.A ⧸ LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1))
        (LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) := by
  intro hD F _ _ 𝔠 X₀ X p hp b β hrank hdisj
  let m := GlobalTheory.Published.AbelianDeRham.bcMor hp.grp
  have hBC : m.IsBC := (hD.2.2.1 Qb X₀.A _ X₀.ab X₀.dim ℂ X.A p hp.grp).1
  haveI : FiniteDimensional Qb (prim (dp0 Qb) (𝟙 _) X₀.A) := (GlobalTheory.Published.AbelianDeRham.Free.prim hD.1 X₀.ab X₀.dim).1
  haveI := X₀.rm.hom
  haveI := X.rm.hom
  let g₀ := primPull (dp0 Qb) (𝟙 _) (X₀.rm.act b) - β • LinearMap.id
  let g := primPull (dp0 ℂ) (𝟙 _) (X.rm.act b) - algebraMap Qb ℂ β • LinearMap.id
  have e₀ : act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1 = g₀.dualMap := by
    refine LinearMap.ext fun h ↦ LinearMap.ext fun c ↦ ?_
    simp [g₀, act_apply, push_apply, smul_eq_mul]
  have e : act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1 = g.dualMap := by
    refine LinearMap.ext fun h ↦ LinearMap.ext fun c ↦ ?_
    simp [g, act_apply, push_apply, smul_eq_mul]
  have hg : ∀ c, g (m.pull c) = m.pull (g₀ c) := by
    intro c
    have k := (homMor (dp0 Qb) (𝟙 _) (X₀.rm.act b)).comp m
    have e1 : primPull (dp0 ℂ) (𝟙 _) (X.rm.act b) (m.pull c) = k.pull c :=
      GrpMor.pull_pull m (homMor (dp0 ℂ) (𝟙 _) (X.rm.act b)) k (fun _ ↦ rfl) (hp.act b) c
    have e2 : m.pull (primPull (dp0 Qb) (𝟙 _) (X₀.rm.act b) c) = k.pull c :=
      GrpMor.pull_pull (homMor (dp0 Qb) (𝟙 _) (X₀.rm.act b)) m k (fun _ ↦ rfl) rfl c
    simp only [g, g₀, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smulₛₗ, e1, e2]
  rw [e₀]
  rw [e] at hrank hdisj
  exact ⟨rank_coker_desc m.pull hBC g₀ g hg hrank, disjoint_desc m.pull hBC g₀ g hg hdisj⟩

end GlobalTheory.DescRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastInverseDifferentElement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

noncomputable section

namespace GlobalTheory.DiffSize

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_intCast (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    ‖((m : ℤ) : ℂ_[p])‖ = (p : ℝ) ^ (-(padicValInt p m : ℤ)) := by
  have e : ((m : ℤ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((m : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_intCast, map_intCast]
  rw [e]
  refine (PadicComplex.norm_extends' (p := p) _).trans ?_
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm),
    padicValRat.of_int]
  push_cast; rfl

theorem pow_mem {K : Type} [Field K] [NumberField K] {I : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ I) (k : ℕ) :
    x ^ k ∈ I ^ k := by
  induction k with
  | zero => simpa using FractionalIdeal.one_mem_one (R := 𝓞 K) (K := K)
  | succ k ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih hx

theorem exists_int_mul_pow {F : Type} [Field F] [NumberField F] [IsGalois ℚ F] {y : F}
    (hy : y ∈ latM (1 : Frac F)) : ∃ c : 𝓞 F, (c : F) = (discr F : F) * y ^ Module.finrank ℚ F := by
  have hd : (discr F : F) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have h1 : latM (1 : Frac F) = ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    simp [latM]
  rw [h1] at hy
  have h2 := pow_mem hy (Module.finrank ℚ F)
  rw [inv_pow, ← FractionalIdeal.coeIdeal_pow, GlobalTheory.T.differentIdeal_pow_finrank_eq_span_discr' F, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv] at h2
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_spanSingleton _).1 h2
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def, map_intCast] at hc
  rw [← hc]; field_simp

theorem sz_invDiff : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [IsGalois ℚ F] (y : F) (i : Emb F), y ∈ latM (1 : Frac F) → Sz l lam ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F) ((i y : ℝ) : ℂ) := by
  intro l _ lam F _ _ _ _ y i hy
  obtain ⟨c, hc⟩ := exists_int_mul_pow hy
  let φ : F →+* ℂ := Complex.ofRealHom.comp i
  have hmem : ∀ x : F, φ x ∈ algebraicClosure ℚ ℂ := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic x).algHom φ.toRatAlgHom
  let ψ : F →+* algebraicClosure ℚ ℂ := φ.codRestrict (algebraicClosure ℚ ℂ) hmem
  let χ : F →+* ℂ_[l] := lam.comp ψ
  refine ⟨hmem y, ?_⟩
  change ‖χ y‖ ≤ _
  have hd0 : discr F ≠ 0 := discr_ne_zero F
  have hcint : ‖χ (c : F)‖ ≤ 1 :=
    norm_le_one_of_isIntegral (by convert map_isIntegral_int χ (RingOfIntegers.isIntegral_coe c); exact Subsingleton.elim _ _)
  have hdn : ‖χ (discr F : F)‖ = (l : ℝ) ^ (-(padicValInt l (discr F) : ℤ)) := by
    rw [map_intCast]; exact norm_intCast l _ hd0
  set n := Module.finrank ℚ F
  set v := padicValInt l (discr F)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hkey : ‖χ y‖ ^ n * (l : ℝ) ^ (-(v : ℤ)) ≤ 1 := by
    rw [← hdn, ← norm_pow, ← norm_mul, ← map_pow, ← map_mul, mul_comm, ← hc]; exact hcint
  have hpow : ‖χ y‖ ^ n ≤ (l : ℝ) ^ (v : ℝ) := by
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(v : ℤ)) := zpow_pos hl0 _
    have := (le_div_iff₀ hpos).2 hkey
    rw [one_div, ← zpow_neg, neg_neg, zpow_natCast] at this
    rwa [Real.rpow_natCast]
  have hn : 0 < n := Module.finrank_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  calc ‖χ y‖ = (‖χ y‖ ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (norm_nonneg _) hn.ne').symm
    _ ≤ ((l : ℝ) ^ (v : ℝ)) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (l : ℝ) ^ ((v : ℝ) / n) := by rw [← Real.rpow_mul hl0.le, div_eq_mul_inv]

end GlobalTheory.DiffSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_twist_normalisedBlowup_noetherian_domain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X X' N : Scheme.{0}) (s : X ⟶ Sp R) (J : X.IdealSheafData) (b : X' ⟶ X) (ν : N ⟶ X') (EX : EffCartierData N), IsProjOver s → FinalTheorems.Blowup b J → IsFinite ν → EX.idealSheaf = J.comap (ν ≫ b) → ∀ L : LB X, IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → IsAmpleLB (CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (CechPic.dual EX.lb)) := by
  first | exact @GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup | exact GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup | (intros; apply GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatementStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anchor_bound_statement : Anchor := by
  first | exact @GlobalTheory.CovTop.anchor_holds | exact GlobalTheory.CovTop.anchor_holds | (intros; apply GlobalTheory.CovTop.anchor_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicPropertiesStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_sigma_map_basic_properties : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → (∀ y, σ y ∈ I.map (algebraMap R B)) ∧ (∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y) ∧ (∀ b₀ : B₀, σ (1 ⊗ₜ b₀) = 0) ∧ ∀ x ∈ I.map (algebraMap R B), ∃ y, α.KerQ y ∧ σ y = x := by
  first | exact @GlobalTheory.Obs.sig_basic | exact GlobalTheory.Obs.sig_basic | (intros; apply GlobalTheory.Obs.sig_basic <;> assumption)
end

