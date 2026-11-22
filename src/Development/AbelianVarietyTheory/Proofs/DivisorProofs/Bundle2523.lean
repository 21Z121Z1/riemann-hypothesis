import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyOpenChartAffineFiniteType
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

section Helpers
variable {S : Scheme.{0}} {A : Over S}

theorem same_of_same_of_same {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB)
    (hM : M.IsLB) {y : Y ⟶ T} {u₁ u₂ : Y ⟶ U} (h₁ : Same A N M y u₁) (h₂ : Same A N M y u₂) :
    Same A M M u₁ u₂ := by
  rw [same_iff hN hM] at h₁ h₂
  rw [same_iff hM hM, ← h₁, h₂]

theorem same_ev_param_iff {T U P Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB)
    (hM : M.IsLB) (g : P ⟶ T) (h : P ⟶ U) (w : Y ⟶ P) :
    Same A (ev N (fst A P) (snd A P ≫ g)) (ev M (fst A P) (snd A P ≫ h)) w w ↔ Same A N M (w ≫ g) (w ≫ h) := by
  rw [same_iff (pull_isLB hN _) (pull_isLB hM _), same_iff hN hM, evc_ev hN, evc_ev hM]
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

variable [GrpObj A]

theorem Fam.ev_param {T P : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (g : P ⟶ T) :
    Fam A (ev N (fst A P) (snd A P ≫ g)) := by
  refine ⟨pull_isLB hN.isLB _, (isAdditive_iff (pull_isLB hN.isLB _)).2 fun Y a a' t ↦ ?_⟩
  rw [evc_ev hN.isLB, evc_ev hN.isLB, evc_ev hN.isLB]
  simp only [lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Y a a' (t ≫ g)

end Helpers

theorem chartAt_of_lifting : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), LocallyOfFiniteType U.hom → Fam A M → Inj A M → (∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Mono f], (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → IsOpenImmersion f) → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ (N : LB (A ⊗ T).left), Fam A N → (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left) (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U), Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ → ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u) → ChartAt A M N := by
  intro R _ _ A _ hA U M hU hM hInj crit T _ hT N hN hlift
  haveI : LocallyOfFiniteType T.hom := hT
  haveI : LocallyOfFiniteType U.hom := hU
  haveI : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  haveI : LocallyOfFiniteType (T ⊗ U).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst T.hom U.hom ≫ T.hom))
  haveI : IsLocallyNoetherian (T ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (T ⊗ U).hom
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree (Sp R) A (T ⊗ U) hA _ _ (hN.ev_param (fst T U)) (hM.ev_param (snd T U))
  have key : ∀ (Y : Over (Sp R)) (w : Y ⟶ T ⊗ U),
      Same A N M (w ≫ fst T U) (w ≫ snd T U) ↔ ∃ z : Y ⟶ G, z ≫ i = w := fun Y w ↦
    (same_ev_param_iff hN.isLB hM.isLB _ _ w).symm.trans (hG Y w)
  obtain ⟨f, hfdef⟩ : ∃ f : G.left ⟶ T.left, f = (i ≫ fst T U).left := ⟨_, rfl⟩
  have hf : f ≫ T.hom = G.hom := by rw [hfdef]; exact Over.w (i ≫ fst T U)
  have hfz : ∀ {Y : Over (Sp R)} (z : Y ⟶ G), (z ≫ i ≫ fst T U).left = z.left ≫ f := fun z ↦ by
    rw [hfdef, Over.comp_left]
  haveI : IsClosedImmersion i.left := hi
  haveI : LocallyOfFiniteType (fst T U).left := inferInstanceAs (LocallyOfFiniteType (pullback.fst T.hom U.hom))
  haveI : LocallyOfFiniteType f := by
    rw [hfdef, Over.comp_left]; infer_instance
  haveI : Mono f := ⟨fun {Z} z₁ z₂ he ↦ by
    let a₁ : Over.mk (z₁ ≫ G.hom) ⟶ G := Over.homMk z₁ rfl
    let a₂ : Over.mk (z₁ ≫ G.hom) ⟶ G := Over.homMk z₂ (by
      simp only [Over.mk_hom]; rw [← hf, reassoc_of% he])
    have e₁ : a₁ ≫ i ≫ fst T U = a₂ ≫ i ≫ fst T U := by
      ext1; rw [hfz, hfz]; exact he
    have h₁ := (key _ (a₁ ≫ i)).2 ⟨a₁, rfl⟩
    have h₂ := (key _ (a₂ ≫ i)).2 ⟨a₂, rfl⟩
    simp only [Category.assoc] at h₁ h₂
    rw [← e₁] at h₂
    have e₂ : a₁ ≫ i ≫ snd T U = a₂ ≫ i ≫ snd T U :=
      hInj _ _ _ (same_of_same_of_same hN.isLB hM.isLB h₁ h₂)
    have e₃ : a₁ ≫ i = a₂ ≫ i := CartesianMonoidalCategory.hom_ext _ _ (by simpa using e₁) (by simpa using e₂)
    have e₄ := congrArg (fun q ↦ q.left) e₃
    simp only [Over.comp_left] at e₄
    exact (cancel_mono i.left).1 e₄⟩
  have hyp : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B),
      I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ →
      ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ G.left) (b : Spec (CommRingCat.of B) ⟶ T.left),
        a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b →
        ∃ l : Spec (CommRingCat.of B) ⟶ G.left, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧
          l ≫ f = b := by
    intro B _ _ _ I hI hmI a b hab
    have ha : a ≫ G.hom = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b ≫ T.hom := by
      rw [← hf, reassoc_of% hab]
    let a' : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b ≫ T.hom) ⟶ G := Over.homMk a ha
    have hsame : Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b) (by simp) :
        Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b ≫ T.hom) ⟶ T) (a' ≫ i ≫ snd T U) := by
      have h₁ := (key _ (a' ≫ i)).2 ⟨a', rfl⟩
      have e : (a' ≫ i) ≫ fst T U = Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b) (by simp) := by
        ext1; rw [Category.assoc, hfz]; exact hab
      rw [e] at h₁
      simpa only [Category.assoc] using h₁
    obtain ⟨u, hu⟩ := hlift B I hI hmI b (a' ≫ i ≫ snd T U) hsame
    obtain ⟨z, hz⟩ := (key _ (lift (Over.homMk b rfl) u)).1 (by rwa [lift_fst, lift_snd])
    have hzf : z.left ≫ f = b := by
      rw [← hfz, ← Category.assoc, hz, lift_fst]; rfl
    refine ⟨z.left, ?_, hzf⟩
    rw [← cancel_mono f, Category.assoc, hzf, hab]
  haveI : IsOpenImmersion f := crit f hyp
  refine ⟨f.opensRange, fun Y y ↦ ⟨?_, fun hy ↦ ?_⟩⟩
  · rintro ⟨u, hu⟩ p
    obtain ⟨z, hz⟩ := (key Y (lift y u)).1 (by rwa [lift_fst, lift_snd])
    have e : z.left ≫ f = y.left := by rw [← hfz, ← Category.assoc, hz, lift_fst]
    rw [← e]
    exact ⟨z.left p, rfl⟩
  · have hr : Set.range y.left ⊆ Set.range f := by
      rintro _ ⟨p, rfl⟩
      simpa using hy p
    have hl : IsOpenImmersion.lift f y.left hr ≫ f = y.left := IsOpenImmersion.lift_fac f y.left hr
    let z : Y ⟶ G := Over.homMk (IsOpenImmersion.lift f y.left hr) (by rw [← hf, reassoc_of% hl, Over.w y])
    refine ⟨z ≫ i ≫ snd T U, ?_⟩
    have h₁ := (key Y (z ≫ i)).2 ⟨z, rfl⟩
    have e : (z ≫ i) ≫ fst T U = y := by
      ext1; rw [Category.assoc, hfz]; exact hl
    rwa [e, Category.assoc] at h₁

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyParamInjectiveOfGeomFiberInjecti
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualInj

theorem mono_of_points_tangents {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h₁ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y')
    (h₂ : ∀ (k : Type) [Field k] [IsAlgClosed k] (w : Sp (DualNumber k) ⟶ X),
      w ≫ f = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w ≫ f →
        w = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w) : Mono f := by
  have hu : FormallyUnramified f := TangentCrit.formallyUnramified_of_tangent f h₂
  have hs : Surjective (pullback.diagonal f) := by
    refine ((tfae_universallyInjective f).out 1 3).1 fun (k : Type) [Field k] y y' e => ?_
    let x : Sp (AlgebraicClosure k) ⟶ Sp k := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    have : Surjective x :=
      ⟨fun z => ⟨(default : PrimeSpectrum (AlgebraicClosure k)), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Epi x := Flat.epi_of_flat_of_surjective x
    refine (cancel_epi x).1 (h₁ _ _ _ ?_)
    rw [Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

variable {S : Scheme.{0}} {A U : Over S} [GrpObj A]

theorem fam_ev {M : LB (A ⊗ U).left} (hM : Fam A M) {T : Over S} (t : T ⟶ U) :
    Fam A (ev M (fst A T) (snd A T ≫ t)) where
  isLB := pull_isLB hM.isLB _
  add := (isAdditive_iff (pull_isLB hM.isLB _)).2 fun Y a a' y => by
    rw [evc_ev hM.isLB, evc_ev hM.isLB, evc_ev hM.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hM.isLB).1 hM.add Y a a' (y ≫ t)

omit [GrpObj A] in

theorem same_ev_iff {M M' : LB (A ⊗ U).left} (hM : M.IsLB) (hM' : M'.IsLB) {T Y : Over S} (t t' : T ⟶ U)
    (y : Y ⟶ T) :
    Same A (ev M (fst A T) (snd A T ≫ t)) (ev M' (fst A T) (snd A T ≫ t')) y y ↔ Same A M M' (y ≫ t) (y ≫ t') := by
  rw [same_iff (pull_isLB hM _) (pull_isLB hM' _), same_iff hM hM', evc_ev hM, evc_ev hM']
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

end GlobalTheory.DualInj

namespace GlobalTheory.DualInj

theorem inj_of_fibInj : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), LocallyOfFiniteType U.hom → Fam A M →
      FibInj A M → Inj A M := by
  intro R _ _ A _ hA U M hU hM hF
  have : LocallyOfFiniteType (U ⊗ U).hom := by
    show LocallyOfFiniteType (pullback.fst U.hom U.hom ≫ U.hom)
    infer_instance
  have : IsLocallyNoetherian (U ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (U ⊗ U).hom
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree (Sp R) A (U ⊗ U) hA
    (ev M (fst A (U ⊗ U)) (snd A (U ⊗ U) ≫ fst U U)) (ev M (fst A (U ⊗ U)) (snd A (U ⊗ U) ≫ snd U U))
    (fam_ev hM _) (fam_ev hM _)
  have key : ∀ (Y : Over (Sp R)) (y : Y ⟶ U ⊗ U),
      Same A M M (y ≫ fst U U) (y ≫ snd U U) ↔ ∃ z : Y ⟶ G, z ≫ i = y :=
    fun Y y => (same_ev_iff hM.isLB hM.isLB _ _ y).symm.trans (hG Y y)
  obtain ⟨δ, hδ⟩ := (key U (lift (𝟙 U) (𝟙 U))).1 (by
    rw [lift_fst, lift_snd]
    exact (same_iff hM.isLB hM.isLB _ _).2 rfl)
  let p : G.left ⟶ U.left := (i ≫ fst U U).left
  have hp : p ≫ U.hom = G.hom := Over.w (i ≫ fst U U)
  have : Mono i.left := inferInstance
  have pt : ∀ (Z : Scheme.{0}) (a b : Z ⟶ G.left) (K : Type) [Field K] [IsAlgClosed K] (t : Z ⟶ Sp K)
      (s : Sp K ⟶ Sp R), a ≫ p = b ≫ p → a ≫ G.hom = t ≫ s → a = b := by
    intro Z a b K _ _ t s e es
    let Y : Over (Sp R) := Over.mk (a ≫ G.hom)
    let α : Y ⟶ G := Over.homMk a rfl
    let β : Y ⟶ G := Over.homMk b (by
      show b ≫ G.hom = a ≫ G.hom
      rw [← hp, ← Category.assoc, ← e, Category.assoc])
    let τ : Y ⟶ Over.mk s := Over.homMk t es.symm
    have h1 : ∀ c0 : Y ⟶ G, c0 ≫ i ≫ fst U U = c0 ≫ i ≫ snd U U := fun c0 => by
      refine hF K s Y τ _ _ ?_
      have := (key Y (c0 ≫ i)).2 ⟨c0, rfl⟩
      simpa only [Category.assoc] using this
    have e1 : α ≫ i ≫ fst U U = β ≫ i ≫ fst U U := by
      refine Over.OverMorphism.ext ?_
      simpa only [Over.comp_left, Over.homMk_left, α, β, p] using e
    have e2 : α ≫ i = β ≫ i := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simpa only [Category.assoc] using e1
      · simpa only [Category.assoc, ← h1 α, ← h1 β] using e1
    have e3 := congrArg CommaMorphism.left e2
    simp only [Over.comp_left, Over.homMk_left, α, β] at e3
    exact (cancel_mono i.left).1 e3
  have : LocallyOfFiniteType p := by
    show LocallyOfFiniteType (i.left ≫ pullback.fst U.hom U.hom)
    infer_instance
  have hmono : Mono p := mono_of_points_tangents p
    (fun k _ _ y y' e => pt _ y y' k (𝟙 _) (y ≫ G.hom) e (Category.id_comp _).symm)
    (fun k _ _ w hw => pt _ w _ k (TangentCrit.dualBase k) (TangentCrit.dualPt k ≫ w ≫ G.hom) hw (by
      have := congrArg (· ≫ U.hom) hw
      simpa only [Category.assoc, hp] using this))
  intro Y u u' hs
  obtain ⟨z, hz⟩ := (key Y (lift u u')).1 (by rw [lift_fst, lift_snd]; exact hs)
  have hz1 : z ≫ i ≫ fst U U = u := by rw [← Category.assoc, hz, lift_fst]
  have hzδ : z = u ≫ δ := by
    refine Over.OverMorphism.ext ((cancel_mono p).1 ?_)
    have e1 : (z ≫ i ≫ fst U U).left = (u ≫ δ ≫ i ≫ fst U U).left := by
      rw [hz1, reassoc_of% hδ, lift_fst, Category.comp_id]
    simpa only [p, Over.comp_left, Category.assoc] using e1
  symm
  calc u' = lift u u' ≫ snd U U := (lift_snd _ _).symm
    _ = u ≫ δ ≫ i ≫ snd U U := by rw [← hz, hzδ]; simp only [Category.assoc]
    _ = u := by rw [reassoc_of% hδ, lift_snd, Category.comp_id]

end GlobalTheory.DualInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleRationalLocalUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.GlueRat

variable {S : Scheme.{0}} [IsIntegral S]

theorem genericPoint_mem' {U : S.Opens} {x : S} (hx : x ∈ U) : genericPoint S ∈ U :=
  ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

theorem unit_eq_of_germ {V : S.Opens} {a b : Γ(S, V)ˣ}
    (h : ∀ hg : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) hg (a : Γ(S, V)) =
      S.presheaf.germ V (genericPoint S) hg (b : Γ(S, V))) : a = b := by
  by_cases hg : genericPoint S ∈ V
  · exact Units.ext (germ_injective_of_isIntegral S (genericPoint S) hg (h hg))
  · exact unit_ext fun x hx => (hg (genericPoint_mem' hx)).elim

theorem germ_res_unit {U V : S.Opens} (hle : V ≤ U) (hg : genericPoint S ∈ V) (a : Γ(S, U)ˣ) :
    S.presheaf.germ V (genericPoint S) hg ((res hle a : Γ(S, V)ˣ) : Γ(S, V)) =
      S.presheaf.germ U (genericPoint S) (hle hg) (a : Γ(S, U)) :=
  S.presheaf.germ_res_apply (homOfLE hle) _ hg _

theorem exists_unit_of_local {W : S.Opens} (f : S.presheaf.stalk (genericPoint S))
    (H : ∀ x ∈ W, ∃ (V : S.Opens) (_ : V ≤ W) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f) :
    ∃ s : Γ(S, W)ˣ, ∀ h : genericPoint S ∈ W, S.presheaf.germ W (genericPoint S) h (s : Γ(S, W)) = f := by
  choose V hVW hxV u hu using fun x : W => H x.1 x.2
  obtain ⟨s, hs⟩ := glue_unit W V hVW (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV _⟩) u
    (fun i j z hz => by
      rw [← gm_res (𝟙 S) z (inf_le_left : V i ⊓ V j ≤ V i) hz,
        ← gm_res (𝟙 S) z (inf_le_right : V i ⊓ V j ≤ V j) hz]
      congr 1
      refine unit_eq_of_germ fun hg => ?_
      rw [germ_res_unit, germ_res_unit, hu i (hg.1), hu j hg.2])
  refine ⟨s, fun h => ?_⟩
  rw [← germ_res_unit (hVW ⟨_, h⟩) (hxV ⟨_, h⟩), hs]
  exact hu _ _

end GlobalTheory.GlueRat

open GlobalTheory.GlueRat in

theorem GlobalTheory.GlueRat.lbIso_of_rat : ∀ (S : Scheme.{0}) [IsIntegral S] (A B : LB S) (f : B.ι × A.ι → S.presheaf.stalk (genericPoint S)),
    (∀ p, ∀ x ∈ B.U p.1 ⊓ A.U p.2, ∃ (V : S.Opens) (_ : V ≤ B.U p.1 ⊓ A.U p.2) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f p) →
    (∀ p q (h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1) (h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2),
      f p * S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) =
        S.presheaf.germ _ (genericPoint S) h1 (B.g p.1 q.1 : Γ(S, B.U p.1 ⊓ B.U q.1)) * f q) →
    LBIso A B := by
  intro S _ A B f H1 H2
  choose s hs using fun p => exists_unit_of_local (f p) (H1 p)
  refine ⟨⟨s⟩, fun p q => unit_eq_of_germ fun hg => ?_⟩
  have hp : genericPoint S ∈ B.U p.1 ⊓ A.U p.2 := hg.1
  have hq : genericPoint S ∈ B.U q.1 ⊓ A.U q.2 := hg.2
  have h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1 := ⟨hg.1.1, hg.2.1⟩
  have h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2 := ⟨hg.1.2, hg.2.2⟩
  refine ((germ_res_unit _ hg _).trans (hs p hp)).trans ?_
  set O := (LB.div B A).U p ⊓ (LB.div B A).U q
  have lB : O ≤ B.U p.1 ⊓ B.U q.1 := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have lA : O ≤ A.U p.2 ⊓ A.U q.2 := le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have lq : O ≤ B.U q.1 ⊓ A.U q.2 := inf_le_right
  change f p = S.presheaf.germ O (genericPoint S) hg
    (((res lB (B.g p.1 q.1) * (res lA (A.g p.2 q.2))⁻¹ * res lq (s q) : Γ(S, O)ˣ)) : Γ(S, O))
  have e : S.presheaf.germ O (genericPoint S) hg (((res lA (A.g p.2 q.2))⁻¹ : Γ(S, O)ˣ) : Γ(S, O)) *
      S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) = 1 := by
    rw [← germ_res_unit lA hg, ← map_mul, Units.inv_mul, map_one]
  have H := H2 p q h1 h2
  simp only [Units.val_mul, map_mul, germ_res_unit, hs q hq]
  calc f p = f p * (S.presheaf.germ O (genericPoint S) hg (((res lA (A.g p.2 q.2))⁻¹ : Γ(S, O)ˣ) : Γ(S, O)) *
      S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2))) := by rw [e, _root_.mul_one]
    _ = _ := by rw [mul_comm (S.presheaf.germ O _ hg _), ← _root_.mul_assoc, H]; ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackFstSndOfAdditiveTrivialKern
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescIsoExists

theorem lbIso_pull_fst_snd : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → P.IsLB → IsAdditive P → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → LBIso (P.pull (pullback.fst (q ▷ B).left (q ▷ B).left)) (P.pull (pullback.snd (q ▷ B).left (q ▷ B).left)) := by
  intro K _ _ A A' B _ _ _ q P _ _ _ hq hP hadd hker
  let f := (q ▷ B).left
  have hw : f ≫ (A' ⊗ B).hom = (A ⊗ B).hom := Over.w (q ▷ B)
  let Z : Over (Sp K) := Over.mk (pullback.fst f f ≫ (A ⊗ B).hom)
  have hsnd : pullback.snd f f ≫ (A ⊗ B).hom = pullback.fst f f ≫ (A ⊗ B).hom := by
    rw [← hw, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hB : (q ▷ B) ≫ snd A' B = snd A B := whiskerRight_snd q B
  have hA : (q ▷ B) ≫ fst A' B = fst A B ≫ q := whiskerRight_fst q B
  have hBl : f ≫ (snd A' B).left = (snd A B).left := by rw [← Over.comp_left, hB]
  have hAl : f ≫ (fst A' B).left = (fst A B).left ≫ q.left := by
    rw [← Over.comp_left, hA, Over.comp_left]
  let a : Z ⟶ A := Over.homMk (pullback.fst f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let a' : Z ⟶ A := Over.homMk (pullback.snd f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w]; exact hsnd)
  let b : Z ⟶ B := Over.homMk (pullback.fst f f ≫ (snd A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let u : Z ⟶ A ⊗ B := Over.homMk (pullback.fst f f) rfl
  let u' : Z ⟶ A ⊗ B := Over.homMk (pullback.snd f f) hsnd
  have hu : lift a b = u := by
    ext1
    · ext; simp [a, u]
    · ext; simp [b, u]
  have hu' : lift a' b = u' := by
    ext1
    · ext; simp [a', u']
    · ext
      simp only [b, u', lift_snd, Over.homMk_left, Over.comp_left]
      rw [← hBl, ← Category.assoc, pullback.condition, Category.assoc]
  have hq' : a ≫ q = a' ≫ q := by
    ext
    simp only [a, a', Over.comp_left, Over.homMk_left, Category.assoc]
    rw [← hAl, ← Category.assoc, pullback.condition, Category.assoc]

  have e1 : (pullback.fst f f : pullback f f ⟶ _) = (lift a b).left := by rw [hu]; rfl
  have e2 : (pullback.snd f f : pullback f f ⟶ _) = (lift a' b).left := by rw [hu']; rfl
  refine (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).1 ?_
  have c1 : cls _ (pull_isLB hP (pullback.fst f f)) = evc hP a b := by
    rw [cls_pull hP]; simp only [evc]; rw [e1]
  have c2 : cls _ (pull_isLB hP (pullback.snd f f)) = evc hP a' b := by
    rw [cls_pull hP]; simp only [evc]; rw [e2]
  rw [c1, c2]
  let k : Z ⟶ A := a' * a⁻¹
  have hinv : a⁻¹ ≫ q = (a ≫ q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hk : k ≫ q = 1 := by
    simp only [k]
    rw [MonObj.mul_comp, hinv, ← hq', mul_inv_cancel]
  have h0 : evc hP k b = 0 := by
    have e := congrArg (CechPic.pull (lift (𝟙 Z) b).left) ((triv_ev_iff hP _ _).1 (hker Z k hk))
    rwa [pull_evc, map_zero, lift_fst_assoc, Category.id_comp, lift_snd] at e
  have ha : a' = k * a := by simp only [k, inv_mul_cancel_right]
  rw [ha, (isAdditive_iff hP).1 hadd, h0, zero_add]

end GlobalTheory.DescIsoExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairOfLambdaBundleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LamPull

theorem lbIso_pull_lift : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (M : LB A.left), P.IsLB → M.IsLB → LBIso P (cubeLB A ![fst A A, snd A A] M) → ∀ (T : Over (Sp ℂ)) (a b : T ⟶ A), LBIso (P.pull (lift a b).left) (cubeLB A ![a, b] M) := by
  intro A _ _ P M hP hM e T a b
  have hc : ∀ {T' : Over (Sp ℂ)} (x : Fin 2 → (T' ⟶ A)), (cubeLB A x M).IsLB := fun x => by
    unfold cubeLB; exact LB.isLB_linComb hM _ _
  have h₁ : LBIso (P.pull (lift a b).left) ((cubeLB A ![fst A A, snd A A] M).pull (lift a b).left) :=
    GlobalTheory.GenSpread.lbIso_pullback e _
  have h₂ : LBIso ((cubeLB A ![fst A A, snd A A] M).pull (lift a b).left) (cubeLB A ![a, b] M) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
      (GlobalTheory.PrimNorm.chartSquare M (lift a b) (lift_fst a b).symm (lift_snd a b).symm) (GlobalTheory.lbIso_refl (hc _))
  exact LBIso.trans (pull_isLB hP _) (pull_isLB (hc _) _) (hc _) h₁ h₂

end GlobalTheory.LamPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLocalSectionFamilyUnitAtFinitePoints
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem isUnit_add_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {u m : R}
    (hu : IsUnit u) (hm : ¬ IsUnit m) : IsUnit (u + m) := by
  by_contra h
  have h1 : u + m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hm
  have h3 : u ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ h1 h2
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 hu

theorem secFam_unit_at_finite : ∀ (X : Scheme.{0}) (L : LB X) (W : X.Opens) (J : Type) (D : J → X.Opens), (∀ j, D j ≤ W) → ∀ (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (F : Set X), F.Finite → ∀ (a : X → Γ(X, W)), (∀ x ∈ F, x ∈ X.basicOpen (a x)) → (∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x)) → ∀ (E : X → ∀ j, Γ(X, D j)), (∀ x ∈ F, GlobalTheory.Pinch.IsSecFam L D k hD (E x)) → (∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (E x j))) → ∃ e : ∀ j, Γ(X, D j), GlobalTheory.Pinch.IsSecFam L D k hD e ∧ ∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) := by
  intro X L W J D hDW k hD F hF a ha hsep E hE hEu
  classical
  let r : ∀ j, Γ(X, W) →+* Γ(X, D j) := fun j => (X.presheaf.map (homOfLE (hDW j)).op).hom
  refine ⟨fun j => ∑ x ∈ hF.toFinset, r j (a x) * E x j, ?_, ?_⟩
  ·
    have hr : ∀ j z (hz : z ∈ D j) (s : Γ(X, W)),
        (X.presheaf.germ (D j) z hz).hom (r j s) = (X.presheaf.germ W z (hDW j hz)).hom s := by
      intro j z hz s
      exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hDW j)) z hz s
    intro j j' z hz hz'
    simp only [map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hr, hr, hE x (hF.mem_toFinset.mp hx) j j' z hz hz']
    ring
  · intro y hy j hyj
    have hyW : y ∈ W := hDW j hyj
    have hyF : y ∈ hF.toFinset := hF.mem_toFinset.mpr hy
    simp only [map_sum, map_mul]
    rw [← Finset.add_sum_erase _ _ hyF]
    have hr : ∀ s : Γ(X, W),
        (X.presheaf.germ (D j) y hyj).hom (r j s) = (X.presheaf.germ W y hyW).hom s :=
      fun s => TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hDW j)) y hyj s
    apply isUnit_add_of_not_isUnit
    · rw [hr]
      exact ((X.mem_basicOpen (a y) y hyW).mp (ha y hy)).mul (hEu y hy j hyj)
    · intro hu
      have hmem : ∑ x ∈ hF.toFinset.erase y,
          (X.presheaf.germ (D j) y hyj).hom (r j (a x)) * (X.presheaf.germ (D j) y hyj).hom (E x j)
            ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        refine Ideal.sum_mem _ fun x hx => ?_
        have hxy : x ≠ y := (Finset.mem_erase.mp hx).1
        have hxF : x ∈ F := hF.mem_toFinset.mp (Finset.mem_erase.mp hx).2
        refine Ideal.mul_mem_right _ _ ?_
        rw [hr, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu'
        exact hsep x hxF y hy (Ne.symm hxy) ((X.mem_basicOpen (a x) y hyW).mpr hu')
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbedsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearlyDisjoint_of_flat_baseChange_embeds : ∀ (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L), (∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) → LinDisj (algebraMap R K) c θ := by
  first | exact @GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat | exact GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat | (intros; apply GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat <;> assumption)
end

