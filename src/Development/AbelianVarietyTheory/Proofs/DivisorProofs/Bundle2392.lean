import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoFiniteTypeAgreementLocusInjectiveFamil
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualGraph

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem evc_ev_comp {T P Y : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (f : P ⟶ T)
    (h : (ev N (fst A P) (snd A P ≫ f)).IsLB) (a : Y ⟶ A) (p : Y ⟶ P) : evc h a p = evc hN a (p ≫ f) := by
  rw [evc_ev hN, lift_fst, lift_snd_assoc]

theorem fam_ev {T P : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (f : P ⟶ T) :
    Fam A (ev N (fst A P) (snd A P ≫ f)) := by
  have h : (ev N (fst A P) (snd A P ≫ f)).IsLB := pull_isLB hN.isLB _
  refine ⟨h, (isAdditive_iff h).2 fun Y a a' p ↦ ?_⟩
  rw [evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h]
  exact (isAdditive_iff hN.isLB).1 hN.add Y a a' (p ≫ f)

theorem same_prod_iff {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (p : Y ⟶ T ⊗ U) :
    Same A (ev N (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ fst T U)) (ev M (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ snd T U)) p p ↔
      Same A N M (p ≫ fst T U) (p ≫ snd T U) := by
  have h₁ : (ev N (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ fst T U)).IsLB := pull_isLB hN _
  have h₂ : (ev M (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ snd T U)).IsLB := pull_isLB hM _
  rw [same_iff h₁ h₂, same_iff hN hM, evc_ev_comp hN _ h₁, evc_ev_comp hM _ h₂, Category.assoc, Category.assoc]

theorem exists_mono_same : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (T U : Over S) [IsLocallyNoetherian T.left] [LocallyOfFiniteType U.hom] (N : LB (A ⊗ T).left)
      (M : LB (A ⊗ U).left), Fam A N → Fam A M → Inj A M → ∃ (G : Over S) (π : G ⟶ T), Mono π.left ∧
        LocallyOfFiniteType π.left ∧ ∀ (Y : Over S) (y : Y ⟶ T),
          (∃ u : Y ⟶ U, Same A N M y u) ↔ ∃ z : Y.left ⟶ G.left, z ≫ π.left = y.left := by
  intro S A _ hA T U _ _ N M hN hM hI
  have hf : LocallyOfFiniteType (fst T U).left := by
    show LocallyOfFiniteType (pullback.fst T.hom U.hom)
    infer_instance
  haveI : IsLocallyNoetherian (T ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (fst T U).left
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.DualLocus.exists_closed_same S A (T ⊗ U) hA _ _ (fam_ev hN (fst T U))
    (fam_ev hM (snd T U))
  have key : ∀ (Y : Over S) (z : Y ⟶ G), Same A N M (z ≫ i ≫ fst T U) (z ≫ i ≫ snd T U) := fun Y z ↦ by
    rw [← Category.assoc, ← Category.assoc, ← same_prod_iff hN.isLB hM.isLB]
    exact (hG Y (z ≫ i)).2 ⟨z, rfl⟩
  have hw : i.left ≫ (fst T U).left ≫ T.hom = G.hom := by
    rw [Over.w (fst T U), Over.w i]
  refine ⟨G, i ≫ fst T U, ⟨fun {W} a b hab ↦ ?_⟩, ?_, fun Y y ↦ ⟨?_, ?_⟩⟩
  · let Y : Over S := Over.mk (a ≫ G.hom)
    let a' : Y ⟶ G := Over.homMk a rfl
    let b' : Y ⟶ G := Over.homMk b (by
      show b ≫ G.hom = a ≫ G.hom
      simp only [Over.comp_left] at hab
      rw [← hw, reassoc_of% hab])
    have e₁ : a' ≫ i ≫ fst T U = b' ≫ i ≫ fst T U := Over.OverMorphism.ext (by
      simpa only [Over.comp_left, a', b', Over.homMk_left] using hab)
    have e₂ : a' ≫ i ≫ snd T U = b' ≫ i ≫ snd T U := by
      refine hI Y _ _ ((same_iff hM.isLB hM.isLB _ _).2 ?_)
      rw [← (same_iff hN.isLB hM.isLB _ _).1 (key Y a'), ← (same_iff hN.isLB hM.isLB _ _).1 (key Y b'), e₁]
    have e : a' ≫ i = b' ≫ i := by
      rw [← Category.assoc, ← Category.assoc] at e₁ e₂
      exact CartesianMonoidalCategory.hom_ext _ _ e₁ e₂
    have e' := congrArg (fun q : Y ⟶ T ⊗ U ↦ q.left) e
    simp only [Over.comp_left, a', b', Over.homMk_left] at e'
    exact (cancel_mono i.left).1 e'
  · rw [Over.comp_left]
    infer_instance
  · rintro ⟨u, hu⟩
    have hs := (same_prod_iff hN.isLB hM.isLB (lift y u)).2 (by rwa [lift_fst, lift_snd])
    obtain ⟨z, hz⟩ := (hG Y (lift y u)).1 hs
    refine ⟨z.left, ?_⟩
    rw [← Over.comp_left, ← Category.assoc, hz, lift_fst]
  · rintro ⟨z, hz⟩
    let z' : Y ⟶ G := Over.homMk z (by
      show z ≫ G.hom = Y.hom
      rw [← hw, ← Over.w y, ← hz, Over.comp_left]
      simp only [Category.assoc])
    have ey : z' ≫ i ≫ fst T U = y := Over.OverMorphism.ext (by
      simpa only [Over.comp_left, z', Over.homMk_left] using hz)
    refine ⟨z' ≫ i ≫ snd T U, ?_⟩
    have := key Y z'
    rwa [ey] at this

end GlobalTheory.DualGraph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHom
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LiftSys.Glue

open Opposite Limits

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_surjective {A B : Type} [CommRing A] [CommRing B] (q : A →+* B)
    (hq : Function.Surjective q) (hn : ∀ a, q a = 0 → a * a = 0) : Function.Surjective (spMap q) := by
  intro p
  have hker : RingHom.ker q ≤ p.asIdeal := by
    intro x hx
    have hx2 := hn x (RingHom.mem_ker.1 hx)
    exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
  haveI := p.isPrime
  haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
  rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
  intro x hx
  exact hker (by simpa [RingHom.mem_ker] using hx)

theorem exists_affine {X₀ : Scheme.{0}} {x : X₀} {U : X₀.Opens} (hx : x ∈ U) :
    ∃ W : X₀.affineOpens, x ∈ W.1 ∧ W.1 ≤ U := by
  obtain ⟨W, hW, hxW, hWU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₀.isBasis_affineOpens) hx
  exact ⟨⟨W, hW⟩, hxW, hWU⟩

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

abbrev cov {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x) :
    X.OpenCover where
  I₀ := X₀.affineOpens
  X U := Sp (S.F.obj (op U))
  f U := h.y (op U)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x ↦ by obtain ⟨U, z, hz⟩ := hc x; exact ⟨U, z, hz⟩, fun U ↦ h.isOpen _⟩

def dir {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x)
    (hd : ∀ (U V : X₀.affineOpens) (a : Sp (S.F.obj (op U))) (b : Sp (S.F.obj (op V))),
      h.y (op U) a = h.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S.F.obj (op W))), h.y (op W) c = h.y (op U) a) :
    (cov h hc).LocallyDirected where
  trans {U V} a := spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U))
  trans_id U := by
    haveI := h.isOpen (op U)
    rw [← cancel_mono (h.y (op U))]
    exact (h.nat _).trans (Category.id_comp _).symm
  trans_comp {U V W} a b := by
    haveI := h.isOpen (op W)
    rw [← cancel_mono (h.y (op W))]
    rw [Category.assoc, h.nat, h.nat, h.nat]
  w {U V} a := h.nat a.op
  directed {U V} x := by
    haveI := h.isOpen (op U)
    haveI := h.isOpen (op V)
    obtain ⟨W, hWU, hWV, c, hcW⟩ := hd U V (pullback.fst (h.y (op U)) (h.y (op V)) x)
      (pullback.snd (h.y (op U)) (h.y (op V)) x)
      (by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply])
    refine ⟨W, homOfLE hWU, homOfLE hWV, c, ?_⟩
    apply (pullback.fst (h.y (op U)) (h.y (op V)) ≫ h.y (op U)).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change (spMap _ ≫ h.y (op U)) c = _
    rw [h.nat, hcW, Scheme.Hom.comp_apply]
  property_trans {U V} a := by
    haveI := h.isOpen (op V)
    haveI : IsOpenImmersion (spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) ≫ h.y (op V)) := by
      rw [h.nat]; exact h.isOpen _
    exact IsOpenImmersion.of_comp _ (h.y (op V))

theorem presents_hom : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (Y : Scheme.{0}) (t : Y ⟶ Sp R) (j : X₀ ⟶ Y), IsPullback i s₀ s (spMap π) → S.Presents t j → S'.Presents s i → (∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b)) → ∃ f : X ⟶ Y, f ≫ t = s ∧ i ≫ f = j := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' X s i Y t j hpb hY hX hψ
  obtain ⟨ψ, hψp, hψn⟩ := hψ

  have hsurU : ∀ U, Function.Surjective (spMap (S'.p U)) := fun U ↦
    spMap_surjective _ (S'.surj U) fun b hb ↦ by
      have hb' := (S'.ker U b).1 hb
      have : b * b ∈ (I.map (algebraMap R (S'.F.obj U))) ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
      rwa [map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hπs : Function.Surjective (spMap π) := spMap_surjective π hπ fun a ha ↦ by
    have ha' : a ∈ I := hk ▸ RingHom.mem_ker.2 ha
    have : a * a ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha' ha'
    rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this

  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI hic : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip inferInstance
  have hinj : Function.Injective i := i.isClosedEmbedding.injective
  have hisurj : Function.Surjective i :=
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hpb.flip ⟨hπs⟩).surj

  have hrng : ∀ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), ∃ x₀ ∈ U.1, hX.y (op U) z = i x₀ := by
    intro U z
    obtain ⟨w, rfl⟩ := hsurU (op U) z
    refine ⟨affPt s₀ U w, U.2.range_fromSpec.le ⟨w, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hX.red (op U), Scheme.Hom.comp_apply]
  have hcov : ∀ (U : X₀.affineOpens) (x₀ : X₀), x₀ ∈ U.1 → ∃ z : Sp (S'.F.obj (op U)), hX.y (op U) z = i x₀ := by
    intro U x₀ hx
    obtain ⟨w, hw⟩ : x₀ ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hx
    refine ⟨spMap (S'.p (op U)) w, ?_⟩
    change (spMap (S'.p (op U)) ≫ hX.y (op U)) w = i x₀
    rw [hX.red (op U), Scheme.Hom.comp_apply]
    exact congrArg i hw
  have hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), hX.y (op U) z = x := by
    intro x
    obtain ⟨x₀, rfl⟩ := hisurj x
    obtain ⟨U, hxU, -⟩ := exists_affine (show x₀ ∈ (⊤ : X₀.Opens) from trivial)
    obtain ⟨z, hz⟩ := hcov U x₀ hxU
    exact ⟨U, z, hz⟩
  have hd : ∀ (U V : X₀.affineOpens) (a : Sp (S'.F.obj (op U))) (b : Sp (S'.F.obj (op V))),
      hX.y (op U) a = hX.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S'.F.obj (op W))), hX.y (op W) c = hX.y (op U) a := by
    intro U V a b hab
    obtain ⟨x₀, hxU, ha⟩ := hrng U a
    obtain ⟨x₁, hxV, hb⟩ := hrng V b
    have e : x₀ = x₁ := hinj (ha.symm.trans (hab.trans hb))
    subst e
    obtain ⟨W, hxW, hWle⟩ := exists_affine (show x₀ ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
    obtain ⟨c, hc'⟩ := hcov W x₀ hxW
    exact ⟨W, le_inf_iff.1 hWle |>.1, le_inf_iff.1 hWle |>.2, c, hc'.trans ha.symm⟩
  letI := dir hX hc hd
  let 𝒰 := cov hX hc
  let g : ∀ U : 𝒰.I₀, 𝒰.X U ⟶ Y := fun U ↦
    spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)
  have hg : ∀ {U V : 𝒰.I₀} (a : U ⟶ V), 𝒰.trans a ≫ g V = g U := by
    intro U V a
    change spMap (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)) ≫
      spMap (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) ≫ hY.y (op V) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)).comp
        (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) =
        (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)).comp
          (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) :=
      RingHom.ext fun b ↦ hψn (op V) (op U) a.op b
    rw [e, spMap_comp₂, Category.assoc, hY.nat a.op]
  refine ⟨𝒰.glueMorphismsOfLocallyDirected g hg, 𝒰.hom_ext _ _ fun U ↦ ?_, ?_⟩
  · rw [𝒰.map_glueMorphismsOfLocallyDirected_assoc g hg U]
    change (spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)) ≫ t = hX.y (op U) ≫ s
    rw [Category.assoc, hY.base, hX.base, ← spMap_comp₂]
    exact congrArg spMap (RingHom.ext fun r ↦ (ψ (op U)).commutes r)
  · let 𝒱 : X₀.OpenCover := Scheme.Cover.mkOfCovers X₀.affineOpens (fun U ↦ Sp (Sec s₀ U.1))
      (fun U ↦ affPt s₀ U)
      (fun x ↦ by
        obtain ⟨U, hxU, -⟩ := exists_affine (show x ∈ (⊤ : X₀.Opens) from trivial)
        obtain ⟨w, hw⟩ : x ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hxU
        exact ⟨U, w, hw⟩)
      (fun U ↦ IsAffineOpen.isOpenImmersion_fromSpec U.2)
    refine 𝒱.hom_ext _ _ fun U ↦ ?_
    change affPt s₀ U ≫ i ≫ _ = affPt s₀ U ≫ j
    rw [← Category.assoc, show affPt s₀ U ≫ i = _ from (hX.red (op U)).symm,
      show affPt s₀ U ≫ j = _ from (hY.red (op U)).symm, Category.assoc]
    change spMap (S'.p (op U)) ≫ 𝒰.f U ≫ _ = _
    rw [𝒰.map_glueMorphismsOfLocallyDirected g hg U]
    change spMap (S'.p (op U)) ≫ spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U) = _
    rw [← Category.assoc, ← spMap_comp₂]
    exact congrArg (· ≫ hY.y (op U)) (congrArg spMap (RingHom.ext fun b ↦ hψp (op U) b))

end GlobalTheory.LiftSys.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarised
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.NormIso

theorem prod_zpow_eq_one {K U : Type} [Fintype K] [CommGroup U] (ε : K → ℤ) (hε : ∑ k, ε k = 0) (c : U) :
    ∏ k, c ^ ε k = 1 := by
  have h : ∀ s : Finset K, ∏ k ∈ s, c ^ ε k = c ^ (∑ k ∈ s, ε k) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  rw [h, hε, zpow_zero]

theorem gm_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (ε : K → ℤ) (hε : ∑ k, ε k = 0)
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a a' : M.ι)
    (ha : r y ∈ LB.wchart M φ (fun _ => a)) (ha' : r y ∈ LB.wchart M φ (fun _ => a')) :
    gm r y (LB.wchart M φ (fun _ => a) ⊓ LB.wchart M φ (fun _ => a'))
      ((LB.LinComb M φ ε).g (fun _ => a) (fun _ => a')) = 1 :=
  (gm_linComb M φ ε r y _ _ ha ha').trans ((Finset.prod_congr rfl fun k _ => by rw [hq k]).trans
    (prod_zpow_eq_one ε hε (gm q y (M.U a ⊓ M.U a') (M.g a a'))))

theorem mem_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B))
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a : M.ι) (ha : q y ∈ M.U a) :
    r y ∈ LB.wchart M φ (fun _ => a) :=
  Set.mem_iInter.2 fun k => show (r ≫ φ k) y ∈ M.U a by rw [hq k]; exact ha

theorem exists_normalised {S X X' B B' : Scheme.{0}} (M : LB B) (M' : LB B') (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (φ' : K → (X' ⟶ B')) (ε : K → ℤ) (hε : ∑ k, ε k = 0) (F : X' ⟶ X)
    (e : S ⟶ X') (π : X' ⟶ S) (he : e ≫ π = 𝟙 S) (q : S ⟶ B) (q' : S ⟶ B') (hq : ∀ k, (e ≫ F) ≫ φ k = q)
    (hq' : ∀ k, e ≫ φ' k = q') (w₀ : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (z : Z) (a : M.ι) (b : M'.ι), q (t z) ∈ M.U a → q' (t z) ∈ M'.U b →
        gw w (t ≫ e) z (fun _ => a) (fun _ => b) = 1 := by
  let C : M.ι × M'.ι → X'.Opens := fun i =>
    ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)
  have mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b) := fun x a b ha hb =>
    ⟨mem_pull.2 (mem_const M φ (e ≫ F) q hq x a ha), mem_const M' φ' e q' hq' x b hb⟩
  obtain ⟨u, hu⟩ := glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hM (q x)
      obtain ⟨b, hb⟩ := exists_chart hM' (q' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)
    (fun i => pullU e (C i) (w₀.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by
      have hi : e x ∈ C i := hx.1
      have hj : e x ∈ C j := hx.2
      refine (gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)
      rw [Category.id_comp]
      have h := (isGen_iff w₀).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2)
        (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
      refine h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹)
        (gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1))
        (gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))
  let c : Γ(X', ⊤)ˣ := res (fun _ _ => trivial : (⊤ : X'.Opens) ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ u⁻¹)
  refine ⟨DVR.scaleGen c w₀, DVR.scaleGen_isGen c w₀ hw, fun Z t z a b ha hb => ?_⟩
  have hm : e (t z) ∈ C (a, b) := mem (t z) a b ha hb
  have h₁ : gm (t ≫ e) z (C (a, b)) (res le_top c) = (gm t z ⊤ u)⁻¹ := by
    refine (gm_res (t ≫ e) z le_top hm c).trans ((gm_res (t ≫ e) z (V := ⊤) _ trivial _).trans
      ((gm_pull (t ≫ e) π z ⊤ trivial _).trans ?_))
    rw [Category.assoc, he, Category.comp_id, map_inv]
  have h₂ : gm (t ≫ e) z (C (a, b)) (w₀.s (fun _ _ => a, fun _ => b)) = gm t z ⊤ u :=
    (gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans
      (gm_res t z le_top hm u))
  exact (map_mul (gm (t ≫ e) z (C (a, b))) _ _).trans ((congrArg₂ (· * ·) h₁ h₂).trans (inv_mul_cancel _))

theorem lift_one_psum {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (I : Finset (Fin 2)) :
    lift (1 : T ⟶ G) 1 ≫ psum G (x2 G) I = 1 := by
  have h : (fun k => lift (1 : T ⟶ G) 1 ≫ x2 G k) = fun _ => 1 := by
    funext k
    fin_cases k
    · exact lift_fst _ _
    · exact lift_snd _ _
  rw [comp_psum, h, psum_one]

theorem origin_square {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {β : G'.left ⟶ G.left} {β₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (T : Over S') :
    (lift (1 : T ⟶ G') 1).left ≫ β₂ = (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left := by
  have h₁ : (1 : T ⟶ G').left ≫ β = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h T))
  have a₁ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.1, ← Category.assoc, ← Over.comp_left, lift_fst, h₁]
  have a₂ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.2, ← Category.assoc, ← Over.comp_left, lift_snd, h₁]
  have b₁ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_fst (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  have b₂ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_snd (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  exact pullback.hom_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)

theorem exists_lamVal_origin {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} {β₂ : (G2 G').left ⟶ (G2 G).left} {M : LB G.left}
    {M' : LB G'.left} (hM : M.IsLB) (hM' : M'.IsLB) (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (H : LBIso (abelian₂ G' M') ((abelian₂ G M).pull β₂)) :
    ∃ w : LB.Iso (abelian₂ G' M') ((abelian₂ G M).pull β₂), w.IsGen ∧ ∀ (T : Over S') z J J', Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J J' = 1 := by
  obtain ⟨w₀, hw₀⟩ := H
  let e : (𝟙_ (Over S')).left ⟶ (G2 G').left := (lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
  let q : (𝟙_ (Over S')).left ⟶ G.left := (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left
  let q' : (𝟙_ (Over S')).left ⟶ G'.left := (1 : 𝟙_ (Over S') ⟶ G').left
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum G (x2 G) I.down).left = q := fun I =>
    (congrArg (· ≫ (psum G (x2 G) I.down).left) (origin_square h hs (𝟙_ (Over S')))).trans
      (congrArg (fun z => z.left) (lift_one_psum G (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) I.down))
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum G' (x2 G') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (lift_one_psum G' (T := 𝟙_ (Over S')) I.down)
  obtain ⟨w, hw, hv⟩ := exists_normalised M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum G (x2 G) I.down).left) (fun I => (psum G' (x2 G') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e (toUnit (G2 G')).left
    (congrArg (fun z => z.left) (toUnit_unique (lift (1 : 𝟙_ (Over S') ⟶ G') 1 ≫ toUnit (G2 G')) (𝟙 _))) q q' hq hq'
    w₀ hw₀
  refine ⟨w, hw, fun T z J J' hJ hJ' => ?_⟩
  have hp : (lift (1 : T ⟶ G') (1 : T ⟶ G')).left = (toUnit T).left ≫ e := by
    show _ = (toUnit T ≫ lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
    rw [comp_lift, MonObj.comp_one]
  have key : ∀ (p : T.left ⟶ (G2 G').left) (j : (abelian₂ G M).ι) (k : (abelian₂ G' M').ι),
      (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum G (x2 G) I.down).left)) = j →
      (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum G' (x2 G') I.down).left)) = k →
      lamVal w p z J J' = gw (L := abelian₂ G M) (L' := abelian₂ G' M') w p z j k := by
    rintro p _ _ rfl rfl
    rfl
  rw [hp]
  refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
    (funext fun I => ?_)).trans (hv T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
  · rw [← hq I, Category.assoc, Category.assoc]
  · rw [← hq' I, Category.assoc]

theorem exists_normalised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → letI := P.isAb.comm; ∃ w : LB.Iso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂), w.IsGen ∧ ∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good P.L z J' → lamVal w (lift (1 : T ⟶ P.A) (1 : T ⟶ P.A)).left z J J' = 1 :=
  fun _ _ _ _ _ _ Q _ P _ _ hpb hs H =>
    letI := P.isAb.comm
    exists_lamVal_origin Q.M.isLB P.isLB hpb hs H

end GlobalTheory.PolDeg.NormIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMvPolynomialLiftConductorCoeffs
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mvPolynomial_lift_of_mem_conductor :
    ∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G := by
  intro R R' ν _ _ _ c hc G hG
  have key : ∀ z ∈ c.map (algebraMap R R'), ∃ y ∈ c, algebraMap R R' y = z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => ∃ y ∈ c, algebraMap R R' y = z)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · exact ⟨0, c.zero_mem, map_zero _⟩
    · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, c.add_mem ha hb, map_add _ _ _⟩
    · rintro r _ _ ⟨a, ha, rfl⟩
      obtain ⟨y, hy, h⟩ := hc a ha r
      exact ⟨y, hy, by rw [h, smul_eq_mul, mul_comm]⟩
  rw [MvPolynomial.mem_map_C_iff] at hG
  choose y hy hyG using fun m => key _ (hG m)
  refine ⟨∑ m ∈ G.support, MvPolynomial.monomial m (y m), ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [MvPolynomial.map_monomial, Ideal.Quotient.eq_zero_iff_mem.mpr (hy m), map_zero]
  · rw [map_sum]
    conv_rhs => rw [G.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.map_monomial, hyG]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAddingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ KltAt p n (Δ + D) x → ∃ z, z ⤳ x ∧ IsNkltCentre p n (Δ + D) z := by
  first | exact @GlobalTheory.PairStep.Centre.exists_isNkltCentre | exact GlobalTheory.PairStep.Centre.exists_isNkltCentre | (intros; apply GlobalTheory.PairStep.Centre.exists_isNkltCentre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionNearOfFlatTrivialStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nowhereZero_section_near_of_flat_trivial : ∀ (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] (g : B →+* C), g.Flat → ∀ (W : (Sp B).Opens), Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : spMap g ⁻¹ᵁ W ≤ ⊤)).op).hom → ∀ (M : LB W.toScheme), M.IsLB → Triv (M.pull (spMap g ∣_ W)) → ∀ y : Sp C, ∃ (s : M.Sec) (D : (Sp C).Opens), y ∈ D ∧ ∀ z : (spMap g ⁻¹ᵁ W).toScheme, (spMap g ⁻¹ᵁ W).ι z ∈ D → (spMap g ∣_ W) z ∈ Out.nonzeroLocus s := by
  first | exact @GlobalTheory.FlatTrivSec.exists_sec_near | exact GlobalTheory.FlatTrivSec.exists_sec_near | (intros; apply GlobalTheory.FlatTrivSec.exists_sec_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushSectionsCanonicalModificationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_push_sections_canonical_modification : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p] (U : Y.Opens) (M : Modif p U d) (K : CanonLB p d) (K' : CanonLB M.str d) (B : LB Y), IsProjOver p → (U : Set Y).Nonempty → B.IsLB → ∃ Ψ : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤ → H0 p (tens K.bundle B) ⊤, ∀ (z : Sp ℂ ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.opn → ∀ (k' : (tens K'.bundle (B.pull M.σ)).ι) (hk' : ⊤ ≤ z ⁻¹ᵁ (tens K'.bundle (B.pull M.σ)).U k') (k : (tens K.bundle B).ι) (hk : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U k), ∃ lam : ℂˣ, ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) = lam * H0.val z k' le_top hk' g := by
  first | exact @GlobalTheory.ModifCanon.exists_push_sections | exact GlobalTheory.ModifCanon.exists_push_sections | (intros; apply GlobalTheory.ModifCanon.exists_push_sections <;> assumption)
end

