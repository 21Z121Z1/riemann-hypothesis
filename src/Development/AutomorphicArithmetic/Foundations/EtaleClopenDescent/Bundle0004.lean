import Mathlib
import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.LeafShMapZeroOf
import Development.EtaleCohomology.EtaleSheaves.Bundle0074

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FreeEtaleSheafLiftExists
section
open CategoryTheory Limits

namespace UpperTheory.Cb.HomologyEvaluation

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem comp_reassoc_six {D : Type*} [Category D] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : D} (f₁ : A₀ ⟶ A₁)
    (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (f₄ : A₃ ⟶ A₄) (f₅ : A₄ ⟶ A₅) (f₆ : A₅ ⟶ A₆) :
    ((f₁ ≫ f₂ ≫ f₃ ≫ f₄) ≫ f₅) ≫ f₆ = (f₁ ≫ f₂) ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ := by
  simp

private theorem single_homologyMap (L : CochainComplex C ℤ) (X : C) (c : X ⟶ L.cycles 0) :
    ∃ φ : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X ⟶ L,
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        HomologicalComplex.homologyMap φ 0 = c ≫ L.homologyπ 0 := by
  refine ⟨HomologicalComplex.mkHomFromSingle (c ≫ L.iCycles 0) (fun k _ => by simp), ?_⟩
  have h1 : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).homologyπ 0 := by
    rw [← cancel_mono (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom]
    simp
  rw [h1, Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles 0)]
  simp

private theorem exists_cycles (K : DerivedCategory C) :
    ∃ (Z : C) (π : Z ⟶ (DerivedCategory.homologyFunctor C 0).obj K), Epi π ∧
      ∀ (X : C) (c : X ⟶ Z), ∃ x : (DerivedCategory.singleFunctor C 0).obj X ⟶ K,
        (DerivedCategory.homologyFunctor C 0).map x =
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X ≫ c ≫ π := by
  obtain ⟨L, ⟨e⟩⟩ : ∃ L, Nonempty (DerivedCategory.Q.obj L ≅ K) :=
    ⟨_, ⟨(DerivedCategory.Q (C := C)).objObjPreimageIso K⟩⟩
  refine ⟨L.cycles 0, L.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
    (DerivedCategory.homologyFunctor C 0).map e.hom, ?_, fun X c => ?_⟩
  · have i0 : Epi (L.homologyπ 0) := inferInstance
    have i1 : IsIso ((DerivedCategory.homologyFunctorFactors C 0).inv.app L) :=
      inferInstanceAs (IsIso ((DerivedCategory.homologyFunctorFactors C 0).app L).inv)
    have i2 : Epi ((DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
        (DerivedCategory.homologyFunctor C 0).map e.hom) := epi_comp _ _
    exact @epi_comp _ _ _ _ _ _ i0 _ i2
  obtain ⟨φ, hφ⟩ := single_homologyMap L X c
  refine ⟨(DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫ DerivedCategory.Q.map φ ≫ e.hom, ?_⟩
  have h2 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X =
      (DerivedCategory.homologyFunctor C 0).map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X) ≫
      (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom := by
    have h3 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X =
        (DerivedCategory.homologyFunctor C 0).map (((DerivedCategory.singleFunctorsPostcompQIso C).hom.hom 0).app X) ≫
        𝟙 _ ≫ (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom := rfl
    have hm : (DerivedCategory.homologyFunctor C 0).map (NatTrans.app (𝟙 ((DerivedCategory.singleFunctors C).functor 0)) X) =
        (DerivedCategory.homologyFunctor C 0).map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X) := rfl
    rw [h3, DerivedCategory.singleFunctorsPostcompQIso_hom_hom]
    erw [Category.id_comp]
    exact congrArg (fun t => t ≫ (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom) hm
  rw [h2, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  have hφ' : HomologicalComplex.homologyMap φ 0 =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom ≫ c ≫ L.homologyπ 0 := by
    rw [← hφ, Iso.hom_inv_id_assoc]
  have n' : (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map φ) =
      ((DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫ HomologicalComplex.homologyMap φ 0) ≫
        (DerivedCategory.homologyFunctorFactors C 0).inv.app L :=
    (Iso.eq_comp_inv ((DerivedCategory.homologyFunctorFactors C 0).app L)).2
      (DerivedCategory.homologyFunctorFactors_hom_naturality φ 0)
  have key : (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map φ) ≫
      (DerivedCategory.homologyFunctor C 0).map e.hom =
      ((DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom) ≫ c ≫
        L.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
          (DerivedCategory.homologyFunctor C 0).map e.hom := by
    rw [n', hφ']
    exact comp_reassoc_six _ _ _ _ _ _
  exact key

end UpperTheory.Cb.HomologyEvaluation

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb.HomologyEvaluation
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf LateralTheory.E.LeafShMapZeroPf.Gen

variable {B : Scheme.{0}} {q : ℕ}

private def ev (H : SShv B q) (U : B.Etale) :
    ((F0 B q).obj U ⟶ H) ≃ ToType (H.obj.obj (op U)) :=
  ((sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H).trans
    ((((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv
      (uliftYoneda.{1}.obj U) H.obj).trans uliftYonedaEquiv)

private theorem ev_comp {H H' : SShv B q} (g : H ⟶ H') (U : B.Etale) (t : (F0 B q).obj U ⟶ H) :
    ev H' U (t ≫ g) = g.hom.app (op U) (ev H U t) := by
  have h1 := (sheafificationAdjunction (EtTop B)
    (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv_naturality_right t g
  have h2 := ((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv_naturality_right
    (X := uliftYoneda.{1}.obj U) ((sheafificationAdjunction (EtTop B)
      (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H t) ((sheafToPresheaf _ _).map g)
  exact (congrArg uliftYonedaEquiv ((congrArg (((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight
    B.Etaleᵒᵖ).homEquiv (uliftYoneda.{1}.obj U) H'.obj) h1).trans h2)).trans
      (uliftYonedaEquiv_comp _ _)

private theorem ev_map (H : SShv B q) {U U' : B.Etale} (a : U' ⟶ U) (t : (F0 B q).obj U ⟶ H) :
    ev H U' ((F0 B q).map a ≫ t) = H.obj.map a.op (ev H U t) := by
  have h1 := (sheafificationAdjunction (EtTop B)
    (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv_naturality_left
      (X' := ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).obj (uliftYoneda.{1}.obj U'))
      (X := ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).obj (uliftYoneda.{1}.obj U))
      (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).map
        (uliftYoneda.{1}.map a)) t
  have h2 := ((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv_naturality_left
    (uliftYoneda.{1}.map a) ((sheafificationAdjunction (EtTop B)
      (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H t)
  exact (congrArg uliftYonedaEquiv ((congrArg (((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight
    B.Etaleᵒᵖ).homEquiv (uliftYoneda.{1}.obj U') H.obj) h1).trans h2)).trans
      (uliftYonedaEquiv_naturality _ a.op).symm

private theorem lift_local {Z H : SShv B q} (π : Z ⟶ H) [Epi π] (U : B.Etale) (t : (F0 B q).obj U ⟶ H) :
    Cov U (fun U' a => ∃ c : (F0 B q).obj U' ⟶ Z, c ≫ π = (F0 B q).map a ≫ t) := by
  haveI : EssentiallySmall.{1} B.Etale := inferInstance
  haveI : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) := inferInstance
  have hls : Sheaf.IsLocallySurjective π :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{1} (ULift.{1} (ZMod q))) π).2 inferInstance
  refine ⟨Presheaf.imageSieve π.hom (ev H U t),
    Presheaf.imageSieve_mem (EtTop B) π.hom (U := op U) (ev H U t), fun U' a ha => ?_⟩
  obtain ⟨z, hz⟩ := ha
  refine ⟨(ev Z U').symm z, (ev H U').injective ?_⟩
  rw [ev_comp, ev_map, Equiv.apply_symm_apply]
  exact hz

end UpperTheory.Cb.HomologyEvaluation

open UpperTheory.Cb.HomologyEvaluation LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShMapZeroPf.Gen in
theorem UpperTheory.Cb.free_etale_sheaf_lift_exists :
    LateralTheory.E.LeafShMapZeroPf.EtaleLift' := by
  intro B q K U s
  obtain ⟨Z, π, hπ, hlift⟩ := exists_cycles (C := SShv B q) K
  refine (lift_local π U ((e0 B q).inv.app U ≫ s)).mono fun U' a hc => ?_
  obtain ⟨c, hc⟩ := hc
  obtain ⟨x, hx⟩ := hlift _ c
  refine ⟨x, ?_⟩
  have he : (e0 B q).hom.app U' =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0).hom.app ((F0 B q).obj U') :=
    Category.comp_id _
  have n : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ (e0 B q).hom.app U =
      (e0 B q).hom.app U' ≫ (F0 B q).map a := (e0 B q).hom.naturality a
  have s1 : s = (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s := by
    rw [Iso.hom_inv_id_app_assoc]
  have h1 : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫
        (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s := by rw [← s1]
  have h2 : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫
      (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s =
      (e0 B q).hom.app U' ≫ (F0 B q).map a ≫ (e0 B q).inv.app U ≫ s := by
    rw [reassoc_of% n]
    rfl
  have h3 : (e0 B q).hom.app U' ≫ (F0 B q).map a ≫ (e0 B q).inv.app U ≫ s =
      (e0 B q).hom.app U' ≫ c ≫ π := by rw [hc]
  have h4 : (e0 B q).hom.app U' ≫ c ≫ π =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map x := by
    rw [he]; exact hx.symm
  exact h1.trans (h2.trans (h3.trans h4))
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLineChartsOfHenselianFinite
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

namespace UpperTheory.Cb.ChartsOfProjectiveLine

section General

variable {σ : Type*} {R : Type} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem fromSpec_fac {f : R} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.isAffineOpen_basicOpen 𝒜 f hf hm).fromSpec =
      Spec.map (Proj.awayToSection 𝒜 f) ≫ Proj.awayι 𝒜 f hf hm := by
  have h : (Proj.basicOpenIsoSpec 𝒜 f hf hm).hom =
      (Proj.isAffineOpen_basicOpen 𝒜 f hf hm).isoSpec.hom ≫ Spec.map (Proj.awayToSection 𝒜 f) := by
    rw [IsAffineOpen.isoSpec_hom, Proj.basicOpenIsoSpec_hom]
    rfl
  rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc, ← h,
    Iso.hom_inv_id, Category.id_comp]

private theorem basicOpen_section {f g : R} {m e : ℕ} (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 e) (hm : 0 < m)
    (he : 0 < e) :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  have hU := Proj.isAffineOpen_basicOpen 𝒜 f hf hm
  have h1 : hU.fromSpec ⁻¹ᵁ (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      hU.fromSpec ⁻¹ᵁ Proj.basicOpen 𝒜 g := by
    rw [hU.fromSpec_preimage_basicOpen, show hU.fromSpec = _ from fromSpec_fac 𝒜 hf hm,
      Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 hf hm hg he,
      SpecMap_preimage_basicOpen]
  have key := congrArg (fun W => hU.fromSpec ''ᵁ W) h1
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, hU.opensRange_fromSpec] at key
  rw [← key]
  exact (inf_eq_right.mpr (Scheme.basicOpen_le _ _)).symm

private theorem res_inf {X : Scheme.{0}} {U V W : X.Opens} (hU : W ≤ U) (hV : W ≤ V) (hW : W = U ⊓ V)
    (x : Γ(X, U)) (y : Γ(X, V))
    (h : X.presheaf.map (homOfLE hU).op x * X.presheaf.map (homOfLE hV).op y = 1) :
    X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op y = 1 := by
  subst hW
  exact h

private theorem away_mul_one {f g : R} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    awayMap 𝒜 hg (rfl : f * g = f * g) (Away.isLocalizationElem hf hg) *
      awayMap 𝒜 hf (mul_comm f g : f * g = g * f) (Away.isLocalizationElem hg hf) = 1 := by
  rw [awayMap_mk, awayMap_mk]
  apply val_injective
  rw [val_mul, Away.val_mk, Away.val_mk, val_one, Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

private theorem sections_mul_one {f g : R} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    (Proj 𝒜).presheaf.map (homOfLE (inf_le_left :
        Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)).op
        (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) *
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_right :
        Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 g)).op
        (Proj.awayToSection 𝒜 g (Away.isLocalizationElem hg hf)) = 1 := by
  have e1 := congrArg (fun φ => φ.hom (Away.isLocalizationElem hf hg))
    (Proj.awayMap_awayToSection 𝒜 hg (rfl : f * g = f * g))
  have e2 := congrArg (fun φ => φ.hom (Away.isLocalizationElem hg hf))
    (Proj.awayMap_awayToSection 𝒜 hf (mul_comm f g : f * g = g * f))
  refine res_inf (Proj.basicOpen_mono 𝒜 _ _ ⟨_, rfl⟩)
    (Proj.basicOpen_mono 𝒜 _ _ ⟨_, mul_comm f g⟩) (Proj.basicOpen_mul 𝒜 f g) _ _ ?_
  have e3 := congrArg (Proj.awayToSection 𝒜 (f * g)) (away_mul_one 𝒜 hf hg)
  rw [map_mul, map_one] at e3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  refine Eq.trans ?_ e3
  exact congrArg₂ _ e1.symm e2.symm

private theorem section_surjective {f g : R} {m e : ℕ} (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 e) (hm : 0 < m)
    (h : Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away 𝒜 f))
      (Away.isLocalizationElem hf hg))) :
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(Proj 𝒜, Proj.basicOpen 𝒜 f))
      (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg))) := by
  intro y
  obtain ⟨p, hp⟩ := h ((Proj.basicOpenIsoAway 𝒜 f hf hm).inv y)
  refine ⟨p, ?_⟩
  have hy : Proj.awayToSection 𝒜 f ((Proj.basicOpenIsoAway 𝒜 f hf hm).inv y) = y :=
    (Proj.basicOpenIsoAway 𝒜 f hf hm).inv_hom_id_apply y
  rw [← hy, ← hp]
  simp only [Polynomial.coe_eval₂RingHom]
  have := Polynomial.hom_eval₂ p (Int.castRingHom (Away 𝒜 f)) (Proj.awayToSection 𝒜 f).hom
    (Away.isLocalizationElem hf hg)
  rw [show ((Proj.awayToSection 𝒜 f).hom).comp (Int.castRingHom (Away 𝒜 f)) = Int.castRingHom _ from
    RingHom.ext_int _ _] at this
  exact this.symm

private theorem charts_gen {f g : R} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (hcov : Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g = ⊤)
    (h1 : Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away 𝒜 f))
      (Away.isLocalizationElem hf hg)))
    (h2 : Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away 𝒜 g))
      (Away.isLocalizationElem hg hf))) :
    ∃ (U V : (Proj 𝒜).Opens) (s : Γ(Proj 𝒜, U)) (s' : Γ(Proj 𝒜, V)), IsAffineOpen U ∧ IsAffineOpen V ∧
      U ⊔ V = ⊤ ∧ (Proj 𝒜).basicOpen s = U ⊓ V ∧ (Proj 𝒜).basicOpen s' = U ⊓ V ∧
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
        (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
      Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(Proj 𝒜, U)) s) ∧
      Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(Proj 𝒜, V)) s') :=
  ⟨_, _, Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg),
    Proj.awayToSection 𝒜 g (Away.isLocalizationElem hg hf),
    Proj.isAffineOpen_basicOpen 𝒜 f hf one_pos, Proj.isAffineOpen_basicOpen 𝒜 g hg one_pos, hcov,
    basicOpen_section 𝒜 hf hg one_pos one_pos,
    (basicOpen_section 𝒜 hg hf one_pos one_pos).trans (inf_comm _ _),
    sections_mul_one 𝒜 hf hg, section_surjective 𝒜 hf hg one_pos h1,
    section_surjective 𝒜 hg hf one_pos h2⟩

end General

section Line

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem scale {S : Type} [CommRing S] (φ ψ : MvPolynomial (Fin 2) ℤ →+* S) (c : S)
    (h : ∀ k, ψ (X k) = c * φ (X k)) {n : ℕ} {a : MvPolynomial (Fin 2) ℤ} (ha : a.IsHomogeneous n) :
    ψ a = c ^ n * φ a := by
  have hC : ∀ r : ℤ, ψ (C r) = φ (C r) := fun r => by
    rw [show (C r : MvPolynomial (Fin 2) ℤ) = (r : MvPolynomial (Fin 2) ℤ) from eq_intCast C r,
      map_intCast, map_intCast]
  rw [a.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    by_contra hne
    exact (mem_support_iff.mp hd) (ha.coeff_eq_zero hne)
  rw [monomial_eq, map_mul, map_mul, hC, Finsupp.prod, map_prod, map_prod]
  simp only [map_pow, h, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

private abbrev G : ℕ → Submodule ℤ (MvPolynomial (Fin 2) ℤ) := homogeneousSubmodule (Fin 2) ℤ

private theorem X_mem (i : Fin 2) : (X i : MvPolynomial (Fin 2) ℤ) ∈ G 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X ℤ i)

private theorem surj_away {i j : Fin 2} (hij : j ≠ i) :
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away G (X i)))
      (Away.isLocalizationElem (X_mem i) (X_mem j))) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G (X_mem i) z
  have ha' : a.IsHomogeneous n := by
    have := (mem_homogeneousSubmodule _ _).mp ha
    simpa using this
  let q := Polynomial.eval₂RingHom (Int.castRingHom (Away G (X i)))
    (Away.isLocalizationElem (X_mem i) (X_mem j))
  let D : MvPolynomial (Fin 2) ℤ →+* Polynomial ℤ :=
    (aeval (fun k => if k = i then (1 : Polynomial ℤ) else Polynomial.X)).toRingHom
  let ι : Away G (X i) →+* Localization.Away (X i : MvPolynomial (Fin 2) ℤ) := algebraMap _ _
  let α : MvPolynomial (Fin 2) ℤ →+* Localization.Away (X i : MvPolynomial (Fin 2) ℤ) := algebraMap _ _
  have hX : ∀ k, α (X k) = α (X i) * (ι.comp (q.comp D)) (X k) := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp [D]
    · have hkj : k = j := by omega
      subst hkj
      have hD : D (X k) = Polynomial.X := by simp [D, hk]
      have hq : (ι.comp (q.comp D)) (X k) = ι (Away.isLocalizationElem (X_mem i) (X_mem k)) := by
        simp [hD, q]
      have hsp := IsLocalization.mk'_spec' (Localization.Away (X i : MvPolynomial (Fin 2) ℤ))
        (X k ^ 1 : MvPolynomial (Fin 2) ℤ)
        (⟨X i ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (X i : MvPolynomial (Fin 2) ℤ))
      have hι : ι (Away.isLocalizationElem (X_mem i) (X_mem k)) =
          IsLocalization.mk' (Localization.Away (X i : MvPolynomial (Fin 2) ℤ))
            (X k ^ 1 : MvPolynomial (Fin 2) ℤ)
            (⟨X i ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (X i : MvPolynomial (Fin 2) ℤ)) := by
        rw [← Localization.mk_eq_mk']
        rfl
      rw [hq, hι, ← pow_one (α (X k)), ← pow_one (α (X i)), ← map_pow, ← map_pow]
      exact hsp.symm
  have hs := scale (ι.comp (q.comp D)) α (α (X i)) hX ha'
  refine ⟨D a, ?_⟩
  apply val_injective
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  change ι (q (D a)) * α (X i ^ n) = α a
  rw [hs, map_pow, mul_comm]
  rfl

private theorem cover : Proj.basicOpen G (X 0) ⊔ Proj.basicOpen G (X 1) = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top' G (X : Fin 2 → MvPolynomial (Fin 2) ℤ)
    (fun i => ⟨1, X_mem i⟩) (by
      rw [eq_top_iff]
      intro p _
      induction p using MvPolynomial.induction_on with
      | C a => exact Subalgebra.algebraMap_mem _ (⟨C a, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ a)⟩ : G 0)
      | add p q hp hq => exact add_mem (hp trivial) (hq trivial)
      | mul_X p i hp => exact mul_mem (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩))
  rw [eq_top_iff, ← h]
  refine iSup_le fun i => ?_
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private theorem intersectionNumber_baseChange : LateralTheory.E.ProjectiveLineCharts₂.ProjectiveLineTwoAffineChartsPolynomialGenerated :=
  charts_gen G (X_mem 0) (X_mem 1) cover (surj_away (by decide)) (surj_away (by decide))

end Line

end UpperTheory.Cb.ChartsOfProjectiveLine

theorem UpperTheory.Cb.projectiveLineCharts_of_henselianFinite :
    LateralTheory.E.LZProperCut.LZHensFinite → LateralTheory.E.ProjectiveLineCharts₂.ProjectiveLineTwoAffineChartsPolynomialGenerated := fun _ =>
  UpperTheory.Cb.ChartsOfProjectiveLine.intersectionNumber_baseChange
end
end

