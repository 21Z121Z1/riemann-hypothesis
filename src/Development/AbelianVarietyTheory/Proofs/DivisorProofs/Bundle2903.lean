import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGaloisDescentAbelianVarietyFinit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem spMap_mul_aut {K' : Type} [Field K'] (a b : K' ≃+* K') :
    spMap ((a * b : K' ≃+* K') : K' →+* K') = spMap (a : K' →+* K') ≫ spMap (b : K' →+* K') := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem lbIso_pull_comp_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a b : X ⟶ X)
    (ha : LBIso L (L.pull a)) (hb : LBIso L (L.pull b)) : LBIso L (L.pull (a ≫ b)) :=
  LBIso.trans hL (pull_isLB hL a) (pull_isLB hL _) ha
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L a a rfl) (chartPullSame L _ (fun _ => b) _ a fun _ => rfl) hb)

theorem exists_lb_descent_of_finite_aut : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ L' : LB A'.left, L'.IsLB → (∀ g, ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧ ψ ≫ A'.hom = A'.hom ≫ spMap (s g).toRingHom ∧ LBIso L' (L'.pull ψ)) → ∃ L : LB A.left, L.IsLB ∧ LBIso L' (L.pull φ) := by
  intro K K' _ _ i hfin Γ _ s hs hfix A _ A' _ φ hA hp L' hL' hinv
  letI : Algebra K K' := i.toAlgebra
  obtain ⟨hgal, hgen⟩ := GlobalTheory.T.isGalois_of_finite_fixed_automorphisms K K' i hfin Γ s hs hfix
  haveI : FiniteDimensional K K' := hfin
  have hc0 := GlobalTheory.ZM.DwModel.isGaloisCover_field K K'
  have hfixσ : ∀ σ : K' ≃ₐ[K] K', ∀ x, (σ : K' ≃+* K') (i x) = i x := fun σ x => σ.commutes x
  have hσi : ∀ σ : K' ≃ₐ[K] K', spMap (σ : K' →+* K') ≫ spMap i = spMap i := fun σ => by
    simp only [spMap, ← Spec.map_comp]
    congr 1
    ext x
    exact σ.commutes x
  have hw : ∀ σ : K' ≃ₐ[K] K', (A'.hom ≫ spMap (σ : K' →+* K')) ≫ spMap i = φ ≫ A.hom := fun σ => by
    rw [Category.assoc, hσi σ, hp.1.w]
  let t : (K' ≃ₐ[K] K') → (A'.left ⟶ A'.left) := fun σ =>
    hp.1.lift φ (A'.hom ≫ spMap (σ : K' →+* K')) (hw σ).symm
  have ht1 : ∀ σ, t σ ≫ φ = φ := fun σ => hp.1.lift_fst _ _ _
  have ht2 : ∀ σ, t σ ≫ A'.hom = A'.hom ≫ spMap (σ : K' →+* K') := fun σ => hp.1.lift_snd _ _ _
  have hGC : GlobalTheory.ZM.IsGaloisCover (K' ≃ₐ[K] K') t φ :=
    hc0.of_isPullback (u := A'.hom) (v := A.hom) hp.1.flip (fun a => ht2 a) ht1

  have hQ : ∀ τ ∈ Submonoid.closure (Set.range s), ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧
      ψ ≫ A'.hom = A'.hom ≫ spMap (τ : K' →+* K') ∧ LBIso L' (L'.pull ψ) := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hinv g
    | one =>
      refine ⟨𝟙 _, Category.id_comp _, ?_, ?_⟩
      · rw [Category.id_comp]
        have : ((1 : K' ≃+* K') : K' →+* K') = RingHom.id K' := rfl
        rw [this]
        exact (Category.comp_id _).symm.trans (by simp [spMap])
      · exact LBIso.symm (lbIso_of_chartPull (chartPullPull L' (𝟙 _)) hL')
    | mul x y _ _ hx hy =>
      obtain ⟨ψ₁, a1, b1, c1⟩ := hx
      obtain ⟨ψ₂, a2, b2, c2⟩ := hy
      refine ⟨ψ₁ ≫ ψ₂, by rw [Category.assoc, a2, a1], ?_, lbIso_pull_comp_self hL' _ _ c1 c2⟩
      rw [Category.assoc, b2, ← Category.assoc, b1, Category.assoc, spMap_mul_aut]
  have hall : ∀ σ : K' ≃ₐ[K] K', LBIso L' (L'.pull (t σ)) := fun σ => by
    obtain ⟨ψ, a1, b1, c1⟩ := hQ (σ : K' ≃+* K') (hgen _ (hfixσ σ))
    have : ψ = t σ := hp.1.hom_ext (by rw [a1, ht1]) (by rw [b1, ht2]; rfl)
    exact this ▸ c1
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hp
  have hsurj : Function.Surjective A'.hom.appTop.hom := (GlobalTheory.globalFns_holds (Sp K') A' hA').2
  let e : Sp K' ⟶ A'.left := hp.1.lift (spMap i ≫ eSec A) (𝟙 _) (by
    rw [Category.id_comp, Category.assoc, show eSec A ≫ A.hom = 𝟙 _ from Over.w η[A]]; exact Category.comp_id _)
  have he : e ≫ A'.hom = 𝟙 _ := hp.1.lift_snd _ _ _
  have heθ : ∀ σ : K' ≃ₐ[K] K', e ≫ t σ = spMap (σ : K' →+* K') ≫ e := fun σ => by
    refine hp.1.hom_ext ?_ ?_
    · rw [Category.assoc, ht1, Category.assoc, hp.1.lift_fst, ← Category.assoc, hσi σ]
    · rw [Category.assoc, ht2, ← Category.assoc, he, Category.assoc, he]
      simp
  obtain ⟨u, hu, hcoc⟩ := GlobalTheory.T.exists_linearisation_invariant_rigidified_bundle (Sp K') A'.left A'.hom e he hsurj L' hL'
    (GlobalTheory.SS.HtForm.gen_field _ (pull_isLB hL' e)) (K' ≃ₐ[K] K') t (fun σ => spMap (σ : K' →+* K'))
    (fun a c => hGC.mul a c) (fun a c => hc0.mul a c) heθ hall
  exact GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ φ _ t L' hGC hL' u hu hcoc

end GlobalTheory.Mum.GenDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGlueMilnorPatchingArtinLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ArtinPatch

theorem elem_of_isPullback {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    (H : IsPullback f g h i) :
    (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩

theorem isPushout_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (H : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁.hom) :
    IsPushout f₁ f₂ g₁ g₂ := by
  obtain ⟨-, hex⟩ := elem_of_isPullback H
  have key : ∀ s : PushoutCocone f₁ f₂, RingHom.ker g₁.hom ≤ RingHom.ker s.inl.hom := by
    intro s r hr
    rw [RingHom.mem_ker] at hr ⊢
    obtain ⟨a, ha1, ha2⟩ := hex r 0 (by rw [hr, map_zero])
    have e := congrArg (fun φ => φ.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [← ha1, e, ha2, map_zero]
  let d : ∀ s : PushoutCocone f₁ f₂, R₀ ⟶ s.pt := fun s =>
    CommRingCat.ofHom (RingHom.liftOfRightInverse g₁.hom (Function.surjInv hg₁)
      (Function.rightInverse_surjInv hg₁) ⟨s.inl.hom, key s⟩)
  have hd : ∀ (s : PushoutCocone f₁ f₂) (r : R₁), (d s).hom (g₁.hom r) = s.inl.hom r := fun s r => by
    simp only [d, CommRingCat.hom_ofHom]
    exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  refine IsPushout.of_isColimit (c := PushoutCocone.mk g₁ g₂ H.w) ?_
  refine PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_
  · intro s
    ext r
    exact hd s r
  · intro s
    ext r₂
    obtain ⟨r₁, hr₁⟩ := hg₁ (g₂.hom r₂)
    obtain ⟨a, ha1, ha2⟩ := hex r₁ r₂ hr₁
    have e := congrArg (fun φ => φ.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    change (d s).hom (g₂.hom r₂) = s.inr.hom r₂
    rw [← hr₁, hd, ← ha1, e, ha2]
  · intro s m h1 _
    ext y
    obtain ⟨r, rfl⟩ := hg₁ y
    have e := congrArg (fun φ => φ.hom r) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    change m.hom (g₁.hom r) = (d s).hom (g₁.hom r)
    rw [hd]
    exact e

theorem spec_eq_of_artinian (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P] (x y : Spec P) :
    x = y := by
  have h : ∀ z : PrimeSpectrum P, z.asIdeal = IsLocalRing.maximalIdeal P := fun z =>
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime z.asIdeal)
  exact PrimeSpectrum.ext ((h x).trans (h y).symm)

end GlobalTheory.ArtinPatch

namespace GlobalTheory.ArtinPatch

theorem glues_spec {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀}
    (H : IsPullback f₁ f₂ g₁ g₂) (hP : ∀ x y : Spec P, x = y) :
    GlobalTheory.PinchLift.Glues (Spec.map f₂) (Spec.map f₁) (Spec.map g₂) (Spec.map g₁) := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback H
  have inj : ∀ {R : CommRingCat.{0}} (u v : Γ(Spec R, ⊤)),
      (Scheme.ΓSpecIso R).hom.hom u = (Scheme.ΓSpecIso R).hom.hom v → u = v := by
    intro R u v h
    simpa using congrArg (Scheme.ΓSpecIso R).inv.hom h
  have nat : ∀ {R S : CommRingCat.{0}} (f : R ⟶ S) (u : Γ(Spec R, ⊤)),
      (Scheme.ΓSpecIso S).hom.hom ((Spec.map f).appTop.hom u) = f.hom ((Scheme.ΓSpecIso R).hom.hom u) := by
    intro R S f u
    exact congrArg (fun φ => φ.hom u) (Scheme.ΓSpecIso_naturality f)
  refine GlobalTheory.PinchLift.glues_of_basis _ _ _ _ {⊤} ?_ ?_
  · intro W x hx
    refine ⟨⊤, rfl, trivial, fun y _ => ?_⟩
    rw [hP y x]
    exact hx
  · rintro W rfl a b hab
    set V := Spec.map g₂ ⁻¹ᵁ Spec.map f₂ ⁻¹ᵁ (⊤ : (Spec P).Opens) ⊓
      Spec.map g₁ ⁻¹ᵁ Spec.map f₁ ⁻¹ᵁ (⊤ : (Spec P).Opens) with hVdef
    have hV : V = ⊤ := top_le_iff.1 (fun x _ => ⟨trivial, trivial⟩)
    have hiso : IsIso (homOfLE (le_top : V ≤ ⊤)) := by
      rw [show homOfLE (le_top : V ≤ ⊤) = (eqToIso hV).hom from Subsingleton.elim _ _]
      infer_instance
    set ρ := (Spec R₀).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    have hρ : ∀ u v, ρ.hom u = ρ.hom v → u = v := by
      intro u v h
      simpa using congrArg (inv ρ).hom h
    have e : (Spec.map g₂).appTop.hom a = (Spec.map g₁).appTop.hom b := by
      apply hρ
      exact hab
    have key : g₁.hom ((Scheme.ΓSpecIso R₁).hom.hom b) = g₂.hom ((Scheme.ΓSpecIso R₂).hom.hom a) := by
      rw [← nat g₁ b, ← nat g₂ a, e]
    obtain ⟨x, hx1, hx2⟩ := hex _ _ key
    refine ⟨(Scheme.ΓSpecIso P).inv.hom x, ⟨?_, ?_⟩, ?_⟩
    · apply inj
      change (Scheme.ΓSpecIso R₂).hom.hom ((Spec.map f₂).appTop.hom _) = _
      rw [nat]
      simpa using hx2
    · apply inj
      change (Scheme.ΓSpecIso R₁).hom.hom ((Spec.map f₁).appTop.hom _) = _
      rw [nat]
      simpa using hx1
    · rintro s ⟨hs2, hs1⟩
      apply inj
      simp only [Iso.inv_hom_id_apply]
      apply hinj
      · rw [← nat]
        change (Scheme.ΓSpecIso R₁).hom.hom (((Spec.map f₁).app ⊤).hom s) = _
        rw [hs1, hx1]
      · rw [← nat]
        change (Scheme.ΓSpecIso R₂).hom.hom (((Spec.map f₂).app ⊤).hom s) = _
        rw [hs2, hx2]

end GlobalTheory.ArtinPatch

namespace GlobalTheory.ArtinPatch

theorem exists_lb_glue : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hg₁ hg₂ X X₁ X₂ X₀ j₁ j₂ i₁ i₂ hflat h₁ h₂ h₀ hc hc₂ L₁ L₂ hL₁ hL₂ hiso
  haveI := hloc
  haveI := hart
  obtain ⟨-, hex⟩ := elem_of_isPullback hpb
  have hf₁ : Function.Surjective f₁.hom := fun r => by
    obtain ⟨r₂, hr₂⟩ := hg₂ (g₁.hom r)
    obtain ⟨a, ha, -⟩ := hex r r₂ hr₂.symm
    exact ⟨a, ha⟩
  have hw : Spec.map g₂ ≫ Spec.map f₂ = Spec.map g₁ ≫ Spec.map f₁ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hpb.w]

  let O : Over (Spec P) := Over.mk (𝟙 (Spec P))
  let O₂ : Over (Spec P) := Over.mk (Spec.map f₂)
  let O₁ : Over (Spec P) := Over.mk (Spec.map f₁)
  let O₀ : Over (Spec P) := Over.mk (Spec.map g₁ ≫ Spec.map f₁)
  let q : O₂ ⟶ O := Over.homMk (Spec.map f₂) (Category.comp_id _)
  let r : O₁ ⟶ O := Over.homMk (Spec.map f₁) (Category.comp_id _)
  let r' : O₀ ⟶ O₂ := Over.homMk (Spec.map g₂) hw
  let q' : O₀ ⟶ O₁ := Over.homMk (Spec.map g₁) rfl
  have hcomm : r' ≫ q = q' ≫ r := by
    ext1
    simpa [q, r, q', r'] using hw
  have hsq : IsPullback r'.left q'.left q.left r.left :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_of_isPullback hpb hg₁).flip)
  haveI hcl : IsClosedImmersion r.left := IsClosedImmersion.spec_of_surjective f₁ hf₁
  have haff : IsAffineHom q.left := by
    change IsAffineHom (Spec.map f₂)
    infer_instance
  have hgl : GlobalTheory.PinchLift.Glues q.left r.left r'.left q'.left :=
    glues_spec hpb (spec_eq_of_artinian P)
  obtain ⟨hpb', haff', hcl', hgl'⟩ :=
    GlobalTheory.PinchLift.glues_whiskerLeft (Spec P) X O O₂ O₁ O₀ q r r' q' hflat hcomm hsq haff hcl hgl

  have hT : ∀ U : Over (Spec P), IsPullback (fst X U).left (snd X U).left X.hom U.hom :=
    fun U => IsPullback.of_hasPullback X.hom U.hom
  have h₀' : IsPullback (i₁ ≫ j₁) X₀.hom X.hom (Spec.map g₁ ≫ Spec.map f₁) := h₀.paste_horiz h₁
  let ψ₂ := IsPullback.isoIsPullback _ _ h₂ (hT O₂)
  let ψ₁ := IsPullback.isoIsPullback _ _ h₁ (hT O₁)
  let ψ₀ := IsPullback.isoIsPullback _ _ h₀' (hT O₀)
  have p₂f : ψ₂.hom ≫ (fst X O₂).left = j₂ := IsPullback.isoIsPullback_hom_fst _ _ h₂ (hT O₂)
  have p₂s : ψ₂.hom ≫ (snd X O₂).left = X₂.hom := IsPullback.isoIsPullback_hom_snd _ _ h₂ (hT O₂)
  have p₁f : ψ₁.hom ≫ (fst X O₁).left = j₁ := IsPullback.isoIsPullback_hom_fst _ _ h₁ (hT O₁)
  have p₁s : ψ₁.hom ≫ (snd X O₁).left = X₁.hom := IsPullback.isoIsPullback_hom_snd _ _ h₁ (hT O₁)
  have p₀f : ψ₀.hom ≫ (fst X O₀).left = i₁ ≫ j₁ := IsPullback.isoIsPullback_hom_fst _ _ h₀' (hT O₀)
  have p₀s : ψ₀.hom ≫ (snd X O₀).left = X₀.hom := IsPullback.isoIsPullback_hom_snd _ _ h₀' (hT O₀)
  let s : X.left ⟶ (X ⊗ O).left := (hT O).lift (𝟙 _) X.hom (by simp [O])
  have wf : ∀ {U V : Over (Spec P)} (k : U ⟶ V), (X ◁ k).left ≫ (fst X V).left = (fst X U).left := by
    intro U V k
    rw [← Over.comp_left, whiskerLeft_fst]
  have ws : ∀ {U V : Over (Spec P)} (k : U ⟶ V), (X ◁ k).left ≫ (snd X V).left = (snd X U).left ≫ k.left := by
    intro U V k
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have E₂ : j₂ ≫ s = ψ₂.hom ≫ (X ◁ q).left := by
    apply (hT O).hom_ext
    · rw [Category.assoc, Category.assoc, wf, (hT O).lift_fst, p₂f, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ws, (hT O).lift_snd, ← Category.assoc, p₂s]
      exact h₂.w
  have E₁ : j₁ ≫ s = ψ₁.hom ≫ (X ◁ r).left := by
    apply (hT O).hom_ext
    · rw [Category.assoc, Category.assoc, wf, (hT O).lift_fst, p₁f, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ws, (hT O).lift_snd, ← Category.assoc, p₁s]
      exact h₁.w
  have E₀₂ : ψ₀.hom ≫ (X ◁ r').left = i₂ ≫ ψ₂.hom := by
    apply (hT O₂).hom_ext
    · rw [Category.assoc, Category.assoc, wf, p₀f, p₂f, hc]
    · rw [Category.assoc, Category.assoc, ws, ← Category.assoc, p₀s, p₂s]
      exact hc₂.symm
  have E₀₁ : ψ₀.hom ≫ (X ◁ q').left = i₁ ≫ ψ₁.hom := by
    apply (hT O₁).hom_ext
    · rw [Category.assoc, Category.assoc, wf, p₀f, p₁f]
    · rw [Category.assoc, Category.assoc, ws, ← Category.assoc, p₀s, p₁s]
      exact h₀.w.symm

  have hab0 : GlobalTheory.CechPic.pull i₂ (GlobalTheory.CechPic.cls L₂ hL₂) = GlobalTheory.CechPic.pull i₁ (GlobalTheory.CechPic.cls L₁ hL₁) := by
    rw [← GlobalTheory.CechPic.cls_pull hL₂ i₂ (pull_isLB hL₂ i₂), ← GlobalTheory.CechPic.cls_pull hL₁ i₁ (pull_isLB hL₁ i₁)]
    exact ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hiso).symm
  have e2 : (X ◁ r').left ≫ ψ₂.inv = ψ₀.inv ≫ i₂ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, E₀₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e1 : (X ◁ q').left ≫ ψ₁.inv = ψ₀.inv ≫ i₁ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, E₀₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hab : GlobalTheory.CechPic.pull (X ◁ r').left (GlobalTheory.CechPic.pull ψ₂.inv (GlobalTheory.CechPic.cls L₂ hL₂)) =
      GlobalTheory.CechPic.pull (X ◁ q').left (GlobalTheory.CechPic.pull ψ₁.inv (GlobalTheory.CechPic.cls L₁ hL₁)) := by
    rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, e2, e1, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.pull_comp, hab0]
  obtain ⟨e', he2, he1⟩ := GlobalTheory.PinchLift.exists_pic_patch _ _ _ _ _ _ _ _ hpb' haff' hcl' hgl' _ _ hab
  obtain ⟨L, hL, hLe⟩ := GlobalTheory.CechPic.cls_surj (GlobalTheory.CechPic.pull s e')
  refine ⟨L, hL, ?_, ?_⟩
  · have h : GlobalTheory.CechPic.cls (L.pull j₁) (pull_isLB hL j₁) = GlobalTheory.CechPic.cls L₁ hL₁ := by
      rw [GlobalTheory.CechPic.cls_pull hL j₁, hLe, ← GlobalTheory.CechPic.pull_comp, E₁, GlobalTheory.CechPic.pull_comp, he1,
        ← GlobalTheory.CechPic.pull_comp, Iso.hom_inv_id, GlobalTheory.CechPic.pull_id]
    exact LBIso.symm ((GlobalTheory.CechPic.cls_eq_iff _ _).1 h)
  · have h : GlobalTheory.CechPic.cls (L.pull j₂) (pull_isLB hL j₂) = GlobalTheory.CechPic.cls L₂ hL₂ := by
      rw [GlobalTheory.CechPic.cls_pull hL j₂, hLe, ← GlobalTheory.CechPic.pull_comp, E₂, GlobalTheory.CechPic.pull_comp, he2,
        ← GlobalTheory.CechPic.pull_comp, Iso.hom_inv_id, GlobalTheory.CechPic.pull_id]
    exact LBIso.symm ((GlobalTheory.CechPic.cls_eq_iff _ _).1 h)

end GlobalTheory.ArtinPatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompPullbackIdValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.IsoPullIdComp

theorem exists_comp_val : ∀ {Y X₀ X : Scheme.{0}} {A : LB Y} {L₀ : LB X₀} {M : LB X} {K₀ K : Type} [Fintype K₀] [Fintype K] (φ₀ : K₀ → (Y ⟶ X₀)) (ε₀ : K₀ → ℤ) (φ : K → (Y ⟶ X)) (ε : K → ℤ), A.IsLB → L₀.IsLB → M.IsLB → ∀ (u : LB.Iso A (LB.LinComb L₀ φ₀ ε₀)), u.IsGen → ∀ (v : LB.Iso (LB.LinComb L₀ φ₀ ε₀) ((LB.LinComb M φ ε).pull (𝟙 Y))), v.IsGen → ∃ w : LB.Iso A (LB.LinComb M φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J₀ : (Z ⟶ X₀) → L₀.ι) (a : A.ι), q z ∈ A.U a → Good M z J → Good L₀ z J₀ → gm q z _ (w.s (fun k => J (q ≫ φ k), a)) = gm q z _ (u.s (fun k => J₀ (q ≫ φ₀ k), a)) * GlobalTheory.Mum.Two.isoVal v q z J J₀ := by
  intro Y X₀ X A L₀ M K₀ K _ _ φ₀ ε₀ φ ε hA hL₀ hM u hu v hv
  have eu := GlobalTheory.LinCombComp.gm_iso_linComb φ₀ ε₀ u hu
  have ev : ∀ (y : Y) (j j' : K → M.ι) (j₀ j₀' : K₀ → L₀.ι), y ∈ LB.wchart M φ j → y ∈ LB.wchart L₀ φ₀ j₀ →
      y ∈ LB.wchart M φ j' → y ∈ LB.wchart L₀ φ₀ j₀' →
      gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
          (v.s (fun _ => j, j₀)) =
        (trF φ ε (𝟙 Y) y j j' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
          gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀'))
            (v.s (fun _ => j', j₀')) := by
    intro y j j' j₀ j₀' h h0 h' h0'
    have hp : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) := ⟨mem_pull.2 h, h0⟩
    have hq : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀') := ⟨mem_pull.2 h', h0'⟩
    have e1 := GlobalTheory.LinCombComp.gm_gen hv (𝟙 Y) y hp hq
    rw [GlobalTheory.Mum.Two.gm_div_pull (𝟙 Y) y _ _ hp hq, Category.comp_id] at e1
    exact e1
  have glue : ∀ (j : K → M.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart M φ j ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι), q z ∈ LB.wchart M φ j → q z ∈ A.U a →
        q z ∈ LB.wchart L₀ φ₀ j₀ →
        gm q z (LB.wchart M φ j ⊓ A.U a) s =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j a
    obtain ⟨W, hW⟩ : ∃ W : (K₀ → L₀.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart M φ j ⊓ A.U a ⊓ LB.wchart L₀ φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart M φ j ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L₀ φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart M φ j ⊓ A.U a := fun j₀ y hy => ((memW y j₀).1 hy).1
    have l₁ : ∀ j₀, W j₀ ≤ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) :=
      fun j₀ y hy => ⟨mem_pull.2 ((memW y j₀).1 hy).1.1, ((memW y j₀).1 hy).2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L₀ φ₀ j₀ ⊓ A.U a := fun j₀ y hy =>
      ⟨((memW y j₀).1 hy).2, ((memW y j₀).1 hy).1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (v.s (fun _ => j, j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart M φ j ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu
      (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ev y j j j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha,
          GlobalTheory.LinCombComp.trF_self hM φ ε (𝟙 Y) y j h1, gm_self hA (𝟙 Y) y ha]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J J₀ a ha hJ hJ₀ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
    have h0 : y ∈ LB.wchart L₀ φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart M φ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ ε (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart M φ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ev y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha',
        GlobalTheory.LinCombComp.trF_self hL₀ φ₀ ε₀ (𝟙 Y) y j₀ h0]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    have hm : y ∈ (LB.div (LB.LinComb M φ ε) A).U p ⊓ (LB.div (LB.LinComb M φ ε) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (GlobalTheory.LinCombComp.gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb M φ ε (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · refine (hs _ a Z q z (fun k => J₀ (q ≫ φ₀ k)) (hJ.mem φ q) ha (hJ₀.mem φ₀ q)).trans
      ((mul_comm _ _).trans (congrArg _ ?_))
    have e : ∀ b b', b = b' → gm q z _ (v.s b) = gm q z _ (v.s b') := by rintro _ _ rfl; rfl
    exact e _ _ (Prod.ext (funext fun _ => funext fun k => by simp only [Category.id_comp]) rfl)

end GlobalTheory.IsoPullIdComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoRestrictAlongSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

noncomputable section

namespace GlobalTheory.IsoRes

variable {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb}

theorem comp_pt {A B C : Scheme.{0}} (f : A ⟶ B) (h : B ⟶ C) (x : A) : (f ≫ h) x = h (f x) := by
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]

theorem sec_apply (hgi : gi ≫ g = 𝟙 XT) (x : XT) : g (gi x) = x := by
  rw [← comp_pt, hgi]; rfl

theorem chart_le (hgi : gi ≫ g = 𝟙 XT) (J : PUnit → LG.ι) (k : LT.ι) :
    (LG.pull (gi ≫ c)).U J ⊓ LT.U k ≤ gi ⁻¹ᵁ ((LG.pull c).U J ⊓ (LT.pull g).U (fun _ => k)) := by
  intro x hx
  refine ⟨mem_pull.2 ?_, mem_pull.2 ?_⟩
  · have := mem_pull.1 hx.1
    rwa [comp_pt] at this
  · rw [sec_apply hgi]; exact hx.2

def resIso (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) : LB.Iso LT (LG.pull (gi ≫ c)) where
  s := fun p => res (chart_le hgi p.1 p.2) (pullU gi _ (w₀.s (p.1, fun _ => p.2)))

theorem gw_resIso (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) {Z : Scheme.{0}} (r : Z ⟶ XT) (z : Z)
    (j : LG.ι) (k : LT.ι) : gw (resIso hgi w₀) r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  by_cases h : r z ∈ (LG.pull (gi ≫ c)).U (fun _ => j) ⊓ LT.U k
  · have h' : gi (r z) ∈ (LG.pull c).U (fun _ => j) ⊓ (LT.pull g).U (fun _ => k) := chart_le hgi _ _ h
    exact (gm_res r z _ h _).trans (gm_pull r gi z _ h' _)
  · have h' : ¬ (r ≫ gi) z ∈ (LG.pull c).U (fun _ => j) ⊓ (LT.pull g).U (fun _ => k) := by
      intro hm
      apply h
      rw [comp_pt] at hm
      refine ⟨mem_pull.2 ?_, ?_⟩
      · rw [comp_pt]; exact mem_pull.1 hm.1
      · have := mem_pull.1 hm.2
        rwa [sec_apply hgi] at this
    show gm r z _ _ = gm (r ≫ gi) z _ _
    rw [gm, gm, dif_neg h, dif_neg h']; rfl

theorem resIso_pgen (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : PGen w₀) :
    PGen (resIso hgi w₀) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_resIso, gw_resIso]
  rw [comp_pt] at hj hj'
  have hj0 : c ((f ≫ gi) y) ∈ LG.U j := by rw [comp_pt]; exact hj
  have hj0' : c ((f ≫ gi) y) ∈ LG.U j' := by rw [comp_pt]; exact hj'
  have hk0 : (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k) := mem_pull.2 (by rw [comp_pt, sec_apply hgi]; exact hk)
  have hk0' : (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k') := mem_pull.2 (by rw [comp_pt, sec_apply hgi]; exact hk')
  have e := hw₀ Y (f ≫ gi) y j j' (fun _ => k) (fun _ => k') hj0 hj0' hk0 hk0'
  have e2 : gm (f ≫ gi) y ((LT.pull g).U (fun _ => k) ⊓ (LT.pull g).U (fun _ => k'))
      ((LT.pull g).g (fun _ => k) (fun _ => k')) = gm f y _ (LT.g k k') := by
    show gm (f ≫ gi) y _ (∏ _k : PUnit, (res _ (pullU g _ (LT.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (f ≫ gi) y _
      (show (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k) ⊓ (LT.pull g).U (fun _ => k') from ⟨hk0, hk0'⟩) _).trans
      ((gm_pull (f ≫ gi) g y (LT.U k ⊓ LT.U k') ⟨mem_pull.1 hk0, mem_pull.1 hk0'⟩ _).trans ?_)
    rw [Category.assoc, hgi, Category.comp_id]
  rw [e, e2, Category.assoc]

theorem exists_iso_restrict : ∀ {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} (hG : LG.IsLB) (hT : LT.IsLB) {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb} (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : w₀.IsGen), ∃ w : LB.Iso LT (LG.pull (gi ≫ c)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ XT) (z : Z) (j : LG.ι) (k : LT.ι), gw w r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  intro XG XT Pb LG LT hG hT c g gi hgi w₀ hw₀
  exact ⟨resIso hgi w₀, (isGen_iff _).2 (resIso_pgen hgi w₀ ((isGen_iff _).1 hw₀)),
    fun Z r z j k => gw_resIso hgi w₀ r z j k⟩

end GlobalTheory.IsoRes
end
end

