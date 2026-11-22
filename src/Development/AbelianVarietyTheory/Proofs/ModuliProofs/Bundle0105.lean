import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeomPtRangeEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem exists_geomPt_range_eq (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X), Set.range z = {g} := by
  let κ := X.residueField g
  let k := AlgebraicClosure κ
  refine ⟨k, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g, ?_⟩
  have hsub : Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g) ⊆ {g} := by
    rw [← X.range_fromSpecResidueField g]
    rintro _ ⟨p, rfl⟩
    exact ⟨_, rfl⟩
  have hne : (Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g)).Nonempty :=
    Set.range_nonempty _
  exact (Set.Nonempty.subset_singleton_iff hne).mp hsub

private lemma exists_factor_of_range_subset_closedImmersion {T N B : Scheme.{0}} [IsReduced T] (x : T ⟶ B) (ν : N ⟶ B)
    [IsClosedImmersion ν] (h : Set.range x ⊆ Set.range ν) : ∃ l : T ⟶ N, l ≫ ν = x := by
  have : Surjective (pullback.snd ν x) := ⟨fun t => by
    have ht : t ∈ Set.range (pullback.snd ν x) := by
      rw [Scheme.Pullback.range_snd]
      exact h ⟨t, rfl⟩
    exact ht⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd ν x)
  exact ⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem etSet_of_kerSet :
    ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') (K : Set G.left), IsSeparated G'.hom → IsFinite ψ.left → Etale ψ.left → KerSet ψ K → EtSet G K ∧ (IsReduced S → ∀ (C : Over S) (j : C ⟶ G), Etale C.hom → IsClosedImmersion j.left → Set.range j.left = K → IsPullback j (toUnit C) ψ η[G']) := by
  intro S G G' _ _ ψ K hsep hfin het hK
  have hew : (η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom = 𝟙 S := Over.w _
  have : IsClosedImmersion ((η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom) := by
    rw [hew]
    have : IsIso (𝟙 S) := inferInstance
    infer_instance
  have he : IsClosedImmersion (η[G'] : 𝟙_ (Over S) ⟶ G').left := IsClosedImmersion.of_comp _ G'.hom
  have htu : ∀ Y : Over S, (toUnit Y).left = Y.hom := fun Y =>
    (Category.comp_id _).symm.trans (Over.w (toUnit Y))
  have hfac : ∀ {T : Scheme.{0}} [IsReduced T] (w : T ⟶ G.left),
      Set.range (w ≫ ψ.left) ⊆ Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left →
      w ≫ ψ.left = (w ≫ G.hom) ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    intro T _ w hw
    obtain ⟨l, hl⟩ := exists_factor_of_range_subset_closedImmersion (w ≫ ψ.left) _ hw
    have hl' : l = w ≫ G.hom := by
      have := congrArg (· ≫ G'.hom) hl
      simp only [Category.assoc, hew, Over.w] at this
      exact this
    rw [← hl, hl']
  have hKeq : K = ψ.left ⁻¹' Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    ext q
    obtain ⟨k, _, _, w, hw⟩ := exists_geomPt_range_eq G.left q
    have key := hK k (w ≫ G.hom) (Over.homMk w rfl)
    have hr : Set.range (Over.homMk (U := Over.mk (w ≫ G.hom)) w rfl).left = {q} := hw
    rw [hr, Set.singleton_subset_iff] at key
    rw [← key, Set.mem_preimage]
    obtain ⟨p, rfl⟩ : q ∈ Set.range w := hw ▸ rfl
    constructor
    · intro h
      have h2 : w ≫ ψ.left = (toUnit (Over.mk (w ≫ G.hom))).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left :=
        congrArg (fun f => f.left) h
      refine ⟨(toUnit (Over.mk (w ≫ G.hom))).left p, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← h2, Scheme.Hom.comp_apply]
    · intro h
      have hw2 := hfac w (by
        rintro _ ⟨p', rfl⟩
        have h3 : w p' ∈ ({w p} : Set G.left) := hw ▸ Set.mem_range_self p'
        rw [Set.mem_singleton_iff] at h3
        rw [Scheme.Hom.comp_apply, h3]
        exact h)
      ext1
      change w ≫ ψ.left = (toUnit (Over.mk (w ≫ G.hom))).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left
      rw [htu]
      exact hw2
  have hsqS : ∀ (C : Over S) (j : C ⟶ G), IsReduced C.left → Set.range j.left = K →
      j.left ≫ ψ.left = C.hom ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    intro C j _ hjr
    have := hfac j.left (by
      rintro _ ⟨p, rfl⟩
      have hp : j.left p ∈ K := hjr ▸ Set.mem_range_self p
      rw [hKeq] at hp
      rw [Scheme.Hom.comp_apply]
      exact hp)
    rw [this, Over.w j]
  have hPfst : Set.range (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) = K := by
    rw [Scheme.Pullback.range_fst, hKeq]
  have hfin' : IsFinite (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  have het' : Etale (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  have hci : IsClosedImmersion (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  refine ⟨⟨Over.mk (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left : _ ⟶ S),
    Over.homMk (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) (by
      change _ = pullback.snd _ _
      rw [← Over.w ψ, ← Category.assoc, pullback.condition, Category.assoc, hew]
      exact Category.comp_id _),
    hfin', het', hci, hPfst⟩, ?_⟩
  intro hred C j hCet hj hjr
  have hCred : IsReduced C.left := GlobalTheory.isReduced_of_smooth_of_isReduced C.hom
  have hsq := hsqS C j hCred hjr
  have hred' : IsReduced (𝟙_ (Over S)).left := hred
  have hPred : IsReduced (pullback ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left)
  let φ : C.left ⟶ pullback ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left := pullback.lift j.left C.hom hsq
  have hφ1 : φ ≫ pullback.fst _ _ = j.left := pullback.lift_fst _ _ _
  have hφci : IsClosedImmersion φ := by
    have : IsClosedImmersion (φ ≫ pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) := by
      rw [hφ1]; exact hj
    exact IsClosedImmersion.of_comp φ (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left)
  have hφs : Surjective φ := ⟨fun r => by
    have hr : pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left r ∈ Set.range j.left := by
      rw [hjr, ← hPfst]; exact Set.mem_range_self r
    obtain ⟨c, hc⟩ := hr
    refine ⟨c, (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ1, hc]⟩
  have hφi : IsIso φ := isIso_of_isClosedImmersion_of_surjective φ
  have HS : IsPullback j.left (toUnit C).left ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    rw [htu C]
    exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso φ) hφ1 (pullback.lift_snd _ _ _)
  have hw : j ≫ ψ = toUnit C ≫ η[G'] := by
    ext1
    change j.left ≫ ψ.left = (toUnit C).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left
    rw [htu C]; exact hsq
  exact IsPullback.of_map (Over.forget S) hw HS

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGrpPullbackRetraction
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

def translInvIso {S : Scheme.{0}} (B : Over S) [GrpObj B] (c : 𝟙_ (Over S) ⟶ B) : B ≅ B where
  hom := 𝟙 B * (toUnit B ≫ c)⁻¹
  inv := 𝟙 B * (toUnit B ≫ c)
  hom_inv_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, inv_mul_cancel_right]
  inv_hom_id := by
    rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, mul_inv_cancel_right]

theorem comp_translInvIso_hom {S : Scheme.{0}} {B T : Over S} [GrpObj B] (c : 𝟙_ (Over S) ⟶ B) (x : T ⟶ B) :
    x ≫ (translInvIso B c).hom = x * (toUnit T ≫ c)⁻¹ := by
  simp [translInvIso, MonObj.comp_mul, GrpObj.comp_inv]

theorem unit_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw : (η[G'].left ≫ φ) ≫ G.hom = (Over.mk ((𝟙_ (Over S')).hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let u : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) hw
  have hη : (η[G'] : 𝟙_ (Over S') ⟶ G') * η[G'] = η[G'] := by
    rw [MonObj.one_eq_one]
    exact _root_.one_mul _
  have huu : u * u = u := by
    ext1
    rw [h.2 _ η[G'] η[G'] u u rfl rfl, hη]
    rfl
  have hu1 : u = 1 := mul_eq_left.mp huu
  have := congrArg (fun v => CommaMorphism.left v) hu1
  simpa [u, Hom.one_def] using this

theorem exists_isGrpPullback_retraction (rig : Out.RigiditySt) {S S' : Scheme.{0}} (A₀ : Over S) [GrpObj A₀]
    (A' : Over S') [GrpObj A'] (f : S' ⟶ S) (i : S ⟶ S') (ρ₀ : A'.left ⟶ A₀.left) (j : A₀.left ⟶ A'.left)
    (h₀ : IsAbelianScheme A₀) (h' : IsAbelianScheme A') (hj : IsGrpPullback A₀ A' i j)
    (hρ : IsPullback ρ₀ A'.hom A₀.hom f) (hjρ : j ≫ ρ₀ = 𝟙 _) :
    ∃ ρ, IsGrpPullback A' A₀ f ρ ∧ j ≫ ρ = 𝟙 _ := by
  let adj := Over.mapPullbackAdj f
  let B : Over S' := Over.mk (pullback.snd A₀.hom f)
  let F : (Over S')ᵒᵖ ⥤ GrpCat := (Over.map f).op ⋙ yonedaGrpObj A₀
  let α : (F ⋙ forget _).RepresentableBy B :=
    { homEquiv := (adj.homEquiv _ _).symm
      homEquiv_comp := fun g h => (adj.representableBy A₀).homEquiv_comp g h }
  let _ : GrpObj B := GrpObj.ofRepresentableBy B F α
  let E : ∀ T : Over S', (T ⟶ B) ≃ ((Over.map f).obj T ⟶ A₀) := fun T => (adj.homEquiv T A₀).symm
  have hmul : ∀ {T : Over S'} (x y : T ⟶ B), E T (x * y) = E T x * E T y := by
    intro T x y
    exact ((yonedaGrpObjIsoOfRepresentableBy B F α).hom.app (Opposite.op T)).hom.map_mul x y
  have hinv : ∀ {T : Over S'} (x : T ⟶ B), E T x⁻¹ = (E T x)⁻¹ := by
    intro T x
    exact ((yonedaGrpObjIsoOfRepresentableBy B F α).hom.app (Opposite.op T)).hom.map_inv x
  have hleft : ∀ {T : Over S'} (x : T ⟶ B), (E T x).left = x.left ≫ pullback.fst A₀.hom f :=
    fun x => rfl
  have hB : IsGrpPullback B A₀ f (pullback.fst A₀.hom f) := by
    refine ⟨IsPullback.of_hasPullback A₀.hom f, ?_⟩
    intro T x y x₁ y₁ hx hy
    have ex : x₁ = E T x := by ext1; rw [hx, hleft]
    have ey : y₁ = E T y := by ext1; rw [hy, hleft]
    rw [ex, ey, ← hmul, hleft]
  have hBab : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback h₀ hB
  let x₀ : (Over.map f).obj A' ⟶ A₀ := Over.homMk ρ₀ (by rw [hρ.w]; rfl)
  let m₀ : A' ⟶ B := (E A').symm x₀
  have hm₀ : m₀.left ≫ pullback.fst A₀.hom f = ρ₀ := by
    rw [← hleft]
    change (E A' ((E A').symm x₀)).left = ρ₀
    rw [Equiv.apply_symm_apply]
    rfl
  let c : 𝟙_ (Over S') ⟶ B := η[A'] ≫ m₀
  let m : A' ⟶ B := m₀ ≫ (translInvIso B c).hom
  have hm : m = m₀ * (toUnit A' ≫ c)⁻¹ := comp_translInvIso_hom c m₀
  have hm1 : η[A'] ≫ m = η[B] := by
    rw [← Category.assoc, comp_translInvIso_hom, MonObj.one_eq_one, toUnit_unit, Category.id_comp]
    exact _root_.mul_inv_cancel c
  have : IsMonHom m := rig S' A' B h' hBab m hm1
  refine ⟨m.left ≫ pullback.fst A₀.hom f, ⟨?_, ?_⟩, ?_⟩
  · have h1 : IsIso m₀.left := by
      have e : m₀.left = hρ.isoPullback.hom := by
        apply pullback.hom_ext
        · rw [IsPullback.isoPullback_hom_fst]; exact hm₀
        · rw [IsPullback.isoPullback_hom_snd]; exact Over.w m₀
      rw [e]; infer_instance
    have h2 : IsIso (translInvIso B c).hom.left :=
      inferInstanceAs (IsIso ((Over.forget S').map (translInvIso B c).hom))
    have h3 : IsIso m.left := by
      change IsIso (m₀.left ≫ (translInvIso B c).hom.left)
      infer_instance
    have sq : IsPullback m.left A'.hom B.hom (𝟙 S') :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w m, Category.comp_id]⟩
    have := sq.paste_horiz (IsPullback.of_hasPullback A₀.hom f)
    rwa [Category.id_comp] at this
  · intro T x y x₁ y₁ hx hy
    rw [hB.2 T (x ≫ m) (y ≫ m) x₁ y₁ (by rw [hx, ← Category.assoc]; rfl)
      (by rw [hy, ← Category.assoc]; rfl), ← MonObj.mul_comp, ← Category.assoc]
    rfl
  · have hJ : j ≫ ((Over.map f).obj A').hom = A₀.hom := by
      change j ≫ A'.hom ≫ f = A₀.hom
      rw [← hρ.w, ← Category.assoc, hjρ, Category.id_comp]
    let J : A₀ ⟶ (Over.map f).obj A' := Over.homMk j hJ
    have hρm : m.left ≫ pullback.fst A₀.hom f = (x₀ * (E A' (toUnit A' ≫ c))⁻¹).left := by
      rw [← hleft, hm, hmul, hinv, Equiv.apply_symm_apply]
    have hc : c.left ≫ pullback.fst A₀.hom f = η[A'].left ≫ ρ₀ := by
      change (η[A'].left ≫ m₀.left) ≫ _ = _
      rw [Category.assoc, hm₀]
    have hz : J ≫ E A' (toUnit A' ≫ c) = 1 := by
      ext1
      change j ≫ (A'.hom ≫ c.left) ≫ pullback.fst A₀.hom f = A₀.hom ≫ η[A₀].left
      rw [Category.assoc, hc, ← Category.assoc j, hj.1.w]
      simp only [Category.assoc]
      rw [← Category.assoc i, ← unit_left_comp hj, Category.assoc, hjρ, Category.comp_id]
    have hJx : J ≫ x₀ = 𝟙 A₀ := by
      ext1
      exact hjρ
    calc j ≫ m.left ≫ pullback.fst A₀.hom f = (J ≫ (x₀ * (E A' (toUnit A' ≫ c))⁻¹)).left := by
          rw [hρm]; rfl
      _ = 𝟙 A₀.left := by
          rw [MonObj.comp_mul, GrpObj.comp_inv, hJx, hz, _root_.inv_one, _root_.mul_one]; rfl

theorem exists_isConst_of_isPullback :
    Out.Laws → ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ₀ : A'.left ⟶ A₀.left) (j : A₀.left ⟶ A'.left), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → IsPullback ρ₀ A'.hom A₀.hom (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ₀ = 𝟙 _ → ∃ ρ, IsConst A' A₀ ρ j := by
  intro hL A₀ _ A' _ ρ₀ j h₀ h' hj hρ hjρ
  obtain ⟨ρ, hρ', hjρ'⟩ := exists_isGrpPullback_retraction hL.rigidity A₀ A' _ _ ρ₀ j h₀ h' hj hρ hjρ
  exact ⟨ρ, by unfold IsConst; exact ⟨hρ', hj, hjρ'⟩⟩

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsHeckeIsog
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

def IsHeckeIsog (o o' : Obj D l b s) (p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.t.act.act a ≫ ψ = ψ ≫ o'.t.act.act a) ∧
  (∀ y : 𝟙_ (Over (Sp k)) ⟶ o'.t.G, ∃ x, x ≫ ψ = y) ∧ (∀ x, x ≫ ψ = 1 ↔ x ∈ C) ∧
  (∀ (n : ℕ) (x x' : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (c : kˣ), n.Coprime p → Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) →
    Out.WeilIs o'.t.G o'.t.PP.L n (x ≫ ψ) (x' ≫ ψ) (unitOn (c ^ (p ^ 2)))) ∧
  ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a, o.eta (p' • a) ≫ ψ = o'.eta a ∧ o.etaA (p' • a) ≫ ψ = o'.etaA a

theorem exists_inv_mod {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) : ∃ p', p * p' ≡ 1 [MOD n] := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
    (by rintro rfl; exact h (dvd_zero p))
  exact ⟨m, hm⟩

theorem natCast_M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_inf h).1

theorem eq_of_modEq {A Q : Type} [AddCommGroup A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c) {n : ℕ}
    (hn : ∀ a, f (n • a) = 1) {p₁ p₂ : ℕ} (h : p₁ ≡ p₂ [MOD n]) (a : A) : f (p₁ • a) = f (p₂ • a) := by
  have key : ∀ q : ℕ, f (q • a) = f ((q % n) • a) := fun q => by
    conv_lhs => rw [← Nat.mod_add_div q n, add_nsmul, hf, mul_nsmul', hn, _root_.mul_one]
  rw [key p₁, key p₂, h]

theorem eta_M (o : Obj D l b s) (a : D.La) : o.eta (l.M • a) = 1 :=
  o.eta_ker _ (by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top)

theorem modEq_of_inv {p p₁ p₂ n : ℕ} (h₁ : p * p₁ ≡ 1 [MOD n]) (h₂ : p * p₂ ≡ 1 [MOD n]) : p₁ ≡ p₂ [MOD n] := by
  calc p₁ = p₁ * 1 := (Nat.mul_one _).symm
    _ ≡ p₁ * (p * p₂) [MOD n] := h₂.symm.mul_left _
    _ = (p * p₁) * p₂ := by ring
    _ ≡ 1 * p₂ [MOD n] := h₁.mul_right _
    _ = p₂ := Nat.one_mul _

theorem comp_act_natCast {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) {T : Over S}
    (x : T ⟶ G) (n : ℕ) : x ≫ a.act (n : O) = x ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero, left_eq_mul.1 h, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, a.add, MonObj.comp_mul, ih, a.one, Category.comp_id, pow_succ]

set_option maxHeartbeats 400000 in

theorem exists_isHeckeIsog [IsAlgClosed k] [CharZero k] (hL : Out.Laws)
    (hfacts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L)
    (hTate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) (k : Type) [Field k] (Q Q' : Type) [CommGroup Q] [CommGroup Q'] (act : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → kˣ → Prop) (I : TateIso D k Q act e) (ψ : Q →* Q'), 𝔓.IsMaximal → 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ 𝔓 → Function.Surjective ψ → (∀ a x, ψ (act a x) = act' a (ψ x)) → (∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → ∀ x, x ^ p = 1 → (∀ a ∈ J, act a x = 1) → ψ x = 1) → (∀ x, ψ x = 1 → x ^ p ^ 2 = 1 ∧ ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), act a x = 1) → (∀ x y, ψ x = 1 → ψ y = 1 → e (p ^ 2) x y 1) → Nat.card ψ.ker = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → (∀ n x y c, 0 < n → ψ x ^ n = 1 → ψ y ^ n = 1 → e (n * p ^ 2) x y c → e' n (ψ x) (ψ y) c) → ∃ I' : TateIso D k Q' act' e', I'.ζ = I.ζ ∧ ∀ n p' : ℕ, 0 < n → p * p' ≡ 1 [MOD n] → ∀ a, I'.ev n a = ψ (I.ev n (p' • a)))
    (hQuot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left))
    (hWeil : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (L : LB A.left) (M : LB B.left) (d : ℕ) (n : ℤ) (T : Over S) (x y : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom ψ → LBIso (lbPow L d) (M.pull ψ.left) → Out.WeilIs B M n (x ≫ ψ) (y ≫ ψ) c' → Out.WeilIs A L (n * d) x y c' ∧ (Out.WeilIs A L n x y c → c' = c ^ d))
    (hLie : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult a x τ n ↔ LieMult b x τ n)
    (o : Obj D l b s) (𝔓 : Ideal (𝓞 E)) (p : ℕ) (h𝔓 : 𝔓.IsMaximal)
    (hco : 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : p.Prime) (hp𝔓 : (p : 𝓞 E) ∈ 𝔓) (hpM : ¬ p ∣ l.M')
    (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)) (c₁ : ∀ x ∈ C, ∀ a, x ≫ o.t.act.act a ∈ C)
    (c₂ : ∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → ∀ x, (∀ a ∈ J, x ≫ o.t.act.act a = 1) → x ∈ C)
    (c₃ : ∀ x ∈ C, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), x ≫ o.t.act.act a = 1)
    (c₄ : ∀ x ∈ C, ∀ y ∈ C, Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1)
    (c₅ : Nat.card C = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) :
    (∀ x ∈ C, x ^ p ^ 2 = 1) ∧ ∃ (o' : Obj D l b s) (ψ : o.t.G ⟶ o'.t.G), IsHeckeIsog o o' p C ψ ∧
      IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left := by
  have hC : ∀ x ∈ C, x ^ p ^ 2 = 1 := fun x hx => by
    rw [← comp_act_natCast o.t.act]
    refine c₃ x hx _ ?_
    rw [Nat.cast_pow, pow_two]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp𝔓
    rwa [map_natCast] at this
  refine ⟨hC, ?_⟩
  obtain ⟨hab, hdim, -, -⟩ := hfacts E H D l B b _ s o
  obtain ⟨t', ψ, hpr, ham, hkt, hhom, hfin, het, hsur, hker, hlin, hiso⟩ :=
    hQuot E H k o.t _ p C hp.pos o.proper hdim o.ample o.ktriv c₁ hC c₄ c₅
  obtain ⟨g', hg'⟩ := exists_dim t'
  let P := polOf o.t o.proper o.ample o.ktriv hdim
  let P' := polOf t' hpr ham hkt hg'
  have hab' := isAbelianScheme_of_proper t' hpr
  have := o.proper
  have hW := fun (n : ℤ) (T : Over (Sp k)) (x y : T ⟶ o.t.G) c c' =>
    hWeil _ o.t.G t'.G ψ o.t.PP.L t'.PP.L (p ^ 2) n T x y c c' hab hab' o.t.PP.isLB t'.PP.isLB hhom hiso
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  have hpow : IsMonHom (𝟙 o.t.G ^ p ^ 2) := by
    rw [← comp_act_natCast o.t.act, Category.id_comp]; exact o.t.act.hom _
  obtain ⟨gm₀, hgm⟩ := exists_fac hab.smooth ψ (𝟙 o.t.G ^ p ^ 2) fun x hx => by
    rw [MonObj.comp_pow, Category.comp_id]; exact hC x ((hker x).1 hx)
  have hgm₁ : ∀ (T : Over (Sp k)) (x : T ⟶ o.t.G), x ≫ ψ = 1 → x ^ p ^ 2 = 1 := fun T x hx => by
    calc x ^ p ^ 2 = (x ≫ ψ) ≫ gm₀ := by rw [Category.assoc, hgm, MonObj.comp_pow, Category.comp_id]
      _ = (1 ≫ ψ) ≫ gm₀ := by rw [hx, MonObj.one_comp ψ]
      _ = 1 := by rw [Category.assoc, hgm, MonObj.one_comp]
  have hMM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hAM : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  let o' : Obj D l b s :=
    { t := t', proper := hpr, ample := ham, ktriv := hkt
      eta := fun a => o.eta (p₀ • a) ≫ ψ
      eta_add := fun a c => by rw [smul_add, o.eta_add, MonObj.mul_comp]
      eta_ker := fun a ha => by rw [o.eta_ker _ (nsmul_mem ha _), MonObj.one_comp]
      etaA := fun a => o.etaA (p₀ • a) ≫ ψ
      etaA_add := fun a c => by rw [smul_add, o.etaA_add, MonObj.mul_comp]
      etaA_ker := fun a => by rw [smul_comm, o.etaA_ker, MonObj.one_comp]
      geom := by
        intro K _ _ x β hx
        obtain ⟨hdet, I, hζ, hA, hM⟩ := o.geom K x β hx
        refine ⟨fun τ => ?_, ?_⟩
        · simp only [← hLie _ _ _ _ ψ o.t.act t'.act hhom het hlin K x τ]
          exact hdet τ
        have hK : ∀ n : ℕ, 0 < n → (n : K) ≠ 0 := fun n hn => by
          have := ((b.unit n hn).map β).ne_zero
          rwa [map_natCast] at this
        let ψx : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ t'.G) :=
          MonoidHom.mk' (fun z => z ≫ ψ) fun a c => MonObj.mul_comp a c ψ
        have desc : ∀ (n : ℕ) (z : Over.mk x ⟶ o.t.G), 0 < n → z ^ n = 1 →
            ∃ z₀ : 𝟙_ (Over (Sp k)) ⟶ o.t.G, toUnit (Over.mk x) ≫ z₀ = z := fun n z hn hz =>
          exists_of_torsion hL.mulN P x (Nat.cast_ne_zero.2 hn.ne') (hK n hn) z hz
        have one : ∀ {G : Over (Sp k)} [GrpObj G] (z₀ : 𝟙_ (Over (Sp k)) ⟶ G),
            toUnit (Over.mk x) ≫ z₀ = 1 → z₀ = 1 := fun z₀ h =>
          toUnit_comp_injective x _ (h.trans (MonObj.comp_one _).symm)
        have kerd : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 → ∃ z₀ ∈ C, toUnit (Over.mk x) ≫ z₀ = z := fun z hz => by
          obtain ⟨z₀, rfl⟩ := desc _ z (pow_pos hp.pos 2) (hgm₁ _ z hz)
          exact ⟨z₀, (hker z₀).1 (one _ ((Category.assoc _ _ _).symm.trans hz)), rfl⟩
        have uniq : ∀ (n : ℕ) (z w : Over.mk x ⟶ o.t.G) (c c' : Kˣ), z ^ n = 1 → w ^ n = 1 →
            Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c) → Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c') → c = c' :=
          fun n z w c c' hz hw h h' => (unitOn_bijective K).1 (((hL.weil _ P n _).1 z w hz hw).unique h h')
        have iso : ∀ z w : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 → w ≫ ψ = 1 →
            Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w (unitOn (1 : Kˣ)) := fun z w hz hw => by
          have h₁ : Out.WeilIs t'.G t'.PP.L ((1 : ℕ) : ℤ) (1 : Over.mk x ⟶ t'.G) 1 1 :=
            (hL.weil _ P' 1 (Over.mk x)).2.2.1 1 (one_pow _)
          have h₀ : Out.WeilIs t'.G t'.PP.L ((1 : ℕ) : ℤ) (z ≫ ψ) (w ≫ ψ) 1 := by rw [hz, hw]; exact h₁
          have h₂ := (hW ((1 : ℕ) : ℤ) _ z w 1 1 h₀).1
          rw [Nat.cast_one, _root_.one_mul] at h₂
          exact (congrArg (Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w) unitOn_one).mpr h₂
        obtain ⟨I', hζ', hev⟩ := hTate E H D 𝔓 p K _ _ _ (fun a g => g ≫ t'.act.act a) _
          (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c)) I ψx h𝔓 hco hp hp𝔓
          (fun y => exists_lift_pt ψ x y)
          (fun a z => by
            show (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
            rw [Category.assoc, hlin, Category.assoc])
          (fun J hJ z hz hz' => by
            obtain ⟨z₀, rfl⟩ := desc _ z hp.pos hz
            show (_ ≫ z₀) ≫ ψ = 1
            rw [Category.assoc, (hker z₀).2 (c₂ J hJ z₀ fun a ha =>
              one _ ((Category.assoc _ _ _).symm.trans (hz' a ha))), MonObj.comp_one])
          (fun z hz => ⟨hgm₁ _ z hz, fun a ha => by
            obtain ⟨z₀, h₀, rfl⟩ := kerd z hz
            show (_ ≫ z₀) ≫ _ = 1
            rw [Category.assoc, c₃ z₀ h₀ a ha, MonObj.comp_one]⟩)
          (fun z w hz hw => iso z w hz hw)
          (by
            rw [← c₅]
            refine (Nat.card_congr (Equiv.ofBijective (fun z : C => (⟨toUnit (Over.mk x) ≫ z.1, by
              show (_ ≫ z.1) ≫ ψ = 1
              rw [Category.assoc, (hker _).2 z.2, MonObj.comp_one]⟩ : ψx.ker)) ⟨fun a c h =>
                Subtype.ext (toUnit_comp_injective x _ (congrArg Subtype.val h)), fun z => ?_⟩)).symm
            obtain ⟨z₀, h₀, e⟩ := kerd z.1 z.2
            exact ⟨⟨z₀, h₀⟩, Subtype.ext e⟩)
          (fun n z w c c' _ hz hw h h' => uniq n z w c c' hz hw h h')
          (fun n z w c hn hz hw h => by
            obtain ⟨c', hc', -⟩ := (hL.weil _ P' n (Over.mk x)).1 (z ≫ ψ) (w ≫ ψ) hz hw
            obtain ⟨c', rfl⟩ := (unitOn_bijective K).2 c'
            have h₂ := (hW n _ z w 1 _ hc').1
            rw [← Nat.cast_mul] at h₂
            have t : ∀ u : Over.mk x ⟶ o.t.G, ψx u ^ n = 1 → u ^ (n * p ^ 2) = 1 := fun u hu => by
              rw [pow_mul]; exact hgm₁ _ _ ((map_pow ψx u n).trans hu)
            rw [uniq _ z w c c' (t z hz) (t w hw) h h₂]
            exact hc')
        refine ⟨I', by rw [hζ']; exact hζ, fun a => ?_, fun a ha => ?_⟩
        · rw [hev l.A p₀ l.A_pos (hp₀.of_dvd hAM), ← hA, ← Category.assoc]; rfl
        · rw [hev l.M p₀ (by have := l.three_le; omega) (hp₀.of_dvd hMM), ← hM _ (nsmul_mem ha _), ← Category.assoc]; rfl }
  refine ⟨o', ψ, ⟨hhom, hlin, fun y => exists_lift_pt ψ (𝟙 _) y, hker, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩,
    hfin, het, hsur⟩
  · have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (𝟙_ (Over (Sp k))).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P' n _).1 (x ≫ ψ) (x' ≫ ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (hW n _ x x' _ _ hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · have e := modEq_of_inv hp' hp₀
    exact ⟨congrArg (· ≫ ψ) (eq_of_modEq o.eta o.eta_add (eta_M o) (e.of_dvd hMM) a),
      congrArg (· ≫ ψ) (eq_of_modEq o.etaA o.etaA_add o.etaA_ker (e.of_dvd hAM) a)⟩

end GlobalTheory.HeckePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerMatrixLinearInDerivationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_linear_in_derivation : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  first | exact @GlobalTheory.KS.Lin.ks_linear | exact GlobalTheory.KS.Lin.ks_linear | (intros; apply GlobalTheory.KS.Lin.ks_linear <;> assumption)
end

