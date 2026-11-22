import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.HomExtendsOverDVR
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR

noncomputable abbrev genericPt (T K : Type) [CommRing T] [Field K] [Algebra T K] :
    Spec (.of K) ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T K))

def HomExtendsOverDVR : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (K : Type) [Field K] [Algebra T K] [IsFractionRing T K]
    (G G' : Over (Spec (.of T))) [GrpObj G] [GrpObj G'],
    ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' →
    ∀ f : (Over.pullback (genericPt T K)).obj G ⟶ (Over.pullback (genericPt T K)).obj G',
      IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (genericPt T K)).map F = f

example (T K : Type) [CommRing T] [Field K] [Algebra T K]
    (G G' : Over (Spec (.of T))) [GrpObj G] [GrpObj G'] (F : G ⟶ G') [IsMonHom F] :
    IsMonHom ((Over.pullback (genericPt T K)).map F) := inferInstance

example (h : HomExtendsOverDVR) (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (G : Over (Spec (.of T))) [GrpObj G] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G)
    (F : G ⟶ G) [IsMonHom F] (hF : (Over.pullback (genericPt T (FractionRing T))).map F = 𝟙 _) :
    F = 𝟙 G := by
  obtain ⟨F₀, -, hu⟩ := h T (FractionRing T) G G hG hG (𝟙 _) inferInstance
  rw [hu F ⟨inferInstance, hF⟩, hu (𝟙 G) ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩]

end GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SemiAbelianModels
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels

def IsExtensionByTorus {k : Type} [Field k] {T G B : Over (Spec (CommRingCat.of k))}
    [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsTorus T ∧ IsAbelianScheme B ∧ IsMonHom i ∧ IsMonHom q ∧
    Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
    IsPullback i (toUnit T) q (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B)

noncomputable abbrev fibreAlong {V F : Type} [CommRing V] [CommRing F] (f : V →+* F)
    (G : Over (Spec (CommRingCat.of V))) : Over (Spec (CommRingCat.of F)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj G

def TorusAffineSplitsFinite : Prop :=
  ∀ (k : Type) [Field k] (T : Over (Spec (CommRingCat.of k))) [GrpObj T], IsTorus T →
    IsAffine T.left ∧
      ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
        (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
        (e : fieldBaseChange k L T ≅ splitTorus (Spec (CommRingCat.of L)) X), IsMonHom e.hom

def ResidueExtensionLifts : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (k' : Type) [Field k'] [Algebra (IsLocalRing.ResidueField V) k']
    [Module.Finite (IsLocalRing.ResidueField V) k'],
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V'),
      Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ IsLocalHom (algebraMap V V') ∧
        ∃ e : IsLocalRing.ResidueField V' ≃+* k', ∀ x : V,
          e (IsLocalRing.residue V' (algebraMap V V' x)) =
            algebraMap (IsLocalRing.ResidueField V) k' (IsLocalRing.residue V x)

def ExtensionQuotientAffine : Prop :=
  ∀ (k : Type) [Field k] (T G B : Over (Spec (CommRingCat.of k)))
    [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B),
    IsExtensionByTorus i q → IsAffineHom q.left

def ModelSemiAbelian : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G],
    IsCommMonObj G → Smooth G.hom → IsSeparated G.hom → QuasiCompact G.hom →
    IsAbelianScheme (fibreAlong (algebraMap V K) G) →
    (∃ (T B : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField V))))
      (_ : GrpObj T) (_ : GrpObj B)
      (i : T ⟶ fibreAlong (IsLocalRing.residue V) G) (q : fibreAlong (IsLocalRing.residue V) G ⟶ B),
      IsExtensionByTorus i q) →
    IsSemiAbelian G

def SeamNodes : Prop :=
  TorusAffineSplitsFinite ∧ ResidueExtensionLifts ∧ ExtensionQuotientAffine ∧ ModelSemiAbelian

end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels
end

