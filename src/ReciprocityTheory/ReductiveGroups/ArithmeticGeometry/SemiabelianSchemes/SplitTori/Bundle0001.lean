import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.IsTorus
section
universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

noncomputable abbrev fieldBaseChange (k Ω : Type u) [Field k] [CommRing Ω] [Algebra k Ω]
    (T : Over (Spec (.of k))) : Over (Spec (.of Ω)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj T

structure IsTorus {k : Type u} [Field k] (T : Over (Spec (.of k))) [GrpObj T] : Prop where
  comm : IsCommMonObj T
  finiteType : LocallyOfFiniteType T.hom
  quasiCompact : QuasiCompact T.hom
  splits : ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra k Ω)
    (X : Type u) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (e : fieldBaseChange k Ω T ≅ splitTorus (Spec (.of Ω)) X), IsMonHom e.hom

end ReciprocityTheory.ChartRestriction.G.Semi
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusIsCommMonObjSt
section
universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

def splitTorus_isCommMonObjSt : Prop :=
  ∀ (S : Scheme.{u}) (X : Type u) [AddCommGroup X], IsCommMonObj (splitTorus S X)

def characters_splitTorusSt : Prop :=
  ∀ (S : Scheme.{u}) [Nonempty S] [ConnectedSpace S] (X : Type u) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X],
    ∃ e : X ≃ characters (splitTorus S X),
      ∀ a b : X, (e (a + b)).1 = lift (e a).1 (e b).1 ≫ μ

def mulN_isMonHomSt : Prop :=
  ∀ (S : Scheme.{u}) (G : Over S) [GrpObj G] [IsCommMonObj G] (m : ℕ), IsMonHom (mulN G m)

end ReciprocityTheory.ChartRestriction.G.Semi
end

