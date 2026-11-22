import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianAmpleAcyclic
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Published

def AbelianAmpleAcyclic : Prop :=
  ∀ (k : Type) [CommRing k] (S : Scheme.{0}) [IsLocallyNoetherian S] [ConnectedSpace S] (p : S ⟶ Sp k) (A : Over S)
    [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → CxForm.IsRelAcyclic (A.hom ≫ p) A.hom L

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.NeronLieSeminegative
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

open GlobalTheory.NeronCurve

def NeronLieSeminegative : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
    ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (N : Over C) [GrpObj N] (φ : A.left ⟶ N.left), IsGrpPullback A N x φ → IsNeron x N → SemiNeg k (Lie N)

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.NeronModelExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

open GlobalTheory.NeronCurve

def NeronModelExists : Prop :=
  ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
    ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
      ∃ (N : Over C) (φ : A.left ⟶ N.left), IsPullback φ A.hom N.hom x ∧ IsNeron x N

end GlobalTheory.Published
end
end

