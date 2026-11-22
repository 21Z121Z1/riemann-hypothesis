import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnLawX
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ComposeLinearAction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} [Algebra c.F ℂ]

def anUvec (e' : Fin g ≃ Lt1 Dw) : Lt1 Dw → Fin g → ℂ := fun ℓ j => if j = e'.symm ℓ then 1 else 0

theorem anX_isChart [StarRing (𝓞 E)] (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (y : FrPt Xo c ℂ) (hy : y.x = F.u i P) (e' : Fin g ≃ Lt1 Dw)
    (hder : ∀ ℓ : Lt1 Dw, IsDerivAt0 (anE F i P) (Pi.single (e'.symm ℓ) 1) (y.u ℓ.1 ℓ.2))
    (hPair : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (F.ex i P (anPr 0 v)).left (F.ex i P (anPr 1 v)).left
        ((Over.w (F.ex i P (anPr 0 v))).trans (Over.w (F.ex i P (anPr 1 v))).symm)) :
    IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec e') (anX F i P hP y hy) where
  zero m := anX_zero F i P hP y hy m
  trunc m := anX_trunc F i P hP y hy m
  law m := anX_law_chart F i P hP y hy hPair m
  act m a := anX_act F i P hP y hy m a
  tan ℓ := anX_tan F i P hP y hy (e'.symm ℓ) (y.u ℓ.1 ℓ.2) (hder ℓ)
  basis v := basis_single e' v

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RegUnifCut
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

def RegularSectionNonneg : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V)))
      [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
      (U : Unif (maximalIdeal V) D A G) (k : ℕ), k = 1 →
      ∀ (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (s : U.SecK k),
        GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s
          (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) 1 →
      ∀ E : Fam D.toPre (FractionRing V) k, U.Expands k s E → NuGe D Q (FractionRing V) vK k E 0

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

