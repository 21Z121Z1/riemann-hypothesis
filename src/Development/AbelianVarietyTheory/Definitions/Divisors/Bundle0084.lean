import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

variable {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def ThAt (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {N : ℕ} (f : F.X ⟶ PSpace (cycAway n) N) : Prop :=
  P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ Odd m ∧ 3 ≤ m ∧ IsUnit (m : cycAway n) ∧
    N + 1 = m ^ (4 * (8 * g)) ∧ f ≫ PSpace.str (cycAway n) N = F.s ∧ ThMap P.A P.L rig m (𝟙 F.X) f ∧ IsE8 W

def QFin {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}

def SymE {S : ThetaSys o Ω} (ρ : S.Real) (m : ℕ) {N : ℕ} (e : Fin N → Ω) : Prop :=
  N = m ^ (4 * S.g) ∧ (m : Ω) ≠ 0 ∧ SymAt ρ.P.A ρ.P.L ρ.rig m (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R))
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ S.R.val.toRingHom) e

def SysAt (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) : Prop :=
  β.Finite ∧ Function.Injective β ∧ S.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W ρ.P u ∧
    u ≫ F.s = spMap (algebraMap o S.R) ≫ spMap β

def LevAt (β : cycAway n →+* o) {S : ThetaSys o Ω} (u : Sp S.R ⟶ F.X) (Y : RatModel o Ω) (q : Y.Z ⟶ F.X) : Prop :=
  Geo.Tor.IsNormalScheme Y.Z ∧ IsFinite q ∧ Surjective q ∧ q ≫ F.s = Y.s ≫ spMap β ∧
    Y.pt ≫ q = spMap S.R.val.toRingHom ≫ u

def OpenAt (β : cycAway n →+* o) {S : ThetaSys o Ω} (u : Sp S.R ⟶ F.X) (M : RatModel o Ω) (U : M.Z.Opens)
    (c : U.toScheme ⟶ F.X) : Prop :=
  (U : Set M.Z).Nonempty ∧ IsFinite c ∧ Surjective c ∧ c ≫ F.s = U.ι ≫ M.s ≫ spMap β ∧
    ∀ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt → x ≫ c = spMap S.R.val.toRingHom ≫ u

def MinorAt (S : ThetaSys o Ω) (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) : Prop :=
  X.IsNm S.th ∧ IsProjOver X.s ∧ Geo.Tor.IsNormalScheme X.Z ∧ S.Over₀ M U₀ ∧ S.IsEE M U₀ EE ∧ X.IsHom M (AlgHom.id o Ω) f ∧
    (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab)

def SameScale (M : RatModel o Ω) {I J : Type} (a : I → Ω) (b : J → Ω) (D : ℕ) : Prop :=
  ∀ z i, M.Div a i z → ∃ j, M.Div b j z ∧ a i ^ D / b j ∈ M.O z ∧ b j / a i ^ D ∈ M.O z

theorem ThAt.card {P : PolAV F.X} {rig : LB.Gen (P.L.pull (eSec P.A))} {m N : ℕ} {f : F.X ⟶ PSpace (cycAway n) N}
    (h : ThAt F W P rig m f) : N + 1 = m ^ (4 * (8 * g)) := h.2.2.2.2.2.2.1

theorem SymE.card {S : ThetaSys o Ω} {ρ : S.Real} {m N : ℕ} {e : Fin N → Ω} (h : SymE ρ m e) : N = m ^ (4 * S.g) := h.1

theorem SymE.cast_ne_zero {S : ThetaSys o Ω} {ρ : S.Real} {m N : ℕ} {e : Fin N → Ω} (h : SymE ρ m e) : (m : Ω) ≠ 0 := h.2.1

example {S : ThetaSys o Ω} (ρ : S.Real) {N : ℕ} (e : Fin N → Ω) : ¬ SymE ρ 0 e := fun h => h.cast_ne_zero (by simp)

end GlobalTheory.SiegTh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PullData
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolDeg GlobalTheory.TChart

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def CanonOn (Q : Data R) (W : (Sp R).Opens) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) : Prop :=
  P.IsLB ∧ ∃ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R))
    (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O)
    (inc : G ⟶ G') (pr : G' ⟶ G), (∀ y, PsiUnitOn D'.toPre y W) ∧ IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G ∧ pr ≫ inc = oG.act F.e ∧
      LBIso P ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)

variable {Q : Data R} {W W' : (Sp R).Opens} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {P : LB (G2 G).left}

theorem CanonOn.canon (h : CanonOn Q W G P) : Canon Q G P := by
  obtain ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, -, h⟩ := h
  exact ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, h⟩

theorem CanonOn.mono (h : CanonOn Q W G P) (hW : W' ≤ W) : CanonOn Q W' G P := by
  obtain ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, hψ, h⟩ := h
  exact ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, fun y j V hV hU => hψ y j V hV (hU.trans hW), h⟩

section Pull

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def PullData (Q : Data R) (θ : R →+* V) (Q' : Data V) (e : Q'.X ≃+ Q.X) : Prop :=
  ∃ (β : Q'.B.left ⟶ Q.B.left) (β₂ : (G2 Q'.B).left ⟶ (G2 Q.B).left)
    (w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback Q'.B Q.B (spMap θ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (e a)).left) ∧
    ∀ a b, ∃ (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c (e a)) (Q.c (e b))) negε)) (x y : R) (k : (FractionRing R)ˣ)
      (k' : (FractionRing V)ˣ), u.IsGen ∧ θ y ≠ 0 ∧
      (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x ∧
      (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) ∧
      (∀ z J, Good Q.M.L z J → val (Q.tau (e a) (e b)) (𝟙 _) z J =
        gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) ∧
      ∀ z J J', Good Q.M.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' =
        gm (𝟙 (TK V).left) z ⊤ (unitOn k') *
          (lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' *
            val u ((TK V).hom ≫ spMap θ) z J)

end Pull

end GlobalTheory.Mum
end
end

