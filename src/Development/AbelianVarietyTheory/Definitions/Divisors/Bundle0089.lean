import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FubiniStudyChowHeight

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CanExtOfCharts
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CanExtM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {V : X.Opens}

def IsBdd (c : Chart t V) (h : HdR c.A) : Prop :=
  ∃ v, IsTanAtG t (chart c.U) v ∧ c.HasImage h v

def canSet {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : Chart t V) : Set (HdR c.A) :=
  {h | IsBdd c h ∧ ∀ D ∈ logDer s (Scheme.IdealSheafData.vanishingIdeal V.compl) c.U, ∀ D' : Derivation ℤ c.S c.S,
    (∀ r, D' (algebraMap Γ(X, c.U.1) c.S r) = algebraMap Γ(X, c.U.1) c.S (D r)) → ∀ k, IsNabla D' h k → IsBdd c k}

def canLat {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : Chart t V) : Submodule Γ(X, c.U.1) (HdR c.A) :=
  Submodule.span Γ(X, c.U.1) (canSet s c)

def IsCanAt {K : Type} [CommRing K] (s : X ⟶ Sp K) (t : SAB H X) (V : X.Opens) (x : X) : Prop :=
  ∃ c : Chart t V, x ∈ c.U.1 ∧ IsCanLattice s c (canLat s c)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {cf : Coeff l}

def GoodModel (Y : Model Xo cf (RingHom.id cf.F)) : Prop :=
  SmoothOfRelativeDimension Dw.dim Y.s ∧ ReciprocityTheory.AnForm.R.FinalTheorems.Snc (boundary Y) ∧ HasLogKS Y.t Y.s (interior Y) ∧
    ∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChart Y x

def CanExtOfCharts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), GoodModel Y →
      ∃ L : ∀ ch : Chart Y.t (interior Y), Submodule Γ(Y.X, ch.U.1) (HdR ch.A), IsCanExt Y.s L

end GlobalTheory.CanExtM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKSChart

section Data

variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R)
  (gam : Fin m → LinearMap.BilinForm ℤ Q.X)

def constHom {k : Type} [Field k] (ρ : R →+* DualNumber k) : R →+* DualNumber k :=
  (algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)

def IsUnitPart (y : Q.X) (n : Fin m → ℕ)
    (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c y).left) fun _ => -1)) : Prop :=
  ψ₀.IsGen ∧ (∀ i, gam i y y = 2 * n i) ∧ ∃ e : (FractionRing R)ˣ,
    (e : FractionRing R) = algebraMap R _ (∏ i, t i ^ n i) ∧ ∀ z J, Good Q.P.L z J →
      val (Q.psi y) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn e) * val ψ₀ (toUnit (TK R)).left z J

def IsConstAlong {k : Type} [Field k] (ρ : R →+* DualNumber k) (a : Fin m → k) : Prop :=
  ∃ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left)
    (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) (ℓ : Q.X →+ k)
    (κ : (DualNumber k)ˣ),
    IsGrpPullback B' Q.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ ∧
    (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) ∧
    w.IsGen ∧ (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) ∧
    ∀ y n ψ₀, IsUnitPart Q t gam y n ψ₀ → ∀ e : (DualNumber k)ˣ,
      (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, a i * n i + ℓ y) → ∀ z J, Good Q.P.L z J →
        val ψ₀ (spMap ρ) z J =
          gm (c' y) z _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))) *
            gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn (κ * e)) * val ψ₀ (spMap (constHom ρ)) z J

def IsRigid [IsLocalRing R] : Prop :=
  ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin m → k), (∀ r ∈ maximalIdeal R, (ρ r).fst = 0) →
    (∀ i, ρ (t i) = 0) → IsConstAlong Q t gam ρ a → ∀ r, (ρ r).snd = 0

end Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasRigidChart (Z : Model Xo c β) (x : gen Z) : Prop :=
  ∃ (k : Type) (_ : Field k) (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Z) (t : SAB H (Sp (ChartRing k m d)))
    (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → levelForms H l.M' P.D.toPre.X),
    ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    (FinalTheorems.stalkId (genBdIdeal Z) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom =
      Ideal.span {∏ i, bdParam k m d i} ∧
    (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) ∧
    Nonempty (SABMap t Z.t (ξ ≫ genι Z)) ∧
    IsMonomial P.D.toPre (bdParam k m d) (fun i => gam i) ∧ IsPartOfBasis gam ∧
    IsRigid P.D.toPre (bdParam k m d) (fun i => gam i)

def RigidForFan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧
          SmoothOfRelativeDimension Dw.dim (genStr Y) ∧ FinalTheorems.Snc (genBdIdeal Y) ∧
          (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) ∧
          (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) ∧
          ((GlobalTheory.FlagMod.detOm Y).IsLB → GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf Y k BD)) ∧
          ∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x

end GlobalTheory.LogKSChart
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
section
namespace GlobalTheory.CovTop

structure HypothesesX : Prop where

  ks : GlobalTheory.Published.ToroidalForFanKS

  lie : GlobalTheory.Published.SemiAbelianLieSeminegative

  green : GlobalTheory.Published.GreenCuspidal

  sep : GlobalTheory.Published.PointSeparationPair

  fsch : GlobalTheory.Published.FubiniStudyChowHeight

example (h : HypothesesX) : GlobalTheory.Published.PointSeparationPair ∧ GlobalTheory.Published.GreenCuspidal := ⟨h.sep, h.green⟩

end GlobalTheory.CovTop
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigChart

section Data

variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R)
  (gam : Fin m → LinearMap.BilinForm ℤ Q.X)

def constHom {k : Type} [Field k] (ρ : R →+* DualNumber k) : R →+* DualNumber k :=
  (algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)

def IsUnitTau (y z : Q.X)
    (τ₀ : LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left]
      ![-1, 1, 1, -1])) : Prop :=
  τ₀.IsGen ∧ ∃ e : (FractionRing R)ˣ, (e : FractionRing R) = ∏ i, algebraMap R _ (t i) ^ gam i y z ∧
    ∀ zz J, Good Q.P.L zz J →
      val (Q.tau y z) (𝟙 _) zz J = gm (𝟙 (TK R).left) zz ⊤ (unitOn e) * val τ₀ (toUnit (TK R)).left zz J

def IsConstAlong {k : Type} [Field k] (ρ : R →+* DualNumber k) (a : Fin m → k) : Prop :=
  ∃ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left)
    (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)),
    IsGrpPullback B' Q.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ ∧
    (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) ∧
    w.IsGen ∧ (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) ∧
    ∀ y z τ₀, IsUnitTau Q t gam y z τ₀ → ∀ e : (DualNumber k)ˣ,
      (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, a i * gam i y z) → ∀ zz J, Good Q.P.L zz J →
        val τ₀ (spMap ρ) zz J =
          gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) *
          (gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))))⁻¹ *
          (gm (c' z) zz _ (w.s (fun _ => J (c' z ≫ π₂), fun _ => J (c' z ≫ π₁))))⁻¹ *
          gm (c' 0) zz _ (w.s (fun _ => J (c' 0 ≫ π₂), fun _ => J (c' 0 ≫ π₁))) *
            gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) * val τ₀ (spMap (constHom ρ)) zz J

def IsRigid [IsLocalRing R] : Prop :=
  ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin m → k), (∀ r ∈ maximalIdeal R, (ρ r).fst = 0) →
    (∀ i, ρ (t i) = 0) → IsConstAlong Q t gam ρ a → ∀ r, (ρ r).snd = 0

end Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasRigidChart (Z : Model Xo c β) (x : gen Z) : Prop :=
  ∃ (k : Type) (_ : Field k) (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Z) (t : SAB H (Sp (ChartRing k m d)))
    (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → levelForms H l.M' P.D.toPre.X),
    ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    (FinalTheorems.stalkId (genBdIdeal Z) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom =
      Ideal.span {∏ i, bdParam k m d i} ∧
    (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) ∧
    Nonempty (SABMap t Z.t (ξ ≫ genι Z)) ∧
    IsMonomial P.D.toPre (bdParam k m d) (fun i => gam i) ∧ IsPartOfBasis gam ∧
    IsRigid P.D.toPre (bdParam k m d) (fun i => gam i)

def RigidForFan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧
          SmoothOfRelativeDimension Dw.dim (genStr Y) ∧ FinalTheorems.Snc (genBdIdeal Y) ∧
          (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) ∧
          (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) ∧
          ((GlobalTheory.FlagMod.detOm Y).IsLB → GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf Y k BD)) ∧
          ∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x

end GlobalTheory.RigChart
end
end

