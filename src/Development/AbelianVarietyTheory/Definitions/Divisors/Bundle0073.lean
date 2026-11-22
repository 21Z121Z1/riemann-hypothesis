import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def Half (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left)
    (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good D.P.L z J' →
      lamVal w (lift (1 : T ⟶ D.P.A) (1 : T ⟶ D.P.A)).left z J J' = 1) ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn (f a b)) =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

theorem Half.refines {Q : Data R} {ρ : R →+* R'} {D : DegPre R'} {e : D.X ≃+ Q.X} (h : Half Q ρ D e fun _ _ => 1) :
    Refines Q ρ D e := by
  obtain ⟨β, β₂, w, h₁, h₂, h₃, -, h₄, h₅⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, fun κ hκ a b z J J' hJ hJ' => ?_⟩
  have := h₅ κ hκ a b z J J' hJ hJ'
  rwa [show unitOn (1 : (FractionRing R')ˣ) = 1 from map_one _, map_one, _root_.mul_one] at this

def rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) : DegPre R :=
  { D with
    psi := fun χ => GlobalTheory.UU.scaleGen (unitOn (g χ)) (D.psi χ)
    psi_gen := fun χ => GlobalTheory.UU.scaleGen_isGen _ (D.psi_gen χ) }

def EvenDefect (D : DegPre R) (h : D.X → (FractionRing R)ˣ) : Prop :=
  ∀ χ z J, Good D.P.L z J →
    val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (h χ)) * val (D.psi χ) (𝟙 _) z J

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

def DefOver {K : Type} [Field K] (k₀ : Subfield K) {Y : Scheme.{0}} (P : Sp K ⟶ Y) : Prop :=
  ∃ P₀ : Sp k₀ ⟶ Y, spMap k₀.subtype ≫ P₀ = P

variable {V : Type} [CommRing V] [IsDomain V]

abbrev Gens (Q : Data V) : Type := ∀ a b : Q.X, LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)

def TauIn (Q : Data V) (τ₀ : Gens Q) {N : ℕ} (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) : Prop :=
  ∀ a b, (τ₀ a b).IsGen ∧ ∃ k : (FractionRing V)ˣ,
    (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ ∀ z J, Good Q.M.L z J →
      val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k) * val (τ₀ a b) (toUnit (TK V)).left z J

def FromBase (Q : Data V) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* V) : Prop :=
  ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
    (w : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ιb) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q.c a).left ≫ β = spMap ιb ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ιb) z J

def UnifOver {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) [IsLocalRing V]
    (ξ : Sp V ⟶ S) (Q : Data V) : Prop :=
  IsCN V ∧ ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : V →+* R'), IsCN R' → Function.Injective ρ →
    ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (A : PolAV (Sp (FractionRing R')))
        (_ : Unif (maximalIdeal R') D A G') (y' : Sp (FractionRing R') ⟶ F.X) (α : A.A.left ⟶ F.univ.A.left)
        (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
        IsSemiAbelian G' ∧ y' ≫ j = jK R' ≫ spMap ρ ≫ ξ ∧ IsGrpPullback A.A F.univ.A y' α ∧
          IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂)

def SepAt (Q : Data V) (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V) {K : Type} [Field K] (ev : V →+* K)
    (k₀ : Subfield K) : Prop :=
  (∀ i, ev (s (.inl i)) = 0) ∧
  (∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left)
      (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap ev ≫ lam ≫ F'.s) →
      IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) →
      ∀ a, DefOver k₀ (spMap ev ≫ (Q.c a).left ≫ β)) ∧
  ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* V), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) → ∀ i, ev (s i) ∈ k₀

def SepSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ →
    ∀ (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), 1 ≤ d →
      (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) Q.X)) (τ₀ : Gens Q),
      Module.finrank ℤ Q.X ≤ g → IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ Q.X)) →
      (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ Q.X) x x) →
      (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) → (∀ k, IsUnit (s (.inr k))) →
      TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k))
        (fun k => (n : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ Q.X)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) → SepAt Q τ₀ s ev k₀

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

abbrev Fld (Z : Scheme.{0}) : Type := ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)

section General

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ}

def IsTr {S : Type} [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (v : TanM (𝟙 (Sp R)) G)
    (w : Sp (DualNumber S) ⟶ G.left) : Prop :=
  ∃ g' v' : tEpsG (g ≫ G.hom) ⟶ G, g'.left = spMap (algebraMap S (DualNumber S)) ≫ g ∧
    v'.left = spMap (dualMap φ) ≫ (tv v).left ∧ (g' * v').left = w

def IsInv (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) : Prop :=
  IsField ⊤ dd ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (w : Sp (DualNumber S) ⟶ G.left)
    (O : G.left.Opens) (f : Γ(G.left, O)), g ≫ G.hom = spMap φ → ⊤ ≤ g ⁻¹ᵁ O → IsTr G φ g v w →
      (valR w O f).snd = valR g O (dd O f)

def IsLift (D : R → R) (W : G.left.Opens) (d : Fld G.left) : Prop :=
  IsField W d ∧ ∀ O, O ≤ W → ∀ r, d O (constFn G.hom O r) = constFn G.hom O (D r)

variable {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R)

def dlg (δ : Fld G.left) (i i' : L.ι) (O : G.left.Opens) : Γ(G.left, O) :=
  δ O (pbT m (L.g i i').val O) * pbT m (L.g i i')⁻¹.val O

def KSRel (Θ : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ (J : Type) (W : J → G.left.Opens) (j : J → L.ι) (d : J → Fld G.left),
    ⨆ i, W i = ⊤ ∧ (∀ i, W i ≤ m ⁻¹ᵁ L.U (j i)) ∧ (∀ i, IsLift G D (W i) (d i)) ∧
    ∀ i i' O, O ≤ W i ⊓ W i' → ∀ f, d i O f - d i' O f =
      ∑ a, ∑ b, constFn G.hom O (Θ a b) * dlg G m L (dd b) (j i) (j i') O * dd a O f

def op (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W)) (k : ℕ)
    (O : G.left.Opens) (f : Γ(G.left, O)) : Γ(G.left, O) :=
  2 * (k : Γ(G.left, O)) * d O f - ∑ a, ∑ b, constFn G.hom O (Θ a b) * dd a O (dd b O f) +
    2 * ∑ a, constFn G.hom O (u a) * dd a O f + (2 * (k : Γ(G.left, O)) ^ 2 * rsT p O + 2 * (k : Γ(G.left, O)) * rsT p' O) * f

structure Heat where

  Θ : Matrix (Fin n) (Fin n) R
  symm : Θᵀ = Θ

  u : Fin n → R

  J : Type

  W : J → G.left.Opens

  j : J → L.ι

  d : J → Fld G.left

  p : ∀ i, Γ(G.left, W i)

  p' : ∀ i, Γ(G.left, W i)
  cover : ⨆ i, W i = ⊤
  le : ∀ i, W i ≤ m ⁻¹ᵁ L.U (j i)
  lift : ∀ i, IsLift G D (W i) (d i)
  glue : ∀ (k : ℕ) i i' O, O ≤ W i ⊓ W i' → ∀ f,
    op G dd Θ u (d i) (p i) (p' i) k O (pbT m (L.g (j i) (j i')).val O ^ k * f) =
      pbT m (L.g (j i) (j i')).val O ^ k * op G dd Θ u (d i') (p i') (p' i') k O f

abbrev SecM {Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ))

variable {G m L dd D}

def Heat.Acts (h : Heat G m L dd D) (k : ℕ) (τ τ' : SecM m L k) : Prop :=
  ∀ i, rsT (τ'.f fun _ => h.j i) (h.W i) =
    op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (rsT (τ.f fun _ => h.j i) (h.W i))

end General

def ringOp {Ω : Type} [CommRing Ω] {n : ℕ} (d : Ω → Ω) (dd : Fin n → Ω → Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω)
    (p p' : Ω) (k : ℕ) (f : Ω) : Ω :=
  2 * (k : Ω) * d f - ∑ a, ∑ b, Θ a b * dd a (dd b f) + 2 * ∑ a, u a * dd a f + (2 * (k : Ω) ^ 2 * p + 2 * (k : Ω) * p') * f

def epsHom {Ω : Type} [CommRing Ω] (δ : Derivation ℤ Ω Ω) : Ω →+* DualNumber Ω where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (δ s)
  map_one' := by ext <;> simp
  map_zero' := by simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm]

def IsValue {X Y : Scheme.{0}} {Ω : Type} [CommRing Ω] (m : Y ⟶ X) (L : LB X) (x : Sp Ω ⟶ Y)
    (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ m)) (k : ℕ) (σ : SecM m L k) (s : Ω) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp Ω) (z : Z) (J), Good L z J →
    sval σ (r ≫ x) z J = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom s) * (val g r z J ^ k).val

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

def IsTerm (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k) : Prop :=
  ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good Q.P.L y J →
    sval τ x.left y J = sval σ (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val

def IsWt (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (a a' : Sp S ⟶ Y.H.left), a = x.left → a' = x'.left → ⊤ ≤ a ⁻¹ᵁ V → ⊤ ≤ a' ⁻¹ᵁ V → x' ≫ Y.q = x ≫ Y.q →
    (∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) →
    valR a' V f = c α * valR a V f

variable {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

def IsBasic : Prop :=
  ∀ i, (∃ V : Q.P.A.left.Opens, h.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h.p i) ∧ IsWt Y 0 _ (h.p' i) ∧
    ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
      IsWt Y α (Y.q.left ⁻¹ᵁ V) (h.d i _ f)

def TActs (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) : Prop :=
  ∃ τ τ', IsTerm Y k α σ τ ∧ IsTerm Y k α σ' τ' ∧ h.Acts k τ τ'

variable (Q) in

def ShiftEq (k : ℕ) (mu α : Q.X) (σ : Q.SecB k α) (σ₁ : Q.SecB k (α + k • mu)) (c : R) (σ₂ : Q.SecB k (α + k • mu)) : Prop :=
  ∀ u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k)), u.IsGen →
    LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α) →
    ∀ z J, Good Q.P.L z J →
      sval σ₁ (DegPre.prB Q (FractionRing R)).left z J =
        (val u (𝟙 _) z J).val * sval σ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left z J +
          gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J

def HasDefect (c : ℕ → Q.X → Q.X → R) : Prop :=
  ∀ (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)), 1 ≤ k →
    ShiftEq Q k mu α σ σ₁ 0 σ₁ → TActs Y h k α σ σ' → TActs Y h k (α + k • mu) σ₁ σ₁' →
      ShiftEq Q k mu α σ' σ₁' (c k mu α) σ₁

end Raynaud

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IdlAlongNeTopOfValOn
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

namespace GlobalTheory.Poinc.Basic₂

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ}

theorem trait_nonneg (T : Trait F) (x : T.D.toPre.X) : 0 ≤ T.β x x := by
  simpa using T.mono.nonneg 0 x

end GlobalTheory.Poinc.Basic₂
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

section Family

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {R : Type} [CommRing R] [IsDomain R]
  (y : Sp (FractionRing R) ⟶ F.X) {G₁ : Over (Sp R)} [GrpObj G₁] (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left)

def IsGenFibre : Prop := IsGrpPullback ((Over.pullback (jK R)).obj G₁) F.univ.A y α₁

def IsUnifAlong {R' : Type} [CommRing R'] [IsDomain R'] {I : Ideal R'} (ρ : R →+* R') {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (π : G'.left ⟶ G₁.left) {D : DegData R' I} {A : PolAV (Sp (FractionRing R'))} (U : Unif I D A G') : Prop :=
  IsGrpPullback G' G₁ (spMap ρ) π ∧
    ∃ (κ : Sp (FractionRing R') ⟶ Sp (FractionRing R)) (πK : pullback G'.hom (jK R') ⟶ pullback G₁.hom (jK R))
      (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      κ ≫ jK R = jK R' ≫ spMap ρ ∧ πK ≫ pullback.fst G₁.hom (jK R) = pullback.fst G'.hom (jK R') ≫ π ∧
        IsGrpPullback A.A F.univ.A (κ ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
        U.gen.hom.left ≫ α = πK ≫ α₁

def IsMumfordFam [IsLocalRing R] (Q : Data R) : Prop :=
  IsCN R ∧ Q.IsPos (maximalIdeal R) ∧
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifAlong F y α₁ ρ π U

variable {F y α₁}

theorem IsMumfordFam.isCN [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) : IsCN R := h.1

theorem IsMumfordFam.isPos [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) : Q.IsPos (maximalIdeal R) := h.2.1

theorem IsMumfordFam.unif [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifAlong F y α₁ ρ π U := h.2.2

end Family

example {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (y : Sp (FractionRing (PowerSeries ℚ)) ⟶ F.X)
    (G₁ : Over (Sp (PowerSeries ℚ))) [GrpObj G₁] (α₁ : pullback G₁.hom (jK (PowerSeries ℚ)) ⟶ F.univ.A.left) :
    ¬ IsMumfordFam F y α₁ (Wit.tate 0) := fun h => Wit.not_isPos_tate_zero h.isPos

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S)

def PreChart [IsOpenImmersion j] (φ : InvFun ℤ) (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (_ : IsDomain R) (b : o →+* R) (ξ : Sp R ⟶ S) (m : ℕ)
    (t : Fin m → R) (Q : Data R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (a : Fin m → ℕ)
    (G₁ : Over (Sp R)) (_ : GrpObj G₁) (y : Sp (FractionRing R) ⟶ F.X) (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left),
    (IsAdicComplete (maximalIdeal R) R ∧ CharZero R ∧ ξ ≫ s = spMap b ∧ ξ (closedPoint R) = x ∧
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) ∧
    (IsRelParam b t ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, t i} ∧
      ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ i, t i ∉ p.asIdeal) ∧
    (IsSemiAbelian G₁ ∧ (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ i, t i ∉ p.asIdeal) ∧ y ≫ j = jK R ≫ ξ ∧ IsGenFibre F y α₁) ∧
    (IsMumfordFam F y α₁ Q ∧ Module.finrank ℤ Q.X ≤ g ∧ IsCone id φ δ ∧ (∀ z, z ≠ 0 → ∃ i, 0 < δ i z z) ∧
      Q.IsMonomialTau t fun i => (n : ℤ) • δ i) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((n : ℤ) • δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, t i ^ a i}

end Charts

section Generic

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_genericMap {ρ : R →+* R'} (hρ : Function.Injective ρ) :
    ∃ κ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ ≫ jK R = jK R' ≫ spMap ρ := by
  have h : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := (IsFractionRing.injective R' _).comp hρ
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing R) h), ?_⟩
  change spMap _ ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  ext r
  simp

omit [IsDomain R] in

theorem ne_zero_of_isRelParam {o : Type} [CommRing o] [IsLocalRing R] {b : o →+* R} {m : ℕ} {t : Fin m → R}
    (h : IsRelParam b t) (i : Fin m) : t i ≠ 0 := fun h0 => by
  have h₁ := h.mem_of_mem_sq (Pi.single i 1) (by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), h0, mul_zero]
    exact zero_mem _) i
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h₁))

end Generic

section Good

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

end Good

section Compare

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o} {j : F.X ⟶ S}
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left} {R : Type} [CommRing R] [IsDomain R]
  {y : Sp (FractionRing R) ⟶ F.X} {G₁ : Over (Sp R)} [GrpObj G₁] {α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left}
  {ξ : Sp R ⟶ S} {π₁ : G₁.left ⟶ G.left}

theorem IsUnifAlong.isUnifOf (h₁ : IsGrpPullback G₁ G ξ π₁) (hy : y ≫ j = jK R ≫ ξ)
    (hα : α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁) {R' : Type} [CommRing R'] [IsDomain R'] {I : Ideal R'} {ρ : R →+* R'}
    {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {π : G'.left ⟶ G₁.left} {D : DegData R' I}
    {A : PolAV (Sp (FractionRing R'))} {U : Unif I D A G'} (h : IsUnifAlong F y α₁ ρ π U) :
    IsUnifOf F j e (spMap ρ ≫ ξ) (π ≫ π₁) U := by
  obtain ⟨hπ, κ, πK, α, α₂, hκ, hK, hA, hsq, hL, hU⟩ := h
  refine ⟨hπ.comp h₁, κ ≫ y, α, α₂, ?_, hA, hsq, hL, ?_⟩
  · rw [Category.assoc, hy, ← Category.assoc, hκ, Category.assoc]
  · rw [← Category.assoc, hU, Category.assoc, hα, ← Category.assoc, hK, Category.assoc]

theorem IsMumfordFam.isMumfordOf [IsLocalRing R] (h₁ : IsGrpPullback G₁ G ξ π₁) (hy : y ≫ j = jK R ≫ ξ)
    (hα : α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁) {Q : Data R} (h : IsMumfordFam F y α₁ Q) : IsMumfordOf F j e ξ Q := by
  refine ⟨h.isCN, h.isPos, fun R' _ _ _ ρ hR hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, A, U, hU⟩ := h.unif R' ρ hR hρ hf D ε hD
  exact ⟨G', inferInstance, inferInstance, π ≫ π₁, A, U, hU.isUnifOf h₁ hy hα⟩

theorem IsGenFibre.exists_isGrpPullback [IsNoetherianRing R] [IsIntegrallyClosed R] (hG : IsSemiAbelian G)
    (he : IsGrpPullback F.univ.A G j e) (hG₁ : IsSemiAbelian G₁) (hy : y ≫ j = jK R ≫ ξ) (h : IsGenFibre F y α₁) :
    ∃ π₁ : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ π₁ ∧ α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁ := by
  have h₀ := isGrpPullback_pullback G ξ
  have h₂ := (isGrpPullback_pullback ((Over.pullback ξ).obj G) (jK R)).comp h₀
  obtain ⟨E, hE, hE'⟩ := grpPullback_iso ((IsGrpPullback.comp h he).congr hy rfl) h₂
  obtain ⟨E₁, ⟨hE₁, hE₂⟩, -⟩ := GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing R) G₁
    ((Over.pullback ξ).obj G) hG₁ (IsSemiAbelian.pullback ξ G hG) E
  refine ⟨E₁.hom.left ≫ pullback.fst G.hom ξ, ((isGrpPullback_of_iso E₁).comp h₀).congr (Category.id_comp _) rfl, ?_⟩
  have h₃ : ((Over.pullback (jK R)).map E₁.hom).left ≫ pullback.fst ((Over.pullback ξ).obj G).hom (jK R) =
      pullback.fst G₁.hom (jK R) ≫ E₁.hom.left := pullback.lift_fst _ _ _
  have h₄ : E.hom = (Over.pullback (jK R)).map E₁.hom := hE₂.symm
  refine hE'.symm.trans ?_
  rw [h₄]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G.hom ξ) h₃).trans (Category.assoc _ _ _))

variable [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}

theorem PreChart.hasPolChart (hG : IsSemiAbelian G) (he : IsGrpPullback F.univ.A G j e) (h : PreChart F s j φ BD d x) :
    HasPolChart F s j e φ BD d x := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, c₁, c₂, ⟨hG₁, -, hy, hα⟩, ⟨hM, c₃⟩, c₄⟩ := h
  have := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  obtain ⟨π₁, h₁, h₂⟩ := hα.exists_isGrpPullback hG he hG₁ hy
  exact ⟨R, inferInstance, inferInstance, inferInstance, b, ξ, m, t, Q, δ, a, c₁, c₂, ⟨hM.isMumfordOf h₁ hy h₂, c₃⟩, c₄⟩

end Compare

end GlobalTheory.PolDeg
end
end

