import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def RZ (H : Host E) (S A : ℕ) : Subring ℂ := Subring.closure {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}

def IsInc {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* ℂ) (i' : R' →+* ℂ) (β : R →+* R') : Prop :=
  ∀ x, i' (β x) = i x

def IsDedFrac {O F : Type} [CommRing O] [Field F] (β : O →+* F) : Prop :=
  (∃ _ : IsDomain O, IsDedekindDomain O) ∧ CharZero O ∧ @IsFractionRing O _ F _ β.toAlgebra

variable {H : Host E}

structure Cpt {U : Scheme.{0}} {F : Type} [Field F] (c : U ⟶ Sp F) (t₀ : SAB H U) {O : Type} [CommRing O]
    (β : O →+* F) where
  X : Scheme.{0}
  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s
  jQ : U ⟶ pullback s (spMap β)
  jQ_over : jQ ≫ pullback.snd _ _ = c
  jQ_open : IsOpenImmersion jQ
  jQ_dense : Dense (Set.range jQ)
  t : SAB H X
  m : SABMap t₀ t (jQ ≫ pullback.fst _ _)
  ab_gen : pullback.fst s (spMap β) ⁻¹' abLocus t.G = Set.range jQ

def AbOpen {X : Scheme.{0}} (G : Over X) : Prop :=
  ∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)

def SplitFib {X : Scheme.{0}} (G : Over X) [GrpObj G] : Prop :=
  ∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)

def HasTheta {X : Scheme.{0}} (G : Over X) (L : LB G.left) : Prop :=
  ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)

def Good {X : Scheme.{0}} (t : SAB H X) : Prop := AbOpen t.G ∧ SplitFib t.G ∧ HasTheta t.G t.PP.L

section

variable {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}

def Cpt.j (C : Cpt c t₀ β) : U ⟶ C.X := C.jQ ≫ pullback.fst _ _

structure Cpt.Above (C' : Cpt c' t₀' β') (C : Cpt c t₀ β) (b : O →+* O') (r : U' ⟶ U) (ν : SABMap t₀' t₀ r) where
  π : C'.X ⟶ C.X
  π_over : π ≫ C.s = C'.s ≫ spMap b
  fin : IsFinite (pullback.lift π C'.s π_over)
  mu : SABMap C'.t C.t π
  j_comm : C'.j ≫ π = r ≫ C.j
  φ_comm : C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ

def Cpt.ExtendsAut (C : Cpt c t₀ β) (r : U ≅ U) (ν : SABMap t₀ t₀ r.hom) : Prop :=
  ∃ (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), ρ.hom ≫ C.s = C.s ∧ C.j ≫ ρ.hom = r.hom ≫ C.j ∧
    C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ

end

variable {D : Datum H}

def ofModel {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Cpt (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) Y.oF.t β :=
  ⟨Y.X, Y.s, Y.normal, Y.proj, Y.flat, Y.jQ, Y.jQ_over, Y.jQ_open, Y.jQ_dense, Y.t, Y.m, Y.ab_gen⟩

def LevComp {l l' : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l' B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} (o' : Obj D l' b' s') (o : Obj D l b s) (r : S' ⟶ S)
    (ν : SABMap o'.t o.t r) : Prop :=
  (∀ a, (o'.eta a ^ (l'.M / l.M)).left ≫ ν.φ = r ≫ (o.eta a).left) ∧
    ∀ a, (o'.etaA a ^ (l'.A / l.A)).left ≫ ν.φ = r ≫ (o.etaA a).left

def SiegData {T : Scheme.{0}} {O : Type} [CommRing O] (sT : T ⟶ Sp O) (t : SAB H T)
    (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) {g p N : ℕ} (Ag : SiegelFamily g p N) (z : ZP p N →+* O)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (cl : T ⟶ pullback Ag.s (spMap z)) : Prop :=
  ∃ (o : SiegPre g N (zetaZP p N) (sT ≫ spMap z)) (φ : o.A.left ⟶ t.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 t.G).left),
    IsGrpPullback o.A t.G (𝟙 T) φ ∧ IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ t.G t.PP.L).pull φ₂) ∧
    (∀ u, (o.lev u).left ≫ φ = (lev (bas u)).left) ∧ cl ≫ pullback.snd _ _ = sT ∧
    SiegPB o Ag.univ (cl ≫ pullback.fst _ _)

structure Top (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) where
  Z : Scheme.{0}
  s : Z ⟶ Sp (RZ H n N)
  normal : IsNormalScheme Z
  proj : IsProjOver s
  flat : Flat s
  t : SAB H Z
  qproj : IsQProjOver (t.G.hom ≫ s)
  good : Good t
  ga : genericPoints Z ⊆ abLocus t.G
  a : ∀ l : Level H, l.A = N → ((Xo l).X ⟶ Z)
  m : ∀ l h, SABMap (Xo l).univ.t t (a l h)
  fin : ∀ l h (β : RZ H n N →+* KA l), IsInc (RZ H n N).subtype (KA l).val.toRingHom β →
    ∃ (W : (pullback s (spMap β)).Opens) (f : (Xo l).X ⟶ W.toScheme),
      (W : Set _) = pullback.fst s (spMap β) ⁻¹' abLocus t.G ∧ IsFinite f ∧ Surjective f ∧
      f ≫ W.ι ≫ pullback.fst _ _ = a l h ∧ f ≫ W.ι ≫ pullback.snd _ _ = (Xo l).s
  compat : ∀ l l' h h' (r : (Xo l').X ⟶ (Xo l).X) (ν : SABMap (Xo l').univ.t (Xo l).univ.t r) (k : KA l →+* KA l'),
    IsInc (KA l).val.toRingHom (KA l').val.toRingHom k → r ≫ (Xo l).s = (Xo l').s ≫ spMap k →
    (∀ x, ((Xo l').univ.etaA x).left ≫ ν.φ = r ≫ ((Xo l).univ.etaA x).left) →
    r ≫ a l h = a l' h' ∧ ν.φ ≫ (m l h).φ = (m l' h').φ
  sym : ∀ l h (r : (Xo l).X ≅ (Xo l).X) (ν : SABMap (Xo l).univ.t (Xo l).univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La)
    (σ : KA l ≃+* KA l), σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ (Xo l).s = (Xo l).s ≫ spMap σ.toRingHom →
    (∀ x, ((Xo l).univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ ((Xo l).univ.etaA x).left) →
    ∃ ρ : Z ≅ Z, a l h ≫ ρ.hom = r.hom ≫ a l h
  U : Z.Opens
  U_eq : (U : Set Z) = abLocus t.G
  MM : Scheme.{0}
  sM : MM ⟶ Sp (RZ H n N)
  tM : SAB H MM
  lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)
  MM_red : IsReduced MM
  MM_flat : Flat sM
  MM_ab : IsProper tM.G.hom
  u : U.toScheme ⟶ MM
  u_over : u ≫ sM = U.ι ≫ s
  u_fin : IsFinite u
  u_surj : Surjective u
  u_gen : ∃ W : MM.Opens, (∀ x : MM, (sM x).asIdeal = ⊥ → x ∈ W) ∧ IsIso (u ∣_ W)
  tU : SAB H U.toScheme
  mU : SABMap tU t U.ι
  mM : SABMap tU tM u
  lev_eq : ∀ l h (a' : (Xo l).X ⟶ U.toScheme) (x : D.La) (y : (Xo l).X ⟶ tU.G.left), a' ≫ U.ι = a l h →
    y ≫ mU.φ = ((Xo l).univ.etaA x).left ≫ (m l h).φ → y ≫ mM.φ = a' ≫ u ≫ (lev x).left
  sieg : ∀ p : ℕ, p.Prime → p ≠ n → ∃ (Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N)
    (bas : (Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) ⊕ Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℤ) ≃ₗ[ℤ] D.La),
    (∀ x y, D.EF (bas x) (bas y) = omegaStd x y) ∧
    ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p N →+* O) (b : RZ H n N →+* O), Function.Injective i →
      IsInc (ZP p N).subtype i z → IsInc (RZ H n N).subtype i b →
      ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ MM) (tT : SAB H T) (ν : SABMap tT tM f)
        (levT : D.La → (𝟙_ (Over T) ⟶ tT.G)), IsPullback f sT sM (spMap b) →
        (∀ x, (levT x).left ≫ ν.φ = f ≫ (lev x).left) →
        ∃ w : T ⟶ pullback Ag.s (spMap z), SiegData sT tT levT Ag z bas w ∧ IsFinite w ∧ FormallyUnramified w

def AuxiliaryInertOddPrime (H : Host E) (n : ℕ) : Prop :=
  n.Prime ∧ Odd n ∧ ¬ IsSquare (-(H.d : ZMod n)) ∧ ¬ (n : ℤ) ∣ NumberField.discr E

structure BaseModel {Xo : ∀ l : Level H, Moduli D l} {n N : ℕ} (T : Top Xo n N) (l₀ : Level H) where
  A_one : l₀.A = 1
  β : RZ H (n * l₀.M) 1 →+* KA l₀
  β_inc : IsInc (RZ H (n * l₀.M) 1).subtype (KA l₀).val.toRingHom β
  C : Cpt (Xo l₀).s (Xo l₀).univ.t β
  good : Good C.t
  acts : ∀ (r : (Xo l₀).X ≅ (Xo l₀).X) (ν : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La),
    r.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν.φ = r.hom ≫ ((Xo l₀).univ.eta x).left) →
    C.ExtendsAut r ν
  l₁ : Level H
  M_eq : l₁.M = l₀.M
  Mb_eq : l₁.Mb = l₀.Mb
  A_eq : l₁.A = N
  β₁ : RZ H (n * l₀.M) N →+* KA l₁
  β₁_inc : IsInc (RZ H (n * l₀.M) N).subtype (KA l₁).val.toRingHom β₁
  C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁
  b : RZ H (n * l₀.M) 1 →+* RZ H (n * l₀.M) N
  b_inc : IsInc (RZ H (n * l₀.M) 1).subtype (RZ H (n * l₀.M) N).subtype b
  r : (Xo l₁).X ⟶ (Xo l₀).X
  ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r
  lev : LevComp (Xo l₁).univ (Xo l₀).univ r ν
  r_surj : Surjective r
  above : C₁.Above C b r ν
  b' : RZ H n N →+* RZ H (n * l₀.M) N
  b'_inc : IsInc (RZ H n N).subtype (RZ H (n * l₀.M) N).subtype b'
  q : C₁.X ⟶ T.Z
  q_over : q ≫ T.s = C₁.s ≫ spMap b'
  q_fin : IsFinite (pullback.lift q C₁.s q_over)
  qm : SABMap C₁.t T.t q
  q_j : C₁.j ≫ q = T.a l₁ A_eq
  q_φ : C₁.m.φ ≫ qm.φ = (T.m l₁ A_eq).φ

def Raises {Xo : ∀ l : Level H, Moduli D l} {n N : ℕ} {T : Top Xo n N} {l₀ l : Level H} (B : BaseModel T l₀)
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model (Xo l) c β) : Prop :=
  ∃ (b : RZ H (n * l₀.M) 1 →+* O) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r),
    IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp β) b ∧ LevComp Y.oF (Xo l₀).univ r ν ∧
    Nonempty ((ofModel Y).Above B.C b r ν)

def IsPrimeToPart (l₀ l : Level H) (p : ℕ) : Prop :=
  l₀.A = 1 ∧ l₀.M = l.M / p ^ l.M.factorization p ∧ l₀.Mb = l.Mb ⊔ Ideal.span {(l₀.M : 𝓞 E)}

structure System (Xo : ∀ l : Level H, Moduli D l) where
  n : Bool → ℕ
  J : Bool → ℕ
  aux : ∀ i, AuxiliaryInertOddPrime H (n i)
  J_pos : ∀ i, 1 ≤ J i
  T : ∀ i, Top Xo (n i) (n i ^ J i)
  B : ∀ i (l₀ : Level H), l₀.A = 1 → BaseModel (T i) l₀
  ch : ℕ → Bool
  ch_ne : ∀ p, n (ch p) ≠ p
  Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W
  raises : ∀ p W hp hW (i : Idx H p), ∃ (l₀ : Level H) (h : IsPrimeToPart l₀ i.l p),
    Raises (B (ch p) l₀ h.1) (Y p W hp hW i)

end GlobalTheory.Models

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
noncomputable section
namespace GlobalTheory.KS
open Classical in

def rsT {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : Γ(Y, O) := if h : O ≤ O₀ then resG Y h s else 0
open Classical in

def pbT {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens) : Γ(Z, O) :=
  if h : O ≤ f ⁻¹ᵁ O₀ then (f.appLE O₀ O h).hom s else 0
variable {K : Type} [Field K] {Y X : Scheme.{0}} {I : Type} {g : ℕ}

abbrev C1 (U : I → Y.Opens) : Type := ∀ i j, Γ(Y, U i ⊓ U j)

def IsCoc (U : I → Y.Opens) (c : C1 U) : Prop :=
  ∀ i j k, rsT (c i j) (U i ⊓ U j ⊓ U k) + rsT (c j k) (U i ⊓ U j ⊓ U k) = rsT (c i k) (U i ⊓ U j ⊓ U k)

def IsCob (U : I → Y.Opens) (c : C1 U) : Prop :=
  ∃ b : ∀ i, Γ(Y, U i), ∀ i j, c i j = rsT (b j) (U i ⊓ U j) - rsT (b i) (U i ⊓ U j)

def Cohom (f : Y ⟶ Y) (U : I → Y.Opens) (c c' : C1 U) : Prop :=
  ∃ b : ∀ i k, Γ(Y, U i ⊓ f ⁻¹ᵁ U k),
    (∀ i i' k, rsT (b i' k) (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k) - rsT (b i k) (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k) =
      rsT (c i i') (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k)) ∧
    ∀ i k k', rsT (b i k) (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k') - rsT (b i k') (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k') =
      pbT f (c' k k') (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k')

def lc (q : Y ⟶ Sp K) {U : I → Y.Opens} (c : Fin g → K) (φ : Fin g → C1 U) : C1 U :=
  fun i j => ∑ a, constFn q (U i ⊓ U j) (c a) * φ a i j

def IsDerK {R : Type} [CommRing R] (x₀ : R →+* K) (D : R → K) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = x₀ a * D b + x₀ b * D a

structure LocDerK {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K)
    (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) : Prop where
  add : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f'
  mul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f
  res : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m ⁻¹ᵁ W')
  base : ∀ W, W ≤ W₀ → ∀ r, d W (constFn p W r) = constFn q (m ⁻¹ᵁ W) (D r)

def IsInvDer {A₀ : Over (Sp K)} [GrpObj A₀] (v : epsR K ⟶ A₀) (dd : ∀ W : A₀.left.Opens, Γ(A₀.left, W) → Γ(A₀.left, W)) : Prop :=
  ∀ (W : A₀.left.Opens) (f : Γ(A₀.left, W)),
    pbT ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀).left f ((snd (epsR K) A₀).left ⁻¹ᵁ W) =
      pbT (snd (epsR K) A₀).left f ((snd (epsR K) A₀).left ⁻¹ᵁ W) +
        constFn (R := DualNumber K) (fst (epsR K) A₀).left _ DualNumber.eps *
          pbT (snd (epsR K) A₀).left (dd W f) ((snd (epsR K) A₀).left ⁻¹ᵁ W)

structure KSCoc {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W : I → X.Opens)
    (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (d : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O))
    (θ : Fin g → C1 (fun i => m ⁻¹ᵁ W i)) : Prop where
  der : ∀ i, LocDerK q p m D (W i) (d i)
  diff : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, d j O f - d i O f = ∑ a, rsT (θ a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)

def IsDlog (m : Y ⟶ X) (L : LB X) (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O))
    (φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)) : Prop :=
  ∀ a i j, pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * φ a i j = dd a _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j))

def IsConstK (A' : Over (Sp (DualNumber K))) [GrpObj A'] (A₀ : Over (Sp K)) [GrpObj A₀] (ρ : A'.left ⟶ A₀.left)
    (j : A₀.left ⟶ A'.left) : Prop :=
  IsGrpPullback A' A₀ (spMap (algebraMap K (DualNumber K))) ρ ∧
    IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j ∧ j ≫ ρ = 𝟙 _
end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
noncomputable section
namespace GlobalTheory.KS

def IsDer {R : Type} [CommRing R] (x₀ : R →+* ℂ) (D : R → ℂ) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = x₀ a * D b + x₀ b * D a

structure PtDer {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  add : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f + f') = δ W f + δ W f'
  mul : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f * f') = valAt' y W f * δ W f' + valAt' y W f' * δ W f
  res : ∀ W W' (h : W' ≤ W), ⊤ ≤ y ⁻¹ᵁ W' → ∀ f, δ W' (resG X h f) = δ W f

structure LocDer {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ)
    (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) : Prop where
  add : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f'
  mul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f
  res : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = resG Y (fun _ hy => h hy) (d W f)
  base : ∀ W, W ≤ W₀ → ∀ r, d W (constFn p W r) = constFn q (m ⁻¹ᵁ W) (D r)
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

def dom (m : A₀.left ⟶ X) (W : X.Opens) : Set (Fin g → ℂ) := {z | ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W}

def fn (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) : ℂ := valAt' ((u.ex z).left ≫ m) W f

structure GoodU (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop where
  ah : u.IsAH Hm χ
  tan₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v
  tan₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v
  endo : ∀ f : A₀ ⟶ A₀, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f
  sec : ∀ (n : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ

structure KSRel {R : Type} [CommRing R] (p : X ⟶ Sp R) (m : A₀.left ⟶ X) (D : R → ℂ) (Θ : Matrix (Fin g) (Fin g) ℂ)
    (s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  der : ∀ z, PtDer ((u.ex z).left ≫ m) (s z)
  base : ∀ z r, s z ⊤ (constFn p ⊤ r) = D r
  hol : ∀ W f, DifferentiableOn ℂ (fun z => s z W f) (dom u m W)
  per : ∀ (l : u.Λ) W f, ∀ z ∈ dom u m W,
    s (z + l) W f = s z W f + fderiv ℂ (fn u m W f) z (Θ.mulVec (star (l : Fin g → ℂ)))

def IsSymm (Hm Θ : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ z w, hermForm Hm (Θ.mulVec (star z)) w = hermForm Hm (Θ.mulVec (star w)) z

def Comm (Θ : Matrix (Fin g) (Fin g) ℂ) (F : (Fin g → ℂ) → (Fin g → ℂ)) : Prop :=
  ∀ z, F (Θ.mulVec (star z)) = Θ.mulVec (star (F z))

def IsConst (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (A₀ : Over (Sp ℂ)) [GrpObj A₀] (ρ : A'.left ⟶ A₀.left)
    (j : A₀.left ⟶ A'.left) : Prop :=
  IsGrpPullback A' A₀ (spMap (algebraMap ℂ (DualNumber ℂ))) ρ ∧
    IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ j ≫ ρ = 𝟙 _
end GlobalTheory.KS
end
end

