import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

def FP (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  Module.Finite R M ∧ Module.Projective R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n

section Formal

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def CohomZeroIsConstants : Prop := ∀ g : C0 F, d0 F g = 0 → ∃! r : R, ∀ T, g T = algebraMap R (F.obj T) r

def WedgeO : Prop :=
  ∃ e : ⋀[R]^2 (CatCoh.H1 F) ≃ₗ[R] CatCoh.H2 F, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup F a b

structure Frame (n : ℕ) where

  w : Fin n → Glob1 F

  δ : Fin n → ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T
  nat : ∀ (i : Fin n) ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ i T' (p1 F φ ω) = mp F φ (δ i T ω)
  sum : ∀ (T : C) (ω : Ω[F.obj T⁄R]), ω = ∑ i, δ i T ω • (w i).1 T

def HasFrame : Prop := ∃ n, Nonempty (Frame F n)

variable {n : ℕ}

def wsum (u v : Fin n → Glob1 F) : W0 F 2 := fun T ↦ ∑ k, wedge R (F.obj T) ((u k).1 T) ((v k).1 T)

def ClRel (w : Glob1 F) (u v : Fin n → Glob1 F) : Prop := ∀ T, dOne R (F.obj T) (w.1 T) = wsum F u v T

def DRel (x : CatCoh.H1 F) (y : Fin n → CatCoh.H1 F) (w : Fin n → Glob1 F) : Prop :=
  ∃ (f : Z1 F) (g : Fin n → Z1 F) (ω : A0 F), CatCoh.H1.mk F f = x ∧ (∀ k, CatCoh.H1.mk F (g k) = y k) ∧
    ∀ ⦃T T' : C⦄ (φ : T ⟶ T'),
      D R (F.obj T') (f.1 T T' φ) = ∑ k, (g k).1 T T' φ • (w k).1 T' + (ω T' - p1 F φ (ω T))

def ObRel (x : CatCoh.H1 F) (u v : Fin n → Glob1 F) : Prop :=
  ∃ (f : Z1 F) (ω : A0 F), CatCoh.H1.mk F f = x ∧
    (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T) + D R (F.obj T') (f.1 T T' φ)) ∧
    ∀ T, dOne R (F.obj T) (ω T) = wsum F u v T

def clAll (h : Closed1 F = ⊤) : Glob1 F →ₗ[R] Hyp1 F :=
  ofForm F ∘ₗ (LinearEquiv.ofTop _ h).symm.toLinearMap

end Formal

section Pull

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

abbrev HO2 (s : X ⟶ Sp R) : Type := CatCoh.H2 (OAff s)

theorem pairRes_pull2_bijective (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : Function.Bijective (pairRes φ s').pull2 := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s') (pairFst φ) H hcov hdir
  exact ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

def pullHO2 : HO2 s →ₛₗ[σ] HO2 s' :=
  (LinearEquiv.ofBijective (pairRes φ s').pull2 (pairRes_pull2_bijective φ s')).symm.toLinearMap.comp
    (pairPull h).pull2

def Red1 (f : C1 (OAff s)) (x : HO1 s') : Prop :=
  ∃ c : Z1 (OPair φ s'), (∀ p q (a : p ⟶ q), c.1 p q a = (pairPull h).α q (f _ _ ((pairPull h).G.map a))) ∧
    CatCoh.H1.mk _ c = (pairRes φ s').pull1 x

def Red2 (w : C2 (OAff s)) (z : HO2 s') : Prop :=
  ∃ c : Z2 (OPair φ s'), (∀ p q r (a : p ⟶ q) (b : q ⟶ r),
      c.1 p q r a b = (pairPull h).α r (w _ _ _ ((pairPull h).G.map a) ((pairPull h).G.map b))) ∧
    CatCoh.H2.mk _ c = (pairRes φ s').pull2 z

def TMul (t : R) (u : HO1 s') (y : HO1 s) : Prop :=
  ∃ (f : C1 (OAff s)) (c : Z1 (OAff s)), c.1 = t • f ∧ CatCoh.H1.mk _ c = y ∧ Red1 h f u

def Bock {R₀ : Type} [CommRing R₀] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {σ₀ : R →+* R₀} {φ₀ : X₀ ⟶ X}
    (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (t : R) (x : HO1 s') (z : HO2 s₀) : Prop :=
  ∃ (f : C1 (OAff s)) (w : C2 (OAff s)), d1 (OAff s) f = t • w ∧ Red1 h f x ∧ Red2 h₀ w z

end Pull

def SmallExt {R R' R₀ : Type} [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) : Prop :=
  Function.Surjective σ ∧ RingHom.ker σ = Ideal.span {t} ∧ Function.Surjective σ₀ ∧ ∀ a, σ₀ a = 0 ↔ a * t = 0

section BaseChange

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

def StructureSheafH1BaseChange : Prop := ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
  (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    ∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c

def StructureSheafH2BaseChange : Prop := ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
  (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c

def UConst : Prop := ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X),
  IsPullback φ s' s (spMap (algebraMap R R')) → CohomZeroIsConstants (OAff s')

abbrev dB (K : CochainComplex (ModuleCat.{0} R) ℕ) (R' : Type) [CommRing R'] [Algebra R R'] (i j : ℕ) :
    R' ⊗[R] K.X i →ₗ[R'] R' ⊗[R] K.X j := (K.d i j).hom.baseChange R'

abbrev ext {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'')
    (M : Type) [AddCommGroup M] [Module R M] : R' ⊗[R] M →ₗ[R] R'' ⊗[R] M := α.toLinearMap.rTensor M

structure Model (K : CochainComplex (ModuleCat.{0} R) ℕ) where

  θ0 : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (_ : IsPullback φ s' s (spMap (algebraMap R R'))),
    LinearMap.ker (dB K R' 0 1) ≃ₗ[R'] LinearMap.ker (d0 (OAff s'))

  one : K.X 0
  θ0_one : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    ∃ e : (1 : R') ⊗ₜ[R] one ∈ LinearMap.ker (dB K R' 0 1), ∀ T, (θ0 h ⟨_, e⟩).1 T = 1

  θ1 : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (_ : IsPullback φ s' s (spMap (algebraMap R R'))), LinearMap.ker (dB K R' 1 2) →ₗ[R'] HO1 s'

  θ2 : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (_ : IsPullback φ s' s (spMap (algebraMap R R'))), LinearMap.ker (dB K R' 2 3) →ₗ[R'] HO2 s'
  exact : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    Function.Surjective (θ1 h) ∧ (∀ z, θ1 h z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' 0 1)) ∧
    Function.Surjective (θ2 h) ∧ ∀ z, θ2 h z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' 1 2)
  nat : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap (algebraMap R R')))
    {R'' : Type} [CommRing R''] [Algebra R R''] {X'' : Scheme.{0}} {s'' : X'' ⟶ Sp R''} {φ' : X'' ⟶ X}
    (h' : IsPullback φ' s'' s (spMap (algebraMap R R''))) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X')
    (w : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' →
    (∀ z z', z'.1 = ext α _ z.1 → θ1 h' z' = pullHO1 w (θ1 h z)) ∧
    ∀ z z', z'.1 = ext α _ z.1 → θ2 h' z' = pullHO2 w (θ2 h z)

def LiftsAt (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R'']
    [Algebra R R''] (α : R' →ₐ[R] R'') (i : ℕ) : Prop :=
  ∀ z : R'' ⊗[R] K.X i, dB K R'' i (i + 1) z = 0 → ∃ (y : R' ⊗[R] K.X i) (b : R'' ⊗[R] K.X (i - 1)),
    dB K R' i (i + 1) y = 0 ∧ z = ext α _ y + dB K R'' (i - 1) i b

end BaseChange

section Over

variable {R : Type} [CommRing R] {Y A : Over (Sp R)}

theorem ovw (f : Y ⟶ A) : f.left ≫ A.hom = Y.hom ≫ spMap (RingHom.id R) := by
  rw [spMap_id, Over.w f]; exact (Category.comp_id _).symm

def pO1 (f : Y ⟶ A) : HO1 A.hom →ₗ[R] HO1 Y.hom := pullHO1 (ovw f)

def structureSheafH2Pullback (f : Y ⟶ A) : HO2 A.hom →ₗ[R] HO2 Y.hom := pullHO2 (ovw f)

def pF (f : Y ⟶ A) : GlobForm A.hom →ₗ[R] GlobForm Y.hom := pullForm (ovw f)

def deRhamH1Pullback (f : Y ⟶ A) : HH1 A.hom →ₗ[R] HH1 Y.hom := pullHH1 (ovw f)

def deRhamH2Pullback (f : Y ⟶ A) : HH2 A.hom →ₗ[R] HH2 Y.hom := pullHH2 (ovw f)

variable (A) [GrpObj A]

def StructureSheafH1Primitive : Prop := ∀ x : HO1 A.hom, pO1 μ[A] x = pO1 (fst A A) x + pO1 (snd A A) x

def PrimF : Prop := ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x

def DeRhamH1Primitive : Prop := ∀ x : HH1 A.hom, deRhamH1Pullback μ[A] x = deRhamH1Pullback (fst A A) x + deRhamH1Pullback (snd A A) x

def NoPrimitiveStructureSheafH2 : Prop := ∀ z : HO2 A.hom, structureSheafH2Pullback μ[A] z = structureSheafH2Pullback (fst A A) z + structureSheafH2Pullback (snd A A) z → z = 0

def AxesVanishingStructureSheafDegOne : Prop := ∀ y : HO1 (A ⊗ A).hom, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 →
  pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0

end Over

def OStr : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    FP R (HO1 A.hom) g ∧ WedgeO (OAff A.hom) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom

example (R : Type) [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (h : ∀ T, Subsingleton Ω[F.obj T⁄R]) : HasFrame F :=
  ⟨0, ⟨⟨Fin.elim0, Fin.elim0, fun i ↦ i.elim0, fun T _ ↦ (h T).elim _ _⟩⟩⟩

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
section
noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def wSub (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) : Submodule D.O D.La :=
  Submodule.span D.O {z | ∃ c ∈ w0 ^ r, ∃ z' : D.La, z = algebraMap (𝓞 D.F) D.O c • z'}

abbrev LevGrp (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) : Type :=
  (D.La ⧸ wSub D w0 r) ≃ₗ[D.O] (D.La ⧸ wSub D w0 r)

def IsEtPlace (b : Base D R) (w0 : Ideal (𝓞 D.F)) : Prop :=
  w0.IsMaximal ∧ (p : 𝓞 D.F) ∈ w0 ∧ (∀ i, Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) = ⊤) ∧
    ∀ (k : Type) [Field k] [CharP k p] (β : R →+* k) (φ : 𝓞 D.F →+* k), RingHom.ker φ = w0 → φ D.ω = β b.ρ

def IsEtLev {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ)
    (lv : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  (∀ x y, lv (x + y) = lv x * lv y) ∧ (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) ∧
    (∀ x ∈ wSub D w0 r, lv x = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (∀ y, toUnit (Over.mk x) ≫ lv y = 1 → y ∈ wSub D w0 r) ∧
      ∀ g : Over.mk x ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
        ∃ y, toUnit (Over.mk x) ≫ lv y = g

structure EtModel (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : Obj b N s
  lv : D.La → (𝟙_ (Over X) ⟶ univ.A)
  isLev : IsEtLev univ w0 r lv
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s') (l : D.La → (𝟙_ (Over S) ⟶ o.A)),
    IsEtLev o w0 r l → ∃! f : S ⟶ X, f ≫ s = s' ∧ ∃ m : ObjMap o univ f, ∀ y, (l y).left ≫ m.φ = f ≫ (lv y).left

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.StarMulOfMulStar
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LKInv

open GlobalTheory.LKTorus

section General

variable (k : Type) [Field k] {B L : Type} [Ring B] [StarRing B] [Algebra k B] [CommRing L] [Algebra k L]

def StConj (γ₀ γ : Bˣ) : Prop :=
  ∃ ν : kˣ, (γ₀ : B) * star (γ₀ : B) = algebraMap k B ν ∧ (γ : B) * star (γ : B) = algebraMap k B ν ∧
    ∃ g : Bˣ, (g : B) * γ₀ = γ * g

variable {k}

theorem star_mul_conj {γ₀ γ g : Bˣ} (n : B) (hn : ∀ x : B, n * x = x * n)
    (h0 : (γ₀ : B) * star (γ₀ : B) = n) (h1 : (γ : B) * star (γ : B) = n) (hg : (g : B) * γ₀ = γ * g) :
    star (g : B) * γ = γ₀ * star (g : B) := by
  have hu : IsUnit (star (γ : B)) := (Units.isUnit γ).star
  apply hu.mul_right_cancel
  calc star (g : B) * γ * star (γ : B) = star (g : B) * n := by rw [mul_assoc, h1]
    _ = n * star (g : B) := (hn _).symm
    _ = γ₀ * star (γ₀ : B) * star (g : B) := by rw [h0]
    _ = γ₀ * star ((g : B) * γ₀) := by rw [star_mul, mul_assoc]
    _ = γ₀ * star ((γ : B) * g) := by rw [hg]
    _ = γ₀ * star (g : B) * star (γ : B) := by rw [star_mul, mul_assoc]

theorem star_mul_self_comm {γ₀ γ g : Bˣ} (n : B) (hn : ∀ x : B, n * x = x * n)
    (h0 : (γ₀ : B) * star (γ₀ : B) = n) (h1 : (γ : B) * star (γ : B) = n) (hg : (g : B) * γ₀ = γ * g) :
    ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B) := by
  rw [Units.val_mul, Units.coe_star, mul_assoc, hg, ← mul_assoc, star_mul_conj n hn h0 h1 hg, mul_assoc]

theorem inv_comm {γ₀ : B} (u : Bˣ) (hu : (u : B) * γ₀ = γ₀ * u) :
    ((u⁻¹ : Bˣ) : B) * γ₀ = γ₀ * ((u⁻¹ : Bˣ) : B) :=
  calc ((u⁻¹ : Bˣ) : B) * γ₀ = ((u⁻¹ : Bˣ) : B) * (γ₀ * u) * ((u⁻¹ : Bˣ) : B) := by
        rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    _ = ((u⁻¹ : Bˣ) : B) * ((u : B) * γ₀) * ((u⁻¹ : Bˣ) : B) := by rw [hu]
    _ = γ₀ * ((u⁻¹ : Bˣ) : B) := by rw [← mul_assoc, Units.inv_mul, one_mul]

def liftUnit (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (u : Bˣ) (hu : (u : B) * γ₀ = γ₀ * u) : Lˣ where
  val := ((hcent u).1 hu).choose
  inv := ((hcent ((u⁻¹ : Bˣ) : B)).1 (inv_comm u hu)).choose
  val_inv := hι (by
    have h1 := ((hcent u).1 hu).choose_spec
    have h2 := ((hcent ((u⁻¹ : Bˣ) : B)).1 (inv_comm u hu)).choose_spec
    rw [map_mul, h1, h2, Units.mul_inv, map_one])
  inv_val := hι (by
    have h1 := ((hcent u).1 hu).choose_spec
    have h2 := ((hcent ((u⁻¹ : Bˣ) : B)).1 (inv_comm u hu)).choose_spec
    rw [map_mul, h1, h2, Units.inv_mul, map_one])

@[simp] theorem ι_liftUnit (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (u : Bˣ) (hu : (u : B) * γ₀ = γ₀ * u) :
    ι ((liftUnit ι hι γ₀ hcent u hu : Lˣ) : L) = u :=
  ((hcent u).1 hu).choose_spec

def cocyc (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[k] L)
    (hc : ∀ a, ι (c a) = star (ι a)) (g : Bˣ) (hg : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B)) :
    fixU k c :=
  ⟨liftUnit ι hι γ₀ hcent (star g * g) hg, hι (by
    rw [hc, ι_liftUnit, Units.val_mul, Units.coe_star, star_mul, star_star])⟩

@[simp] theorem ι_cocyc (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[k] L)
    (hc : ∀ a, ι (c a) = star (ι a)) (g : Bˣ) (hg : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B)) :
    ι (((cocyc ι hι γ₀ hcent c hc g hg : fixU k c) : Lˣ) : L) = star (g : B) * g := by
  simp [cocyc]

section Inv

variable (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : Bˣ)
  (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[k] L) (hc : ∀ a, ι (c a) = star (ι a))

theorem mk_eq_mk_of {c : L →ₐ[k] L} (a b : fixU k c) (t : kˣ) (y : Lˣ)
    (h : ((b : Lˣ) : L) = algebraMap k L t * ((a : Lˣ) : L) * ((y : L) * c y)) :
    (QuotientGroup.mk a : H1 k c) = QuotientGroup.mk b := by
  apply QuotientGroup.eq.2
  rw [GlobalTheory.LKTorus.Model.mem_normSub_iff]
  refine ⟨t, y, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, h]
  calc ((((a : Lˣ))⁻¹ : Lˣ) : L) * (algebraMap k L t * ((a : Lˣ) : L) * ((y : L) * c y))
      = algebraMap k L t * ((y : L) * c y) * ((((a : Lˣ))⁻¹ : Lˣ) * (a : Lˣ) : Lˣ) := by
        rw [Units.val_mul]; ring
    _ = _ := by rw [inv_mul_cancel, Units.val_one, mul_one]

theorem StConj.comm {γ₀ γ : Bˣ} (ν : kˣ) (h0 : (γ₀ : B) * star (γ₀ : B) = algebraMap k B ν)
    (h1 : (γ : B) * star (γ : B) = algebraMap k B ν) {g : Bˣ} (hg : (g : B) * γ₀ = γ * g) :
    ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B) :=
  star_mul_self_comm _ (fun x => Algebra.commutes _ x) h0 h1 hg

def invCls {γ : Bˣ} (h : StConj k γ₀ γ) : H1 k c :=
  QuotientGroup.mk (cocyc ι hι (γ₀ : B) hcent c hc h.choose_spec.2.2.choose
    (StConj.comm h.choose h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.choose_spec))

theorem mk_cocyc_eq {γ : Bˣ} (g g' : Bˣ) (hg : (g : B) * γ₀ = γ * g) (hg' : (g' : B) * γ₀ = γ * g')
    (hgc : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B))
    (hgc' : ((star g' * g' : Bˣ) : B) * γ₀ = γ₀ * ((star g' * g' : Bˣ) : B)) :
    (QuotientGroup.mk (cocyc ι hι (γ₀ : B) hcent c hc g hgc) : H1 k c) =
      QuotientGroup.mk (cocyc ι hι (γ₀ : B) hcent c hc g' hgc') := by
  have hq : ((g⁻¹ * g' : Bˣ) : B) * γ₀ = γ₀ * ((g⁻¹ * g' : Bˣ) : B) := by
    have e : (γ : B) = g * γ₀ * ((g⁻¹ : Bˣ) : B) := by
      calc (γ : B) = γ * g * ((g⁻¹ : Bˣ) : B) := by rw [mul_assoc, Units.mul_inv, mul_one]
        _ = _ := by rw [← hg]
    rw [Units.val_mul, mul_assoc, hg', e]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  set y := liftUnit ι hι (γ₀ : B) hcent (g⁻¹ * g') hq with hy
  have hιy : ι (y : L) = ((g⁻¹ * g' : Bˣ) : B) := ι_liftUnit ι hι _ hcent _ hq
  have hgy : (g' : B) = g * ι (y : L) := by
    rw [hιy, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  set a := cocyc ι hι (γ₀ : B) hcent c hc g hgc with hadef
  have ha : star (g : B) * g = ι (((a : Lˣ)) : L) := by
    rw [hadef, ι_cocyc]
  apply mk_eq_mk_of _ _ 1 y
  apply hι
  rw [ι_cocyc, hgy]
  calc star ((g : B) * ι (y : L)) * ((g : B) * ι (y : L))
      = star (ι (y : L)) * (star (g : B) * g) * ι (y : L) := by rw [star_mul]; simp only [mul_assoc]
    _ = ι (c (y : L) * ((a : Lˣ) : L) * (y : L)) := by rw [← hc, ha, map_mul, map_mul]
    _ = _ := by congr 1; rw [Units.val_one, map_one, one_mul]; ring

theorem invCls_eq {γ : Bˣ} (h : StConj k γ₀ γ) (g : Bˣ) (hg : (g : B) * γ₀ = γ * g)
    (hgc : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B)) :
    invCls ι hι γ₀ hcent c hc h = QuotientGroup.mk (cocyc ι hι (γ₀ : B) hcent c hc g hgc) :=
  mk_cocyc_eq ι hι γ₀ hcent c hc _ g h.choose_spec.2.2.choose_spec hg _ hgc

theorem StConj.refl' (ν : kˣ) (h0 : (γ₀ : B) * star (γ₀ : B) = algebraMap k B ν) : StConj k γ₀ γ₀ :=
  ⟨ν, h0, h0, 1, by simp⟩

theorem invCls_self (h : StConj k γ₀ γ₀) : invCls ι hι γ₀ hcent c hc h = 1 := by
  have h1 : ((star (1 : Bˣ) * 1 : Bˣ) : B) * γ₀ = γ₀ * ((star (1 : Bˣ) * 1 : Bˣ) : B) := by simp
  have e : cocyc ι hι (γ₀ : B) hcent c hc 1 h1 = 1 := by
    ext
    apply hι
    rw [ι_cocyc]
    simp
  rw [invCls_eq ι hι γ₀ hcent c hc h 1 (by simp) h1, e]
  rfl

theorem mul_star_of_star_mul (x : Bˣ) (n : B) (hn : ∀ y : B, n * y = y * n)
    (h : star (x : B) * x = n) : (x : B) * star (x : B) = n := by
  calc (x : B) * star (x : B) = x * (star (x : B) * x) * ((x⁻¹ : Bˣ) : B) := by
        rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    _ = n := by rw [h, mul_assoc, hn, ← mul_assoc, Units.mul_inv, one_mul]

def kerG : Set (H1 k c) :=
  {X | ∃ a : fixU k c, (QuotientGroup.mk a : H1 k c) = X ∧
    ∃ (t : kˣ) (g : Bˣ), ι (algebraMap k L t * ((a : Lˣ) : L)) = star (g : B) * g}

end Inv

end General

section Local

variable (S : Type) [Field S] [CharZero S] {B L : Type} [Ring B] [StarRing B] [Algebra ℚ B] [CommRing L]
  [Algebra ℚ L]

def locMap (ι : L →ₐ[ℚ] B) : S ⊗[ℚ] L →ₐ[S] S ⊗[ℚ] B := Algebra.TensorProduct.map (AlgHom.id S S) ι

def locElt (γ₀ : Bˣ) : (S ⊗[ℚ] B)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] S ⊗[ℚ] B).toMonoidHom γ₀

@[simp] theorem coe_locElt (γ₀ : Bˣ) : ((locElt S γ₀ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) = (1 : S) ⊗ₜ[ℚ] (γ₀ : B) :=
  rfl

variable {S}

theorem locMap_cent (ι : L →ₐ[ℚ] B) (hι : Function.Injective ι) (γ₀ : Bˣ)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) :
    Function.Injective (locMap S ι) ∧ ∀ y : S ⊗[ℚ] B, y * (locElt S γ₀ : S ⊗[ℚ] B) = (locElt S γ₀ : S ⊗[ℚ] B) * y ↔
      y ∈ Set.range (locMap S ι) :=
  GlobalTheory.LKCent.baseChange_centralizer ℚ S B L (γ₀ : B) ι hι hcent

theorem locMap_star (ι : L →ₐ[ℚ] B) (c : L →ₐ[ℚ] L) (hc : ∀ a, ι (c a) = star (ι a))
    [StarRing (S ⊗[ℚ] B)] (hstar : ∀ (s : S) (b : B), star (s ⊗ₜ[ℚ] b) = s ⊗ₜ[ℚ] star b) (a : S ⊗[ℚ] L) :
    locMap S ι (locInv S c a) = star (locMap S ι a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul s x =>
    simp only [locMap, locInv, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hstar, hc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]

def invLoc (ι : L →ₐ[ℚ] B) (hι : Function.Injective ι) (γ₀ : Bˣ)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[ℚ] L) (hc : ∀ a, ι (c a) = star (ι a))
    [StarRing (S ⊗[ℚ] B)] (hstar : ∀ (s : S) (b : B), star (s ⊗ₜ[ℚ] b) = s ⊗ₜ[ℚ] star b)
    {γ : (S ⊗[ℚ] B)ˣ} (h : StConj S (locElt S γ₀) γ) : H1 S (locInv S c) :=
  invCls (locMap S ι) (locMap_cent ι hι γ₀ hcent).1 (locElt S γ₀) (locMap_cent ι hι γ₀ hcent).2 (locInv S c)
    (locMap_star ι c hc hstar) h

def invL (ℓ : ℕ) [Fact ℓ.Prime] (ι : L →ₐ[ℚ] B) (hι : Function.Injective ι) (γ₀ : Bˣ)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[ℚ] L) (hc : ∀ a, ι (c a) = star (ι a))
    [StarRing (ℚ_[ℓ] ⊗[ℚ] B)] (hstar : ∀ (s : ℚ_[ℓ]) (b : B), star (s ⊗ₜ[ℚ] b) = s ⊗ₜ[ℚ] star b)
    {γ : (ℚ_[ℓ] ⊗[ℚ] B)ˣ} (h : StConj ℚ_[ℓ] (locElt ℚ_[ℓ] γ₀) γ) : H1 ℚ_[ℓ] (locInv ℚ_[ℓ] c) :=
  invLoc ι hι γ₀ hcent c hc hstar h

end Local

end GlobalTheory.LKInv

section Examples

open GlobalTheory.LKInv

example : invCls (k := ℝ) (AlgHom.id ℝ ℂ) (fun _ _ h => h) (Units.mk0 Complex.I Complex.I_ne_zero)
    (fun x => ⟨fun _ => ⟨x, rfl⟩, fun _ => mul_comm _ _⟩) (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fun _ => rfl)
    (StConj.refl' (Units.mk0 Complex.I Complex.I_ne_zero) 1 (by
      simp [Complex.ext_iff])) = 1 :=
  invCls_self _ _ _ _ _ _ _

example (x : ℂˣ) (h : star (x : ℂ) * x = 2) : (x : ℂ) * star (x : ℂ) = 2 :=
  mul_star_of_star_mul x 2 (fun y => mul_comm _ _) h

example (B : Type) [Ring B] [Algebra ℚ B] (γ₀ : Bˣ) [Fact (Nat.Prime 5)] :
    ((locElt ℚ_[5] γ₀ : (ℚ_[5] ⊗[ℚ] B)ˣ) : ℚ_[5] ⊗[ℚ] B) = (1 : ℚ_[5]) ⊗ₜ[ℚ] (γ₀ : B) := rfl

end Examples
end
end

