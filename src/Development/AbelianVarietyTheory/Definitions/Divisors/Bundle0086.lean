import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsCyclicClassPolynomial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.ChernCalc
open GlobalTheory.FlagFibre (Low)
open scoped Matrix

namespace GlobalTheory.FlagCell2

variable {ι : Type} {m : ι → ℕ} {n d : ℕ}

abbrev Cell (m : ι → ℕ) : Type := Σ τ, Low (m τ)

def upU {K : Type} [Zero K] [One K] {s : ℕ} (y : Low s → K) : Matrix (Fin s) (Fin s) K :=
  Matrix.of fun a b => if h : a < b then y ⟨(b, a), h⟩ else if a = b then 1 else 0

def upM {K : Type} [Zero K] [One K] (y : Cell m → K) : Mat m K := fun τ => upU fun s => y ⟨τ, s⟩

def Cell.root (j : Cell m) : Root m := ⟨j.1, j.2.1.2⟩

def bsL {J : Type} (ε : Fin n ≃ Fin d ⊕ J) : V n →L[ℂ] V d :=
  (EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun a => EuclideanSpace.proj (ε.symm (.inl a))

def fb {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) (j : J) : ℂ := w (ε.symm (.inr j))

def pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : V n := WithLp.toLp 2 fun a => Sum.elim (fun b => v b) y (ε a)

def cellPot (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (x : Root m) (w : V n) : ℝ :=
  -Real.log (grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2)

variable [Fintype ι]

def cellFib (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) : Ev n :=
  MvPolynomial.aeval (fun x => ofValues (ddc (cellPot ε G x) w)) ((fibrePoint m).map (algebraMap ℝ ℂ))

def cellForm (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n) : Alt n :=
  pull (bsL ε) (a (bsL ε w)) * (cellFib ε G w : Alt n)

def fibDens (G : Mat m ℂ) (y : Cell m → ℂ) : ℝ :=
  ∏ τ, GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ fun s => y ⟨τ, s⟩

omit [Fintype ι] in

theorem upU_eq {s : ℕ} (y : Low s → ℂ) : upU y = (GlobalTheory.FlagFibre.uni y)ᵀ := by
  ext a b
  simp only [upU, GlobalTheory.FlagFibre.uni, Matrix.of_apply, Matrix.transpose_apply, eq_comm]

omit [Fintype ι] in

theorem bsL_apply {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) (a : Fin d) : bsL ε w a = w (ε.symm (.inl a)) := rfl

omit [Fintype ι] in

theorem bsL_pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : bsL ε (pt ε v y) = v := by
  ext a
  simp [bsL_apply, pt]

omit [Fintype ι] in

theorem fb_pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : fb ε (pt ε v y) = y := by
  funext j
  simp [fb, pt]

section Variety

variable {F : Type} [Field F] {X Y : Var F} {σ : F →+* ℂ}

def InCell (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (A : Mat m X.Fn)
    (u : Cell m → Y.Fn) (y : Y.X) : Prop :=
  A ∈ E.S (f y) ∧ upM u * A.map φ ∈ E'.S y

def cellMap (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (c : AlgChart X.str σ X.dim)
    (u : Cell m → Y.Fn) (y : CxPts Y.str σ) : V n :=
  pt ε (c.e (ptMap σ f hf y)) fun j => ratVal (u j) y

def cellSet (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X)
    (hf : f ≫ X.str = Y.str) (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn) : Set (CxPts Y.str σ) :=
  {y | InCell E E' φ f A u (under y) ∧ ptMap σ f hf y ∈ c.e.source}

end Variety

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ClassifyField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.HT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKP

structure Raw (K R : Type) [Field K] [Ring R] [Algebra ℚ R] where

  A : AbVar K

  ia : R →ₐ[ℚ] End0 A

  L : LB A.X.left
  hL : L.IsLB

section General

variable {K R : Type} [Field K] [Ring R] [Algebra ℚ R]

def Raw.c (X : Raw K R) : Pic X.A.X.left := cls X.L X.hL

def IsPol (σ : R → R) (X : Raw K R) : Prop :=
  IsAmpleCls X.c ∧ ∀ r : End0 X.A →ₗ[ℚ] End0 X.A, IsRosati X.c r → ∀ x, r (X.ia x) = X.ia (σ x)

def Intertw {A B : AbVar K} (f : A ⟶ B) (a : End0 A) (b : End0 B) : Prop :=
  ∀ (n : ℤ) (g : End A) (h : End B), n • a = toEnd0 A g → n • b = toEnd0 B h →
    (show A ⟶ A from g) ≫ f = f ≫ (show B ⟶ B from h)

def IsRIsog {A B : AbVar K} (a : R →ₐ[ℚ] End0 A) (b : R →ₐ[ℚ] End0 B) (f : A ⟶ B) : Prop :=
  IsIsogeny f ∧ ∀ x, Intertw f (a x) (b x)

def PolIsog (X Y : Raw K R) : Prop :=
  ∃ (f : X.A ⟶ Y.A) (m n : ℕ), IsRIsog X.ia Y.ia f ∧ 0 < m ∧ 0 < n ∧
    m • AbVar.lam X.c (fst X.A.X X.A.X) (snd X.A.X X.A.X) =
      n • AbVar.lam Y.c (fst X.A.X X.A.X ≫ f.hom) (snd X.A.X X.A.X ≫ f.hom)

def Betti (X : Raw K R) {W : Type} [AddCommGroup W] [Module ℚ W] (ρ : R → W → W) (ψ : W → W → ℚ) : Prop :=
  ∃ (Λ : Submodule ℤ W) (s : ℚ), Λ.FG ∧ Submodule.span ℚ (Λ : Set W) = ⊤ ∧ 0 < s ∧
    (∀ v ∈ Λ, ∀ w ∈ Λ, ∃ a : ℤ, s * ψ v w = a) ∧
    ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
      ∃ (β : Λ →ₗ[ℤ] Tl l X.A) (ζ : Tate l (AlgebraicClosure K)ˣ),
        Function.Bijective (β.liftBaseChange ℤ_[l]) ∧ Submodule.span ℤ_[l] {ζ} = ⊤ ∧
        (∀ (x : R) (n : ℤ) (g : End X.A) (v w : Λ), n • X.ia x = toEnd0 X.A g → n • ρ x v = (w : W) →
          tend l X.A g (β v) = β w) ∧
        ∀ E : Tl l X.A →ₗ[ℤ_[l]] Tl l X.A →ₗ[ℤ_[l]] Tate l (AlgebraicClosure K)ˣ, IsWeilForm l X.L E →
          ∀ (v w : Λ) (a : ℤ), s * ψ v w = a → E (β v) (β w) = a • ζ

def Link {K' : Type} [Field K'] (X : Raw K R) (Y : Raw K' R) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], (l : K') ≠ 0 →
    ∃ (e : Tl l X.A ≃ₗ[ℤ_[l]] Tl l Y.A)
      (u : Tate l (AlgebraicClosure K)ˣ ≃ₗ[ℤ_[l]] Tate l (AlgebraicClosure K')ˣ),
      (∀ (x : R) (n : ℤ) (g : End X.A) (h : End Y.A), n • X.ia x = toEnd0 X.A g → n • Y.ia x = toEnd0 Y.A h →
        ∀ t, e (tend l X.A g t) = tend l Y.A h (e t)) ∧
      ∀ (E : Tl l X.A →ₗ[ℤ_[l]] Tl l X.A →ₗ[ℤ_[l]] Tate l (AlgebraicClosure K)ˣ)
        (E' : Tl l Y.A →ₗ[ℤ_[l]] Tl l Y.A →ₗ[ℤ_[l]] Tate l (AlgebraicClosure K')ˣ),
        IsWeilForm l X.L E → IsWeilForm l Y.L E' → ∀ s t, E' (e s) (e t) = u (E s t)

def IsTwist {A : AbVar K} (c d : Pic A.X.left) (h : End0 A) : Prop :=
  ∃ (n m : ℕ) (g : End A), 0 < n ∧ 0 < m ∧ (m : ℤ) • h = toEnd0 A g ∧
    IsAdj (A := A) (B := A) c d (𝟙 A) n g

def IsFrobModel (q : ℕ) (A : AbVar K) (φ : End A) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Fintype k) (_ : Algebra k K) (A₀ : AbVar k) (e : baseChange K A₀ ≅ A),
    Fintype.card k = q ∧ (show A ⟶ A from φ) = e.inv ≫ bcMap K (A := A₀) (B := A₀) (frob A₀) ≫ e.hom

def PInt (p : ℕ) {D : Type} [Ring D] (x : D) : Prop := ∃ N : ℕ, ¬ p ∣ N ∧ IsIntegral ℤ (N • x)

def PUnit (p : ℕ) {D : Type} [Ring D] (x : D) : Prop := ∃ u : Dˣ, (u : D) = x ∧ PInt p x ∧ PInt p ((u⁻¹ : Dˣ) : D)

def FrobLike (p r : ℕ) (A : AbVar K) (π : End0 A) : Prop :=
  ∃ (m : ℕ) (φ : End A) (u : End0 A), 0 < m ∧ IsFrobModel (p ^ (r * m)) A φ ∧ Commute π (toEnd0 A φ) ∧
    PUnit p u ∧ π ^ m = u * toEnd0 A φ

end General

abbrev Fb (p : ℕ) [Fact p.Prime] : Type := AlgebraicClosure (ZMod p)

abbrev Zb : Type := integralClosure ℤ ℂ

section CM

variable {M : Type} [Field M] [NumberField M]

def intEmb (φ : M →+* ℂ) : 𝓞 M →+* Zb :=
  (φ.comp (algebraMap (𝓞 M) M)).codRestrict (integralClosure ℤ ℂ) fun x =>
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (RingHom.id ℤ) φ (RingHom.ext_int _ _)

def IsCMType (Φ : Finset (M →+* ℂ)) : Prop := ∀ φ, φ ∈ Φ ↔ ComplexEmbedding.conjugate φ ∉ Φ

def Matches (p r : ℕ) {k : Type} [Field k] (j : Zb →+* k) (Φ : Finset (M →+* ℂ)) (π : M) : Prop :=
  π ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 M)) (m : ℤ), (p : 𝓞 M) ∈ w.asIdeal →
    w.valuation M π = WithZero.exp (-m) →
      (Ideal.absNorm w.asIdeal : ℚ) ^ m =
        (p : ℚ) ^ (r * Nat.card {φ : Φ // RingHom.ker (j.comp (intEmb φ.1)) = w.asIdeal})

def HasInt {K : Type} [Field K] (X : Raw K M) (a : OAct (𝓞 M) X.A.X) : Prop :=
  ∀ x : 𝓞 M, ∃ g : End X.A, AbVar.Hom.hom g = a.act x ∧ X.ia x = toEnd0 X.A g

def IsCMLie {K : Type} [Field K] (X : Raw K M) {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → 𝓞 M →+* K) : Prop :=
  2 * X.A.dim = Module.finrank ℚ M ∧ ∃ a : OAct (𝓞 M) X.A.X, HasInt X a ∧ IsLieType a φ

variable [IsCMField M]

def cj (x : M) : M := IsCMField.complexConj M x

def TotPos (h : M) : Prop := cj h = h ∧ ∀ φ : M →+* ℂ, 0 < (φ h).re

def PosXi (Φ : Finset (M →+* ℂ)) (ξ : M) : Prop := cj ξ = -ξ ∧ ∀ φ ∈ Φ, 0 < (φ ξ).im

def sigH {d : ℕ} (H : Fin d → M) (x : Matrix (Fin d) (Fin d) M) : Matrix (Fin d) (Fin d) M :=
  Matrix.of fun i j => (H i)⁻¹ * cj (x j i) * H j

def psiH {d : ℕ} (H : Fin d → M) (ξ : M) (v w : Fin d → M) : ℚ :=
  Algebra.trace ℚ M (ξ * ∑ i, H i * v i * cj (w i))

def psi1 (ξ v w : M) : ℚ := Algebra.trace ℚ M (ξ * (v * cj w))

def XiEquiv (ξ ξ' : M) : Prop := ∃ (c : ℚ) (x : M), 0 < c ∧ x ≠ 0 ∧ ξ' = c * (x * cj x) * ξ

def admitted (p r : ℕ) {K : Type} [Field K] {d : ℕ} (H : Fin d → M) (π : M)
    (X : Raw K (Matrix (Fin d) (Fin d) M)) : Prop :=
  IsPol (sigH H) X ∧ 2 * X.A.dim = d * Module.finrank ℚ M ∧
    FrobLike p r X.A (X.ia (Matrix.scalar (Fin d) π))

end CM

def ClassifyField : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (M : Type) [Field M] [NumberField M] [IsCMField M] (d : ℕ) (H : Fin d → M)
    (Φ : Finset (M →+* ℂ)) (j : Zb →+* Fb p) (π : M), 0 < r → 0 < d → (∀ i, TotPos (H i)) → IsCMType Φ →
    Matches p r j Φ π →
    ∃ X : {ξ : M // PosXi Φ ξ} → Raw (Fb p) (Matrix (Fin d) (Fin d) M),
      (∀ ξ, admitted p r H π (X ξ) ∧ Betti (X ξ) Matrix.mulVec (psiH H ξ.1)) ∧
      (∀ Y, admitted p r H π Y → ∃ ξ, PolIsog Y (X ξ)) ∧
      ∀ ξ ξ', PolIsog (X ξ) (X ξ') ↔ XiEquiv ξ.1 ξ'.1

end GlobalTheory.LKP
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasRepOfPublished
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem Fam.ev {T Y : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hN' : (GlobalTheory.AbDual.ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB h.isLB _
  refine ⟨hN', (isAdditive_iff hN').2 fun Z a a' t => ?_⟩
  simp only [evc_ev h.isLB (fst A Y) (snd A Y ≫ y) hN', lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Z a a' (t ≫ y)

omit [GrpObj A] in

theorem Inj.fibInj {U : Over S} {M : LB (A ⊗ U).left} (h : Inj A M) : FibInj A M :=
  fun _ _ _ _ Y _ u u' hs => h Y u u' hs

end GlobalTheory.DualCon
end
end

