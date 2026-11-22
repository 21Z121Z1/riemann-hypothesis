import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def charVal {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ : X) : A :=
  (Spec.preimage (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp A ⟶ Spec (torusRing ZU X))).hom
    (AddMonoidAlgebra.single χ 1)

def KillsOver {G : Over S} [GrpObj G] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) {B : Type} [CommRing B]
    (b : Sp B ⟶ S) : Prop :=
  ∀ (A : Type) [CommRing A] (g : B →+* A) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X),
    (∀ y ∈ Y, charVal t y = 1) → t ≫ u = 1

def IsCocharLie {R : Type} [CommRing R] {x : Sp R ⟶ S} (M : LieModel (splitTorus S X) x (X →+ R)) : Prop :=
  ∀ (δ : X →+ R) (χ : X), charVal (M.pt δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ)

def LieModel.Lifts {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S}
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (c : R →+* R') {S' : Scheme.{0}} {G' : Over S'}
    (φ : G'.left ⟶ G.left) {x' : Sp R' ⟶ S'} (e : E) (v : epsAt x' ⟶ G') : Prop :=
  v.left ≫ φ = spMap (dualMap c) ≫ (M.pt e).left

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def flagStep (Ω : Type) [Field Ω] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : ℕ) : Submodule Ω E :=
  Submodule.span Ω (b₀ '' {k | (k : ℕ) < i})

namespace Lat

def IsFlagVBOn (L : Lat ξ E) (T : Set (Cpt ξ)) {r : ℕ} (b₀ : Fin r → E) : Prop :=
  ∀ p ∈ T, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin r → E, (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧
    ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q

def gr (L : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (i : Fin r) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p) {t | ∃ e ∈ L p, e - t • b₀ i ∈ flagStep Ω b₀ i}

def IsGenAt (Λ : Lat ξ Ω) (p : Cpt ξ) (t : Ω) : Prop := t ≠ 0 ∧ Λ p = Submodule.span (regAt ξ p) {t}

def tens {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p) {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i}

def grTens {S : Type} [Fintype S] {r : S → ℕ} (L : S → Lat ξ E) (b₀ : ∀ σ, Fin (r σ) → E)
    (a : (Σ σ, Fin (r σ)) → ℤ) : Lat ξ Ω :=
  tens (fun q : Σ σ, Fin (r σ) => (L q.1).gr (b₀ q.1) q.2) a

end Lat

def IsGenericFlag {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {E' : Type} [AddCommGroup E'] [Module Ω' E']
    (j : E →+ E') {S : Type} {r : S → ℕ} (V : S → Submodule Ω E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ) : Prop :=
  ∃ (c : ∀ σ, Fin (r σ) → E) (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω'),
    (∀ σ, LinearIndependent Ω (c σ) ∧ Submodule.span Ω (Set.range (c σ)) = V σ) ∧
    (∀ (a : Ω) e, j (a • e) = algebraMap Ω Ω' a • j e) ∧ (∀ σ, LinearIndependent Ω' fun k => j (c σ k)) ∧
    (∀ σ, LinearIndependent Ω' (b₀ σ)) ∧ (∀ σ k, u σ k k = 1) ∧ (∀ σ l k, l < k → u σ l k = 0) ∧
    (∀ σ i, flagStep Ω' (b₀ σ) i = flagStep Ω' (fun k => ∑ l, u σ l k • j (c σ l)) i) ∧
    AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    0 < d ∧ Module.finrank (IntermediateField.adjoin Ω
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω' = d

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def IsCoeffAt (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (x : Cpt ξ) (f : Ω) : Prop :=
  ∃ α β : Ω, α ≠ 0 ∧ β ≠ 0 ∧ A.wedge p x = Submodule.span (regAt ξ x) {α • a} ∧
    B.wedge q x = Submodule.span (regAt ξ x) {β • b} ∧ f * α = β

def IsLineGenOn (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (T : Set (Cpt ξ)) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ ∀ x ∈ T, IsCoeffAt A B p q a b x 1

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

