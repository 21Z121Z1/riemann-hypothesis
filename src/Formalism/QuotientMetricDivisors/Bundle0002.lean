import Mathlib
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LogFactorialIndices.Bundle0001

-- bundled from Formalism.QuotientMetricDivisors.ClassSumDualGeF
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def valLatF {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V) :
    Submodule (𝓞 K) (Fin n → K) :=
  (Submodule.pi Set.univ N).comap (I.restrictScalars (𝓞 K))

end Defs

def ClassSumDualLeF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K),
    pair.IsSymm → pair.Nondegenerate →
    ∀ (Gam : Cl → Type) [∀ c, Group (Gam c)] [∀ c, Fintype (Gam c)]
      (ρ : ∀ c, Gam c →* Module.End K V),
    (∀ c γ x y, pair (ρ c γ x) (ρ c γ y) = pair x y) →
    ∀ I : (Fin n → K) →ₗ[K] (Cl → V),
    (∀ f : Cl → V, (∃ x, I x = f) ↔ ∀ c γ, ρ c γ (f c) = f c) →
    IsClassSum H I pair (fun c => Fintype.card (Gam c)) →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsLattice K (Nab c)) →
    ∀ s : ℕ, (∀ c, ∀ y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c), (s : 𝓞 K) • y ∈ Del c) →
    (∀ c γ, ∀ y ∈ Del c, ρ c γ y ∈ Del c) →
    ∀ y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLatF I Nab), (s : 𝓞 K) • y ∈ valLatF I Del

def ClassSumDualGeF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), (∀ c, 0 < g c) → IsClassSum H I pair g →
    ∀ (Nab Del : Cl → Submodule (𝓞 K) V) (s : ℕ),
    (∀ c, ∀ y ∈ Del c, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c)) →
    ∀ DG : ℕ, (∀ c, g c ∣ DG) →
    ∀ y ∈ valLatF I Del, ((DG * s : ℕ) : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLatF I Nab)

def BoundsIClassF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K),
    pair.IsSymm → pair.Nondegenerate →
    ∀ (Gam : Cl → Type) [∀ c, Group (Gam c)] [∀ c, Fintype (Gam c)]
      (ρ : ∀ c, Gam c →* Module.End K V),
    (∀ c γ x y, pair (ρ c γ x) (ρ c γ y) = pair x y) →
    ∀ I : (Fin n' → K) →ₗ[K] (Cl → V), Function.Injective I →
    (∀ f : Cl → V, (∃ x, I x = f) ↔ ∀ c γ, ρ c γ (f c) = f c) →
    IsClassSum H' I pair (fun c => Fintype.card (Gam c)) →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsLattice K (Nab c)) →
    ∀ s : ℕ, (∀ c, ∀ y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c), (s : 𝓞 K) • y ∈ Del c) →
    (∀ c, Del c ≤ Nab c) → (∀ c γ, ∀ y ∈ Del c, ρ c γ y ∈ Del c) →
    ∀ (G0 : Type) [Fintype G0] (r : G0 → Matrix (Fin n') (Fin n') K) (c : G0 → K) (G : ℕ),
    E * Pr = ∑ t, c t • r t → (∀ t, ∃ a : 𝓞 K, (a : K) = (G : K) * c t) →
    (∀ t, ∀ x ∈ valLatF I Del, (r t).mulVec x ∈ valLatF I Del) →
      Submodule.IsLattice K (valLatF I Nab) ∧ Submodule.IsLattice K (cutLat E (valLatF I Nab)) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E (valLatF I Nab)),
        ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E (valLatF I Nab)

def BoundsIVClassF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), Function.Injective I → (∀ c, 0 < g c) →
    IsClassSum H I pair g →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsLattice K (Nab c)) →
    ∀ s : ℕ, 0 < s → (∀ c, ∀ y ∈ Del c, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c)) →
    ∀ DG : ℕ, 0 < DG → (∀ c, g c ∣ DG) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E (valLatF I Nab),
      (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E (valLatF I Del))) →
      Submodule.IsLattice K (matLat Pr (valLatF I Nab)) ∧
      jw (Eᴴ * H * E) w (matLat Pr (valLatF I Nab)) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr (valLatF I Nab)) (cutLat E (valLatF I Nab)) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K) + vw w (s : K))

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.Complement2Normaliser
section
open Module NumberField IsDedekindDomain Finset

noncomputable section

namespace Formalism.DivisionValues

def PlOver {K : Type} [Field K] [NumberField K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  0 < vw w (g : K)

def LwSumOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : ℕ), 0 < g →
    {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite ∧
    (∀ w : HeightOneSpectrum (𝓞 K), vw (conjPl w) (g : K) = vw w (g : K)) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), PlOver g (conjPl w) ↔ PlOver g w) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), 0 < lw w) ∧
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : PlOver g w), lw w * (vw w (g : K) : ℝ) = Real.log g

def PlOverCoprime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g g' : ℕ), Nat.Coprime g g' →
    ∀ w : HeightOneSpectrum (𝓞 K), ¬ (PlOver g w ∧ PlOver g' w)

def Complement2Normaliser : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ), 0 < g →
    ∀ pb : K, pb * star pb = (g : K) →
    ∀ (Psi : Type) [Fintype Psi] (p : Psi → K) (ν : Psi → ℕ), (∀ τ, p τ = pb) →
    ∀ w : HeightOneSpectrum (𝓞 K),
      vw w (∏ τ, p τ ^ ν τ) + vw (conjPl w) (∏ τ, p τ ^ ν τ) = ((∑ τ, ν τ : ℕ) : ℤ) * vw w (g : K)

def Complement2Scalar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ cg : K, ‖v0.embedding cg‖ = 1 →
    ∀ w : HeightOneSpectrum (𝓞 K), vw w cg + vw (conjPl w) cg = 0

def Complement2Arith : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : ℕ), 0 < g →
    ∀ (E F : HeightOneSpectrum (𝓞 K) → ℝ) (nn cg : K) (m Dpi Dp Dm er : ℝ),
    (∀ w, PlOver g w →
      |E w - (F w + (vw w nn : ℝ) - (vw w cg : ℝ) / m)| ≤ er * (vw w (g : K) : ℝ)) →
    (∀ w, PlOver g w → F w = -((Dp + Dm) / 2) * (vw w (g : K) : ℝ)) →
    (∀ w, PlOver g w → vw w cg + vw (conjPl w) cg = 0) →
    (∀ w, PlOver g w → (vw w nn : ℝ) + (vw (conjPl w) nn : ℝ) = Dpi * (vw w (g : K) : ℝ)) →
      |2 * (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : PlOver g w), lw w * E w) -
        (Dpi - Dp - Dm) * Real.log g| ≤ 2 * er * Real.log g

def Complement2Degree : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (aT w nν δν δpm : Pl → ℝ) (k Dpi Dp Dm : ℝ),
    Dpi = ∑ ρ, nν ρ →
    (∀ ρ, nν ρ = (if ρ ∈ TT then aT ρ + (k - 1) * w ρ else k * w ρ) + δν ρ) →
    Dp + Dm = ∑ ρ, ((k - 1) * w ρ + δpm ρ) →
      Dpi - Dp - Dm =
        (∑ t ∈ TT, aT t) + (∑ ρ, if ρ ∈ TT then 0 else w ρ) + ∑ ρ, (δν ρ - δpm ρ)

def Complement2Sum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : Fin 2 → ℕ),
    (∀ i, 0 < g i) → Nat.Coprime (g 0) (g 1) →
    ∀ (E F : HeightOneSpectrum (𝓞 K) → ℝ), (Function.support E).Finite →
    ∀ (nn cg : Fin 2 → K) (m Dpi Dp Dm er Eels : ℝ),
    (∀ i w, PlOver (g i) w →
      |E w - (F w + (vw w (nn i) : ℝ) - (vw w (cg i) : ℝ) / m)| ≤ er * (vw w (g i : K) : ℝ)) →
    (∀ i w, PlOver (g i) w → F w = -((Dp + Dm) / 2) * (vw w (g i : K) : ℝ)) →
    (∀ i w, PlOver (g i) w → vw w (cg i) + vw (conjPl w) (cg i) = 0) →
    (∀ i w, PlOver (g i) w →
      (vw w (nn i) : ℝ) + (vw (conjPl w) (nn i) : ℝ) = Dpi * (vw w (g i : K) : ℝ)) →
    (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : ∀ i, ¬ PlOver (g i) w), lw w * |E w|) ≤ Eels →
    ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
      (aT w nν δν δpm : Pl → ℝ) (k : ℝ),
    Dpi = ∑ ρ, nν ρ →
    (∀ ρ, nν ρ = (if ρ ∈ TT then aT ρ + (k - 1) * w ρ else k * w ρ) + δν ρ) →
    Dp + Dm = ∑ ρ, ((k - 1) * w ρ + δpm ρ) →
      |2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E w) -
        (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤
      ((∑ ρ, if ρ ∈ TT then 0 else |w ρ|) + (∑ ρ, (|δν ρ| + |δpm ρ|)) + 2 * er) *
        Real.log ((g 0 : ℝ) * (g 1 : ℝ)) + 2 * Eels

def Complement2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : Fin 2 → ℕ),
    (∀ i, 0 < g i) → Nat.Coprime (g 0) (g 1) →
    ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
      (E F : J → HeightOneSpectrum (𝓞 K) → ℝ), (∀ j, (Function.support (E j)).Finite) →
    ∀ (nn : J → Fin 2 → K) (cg : Fin 2 → K) (Dpi Dp Dm er Eels : J → ℝ)
      (aT : Pl → ℝ) (w nν δν δpm : J → Pl → ℝ)
      (x eps L b B0 m f k N S tt η w'' b' X'' logd C0 : ℝ),

    (∀ j i w, PlOver (g i) w →
      |E j w - (F j w + (vw w (nn j i) : ℝ) - (vw w (cg i) : ℝ) / m)| ≤
        er j * (vw w (g i : K) : ℝ)) →
    (∀ j i w, PlOver (g i) w → F j w = -((Dp j + Dm j) / 2) * (vw w (g i : K) : ℝ)) →
    (∀ i w, PlOver (g i) w → vw w (cg i) + vw (conjPl w) (cg i) = 0) →
    (∀ j i w, PlOver (g i) w →
      (vw w (nn j i) : ℝ) + (vw (conjPl w) (nn j i) : ℝ) = Dpi j * (vw w (g i : K) : ℝ)) →

    (∀ j, (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : ∀ i, ¬ PlOver (g i) w), lw w * |E j w|) ≤ Eels j) →

    (∀ j, Dpi j = ∑ ρ, nν j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ + (k - 1) * w j ρ else k * w j ρ) + δν j ρ) →
    (∀ j, Dp j + Dm j = ∑ ρ, ((k - 1) * w j ρ + δpm j ρ)) →

    1 ≤ x → 0 < eps → L = x ^ eps → 0 ≤ b → B0 = f * m * b * x ^ eps →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 0 ≤ b' → 0 ≤ logd →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →

    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → N * (N + tt) ≤ b → k * b' ≤ b →
    f * k * N * X'' ≤ b → logd ≤ L → Real.log ((g 0 : ℝ) * (g 1 : ℝ)) ≤ C0 * L →

    0 ≤ C0 →
    (∀ j, er j ≤ C0 * (f * (N * (N + tt) + m ^ 2 * η))) →
    (∀ j ρ, |δν j ρ| ≤ C0 * (k * S + m * tt * η + (if ρ ∈ TT then b' / x else 0))) →
    (∀ j ρ, |δpm j ρ| ≤ C0 * (k * S + m * η)) →
    (∀ j, Eels j ≤ C0 * B0 + ((TT.card : ℝ) * (2 * b + 4 * k * b') + 4 * f * k * b') * logd +
      C0 * (f * k * N * X'')) →
      (∀ j, |2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E j w) -
        (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0) ∧
      |2 * (∑ j, ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E j w) -
        m * ((∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ)))| ≤
        (9 * C0 ^ 2 + 6 * C0 + 20) * (m * B0)

def PhLip : Prop :=
  ∀ y y' A : ℝ, 1 ≤ y → 1 ≤ y' → y ≤ A → y' ≤ A →
    |Formalism.LatticeIndexTer.ph y - Formalism.LatticeIndexTer.ph y'| ≤ |y - y'| * Real.log A

def Complement3 : Prop :=
  ∀ (U J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (n : ℕ)

    (hu hP logT : U → ℝ) (hK : U → J → ℝ) (aT nτ : U → Pl → ℝ) (phν nν : U → J → Pl → ℝ)
    (c : U → J → Pl → Fin n → ℝ)

    (mlam logκ cP cT e6 logOm logg : ℝ) (cK : J → ℝ) (w fa pr nr : J → Pl → ℝ)

    (x eps L b a rd La B0 m f k N S Sc tt η w'' b' Δ C0 : ℝ),

    (∀ u, hu u = hP u + ∑ j, hK u j - mlam - logκ) →
    (∀ u, hP u = -(∑ ρ, nτ u ρ) * logT u + cP) →
    (∀ u j, hK u j = ∑ ρ, (phν u j ρ - nν u j ρ * logOm) + cK j + cT * (L + logg + logT u)) →
    mlam = ∑ j, ∑ ρ, fa j ρ - e6 →

    (∀ u j ρ, phν u j ρ = ∑ i, Formalism.LatticeIndexTer.ph (w j ρ + c u j ρ i) +
      (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT u ρ + w j ρ) else 0) + pr j ρ) →
    (∀ u j ρ, nν u j ρ = ∑ i, (w j ρ + c u j ρ i) +
      (if ρ ∈ TT then aT u ρ + w j ρ else 0) + nr j ρ) →
    (∀ u j ρ i, 0 ≤ c u j ρ i ∧ c u j ρ i ≤ Sc) → 0 ≤ Sc → Sc ≤ 3 * S → (n : ℝ) ≤ k →
    (∀ u, ∀ ρ ∈ TT, a ≤ aT u ρ ∧ aT u ρ ≤ a + Δ) → m * Δ ≤ a →
    (∀ j ρ, 1 ≤ w j ρ ∧ w j ρ + Sc ≤ a * rd) → (∀ u j, ∀ ρ ∈ TT, aT u ρ + w j ρ ≤ a * rd) →

    (∀ u, 0 ≤ logT u ∧ logT u ≤ C0 * m * L) → 0 ≤ cT → cT ≤ C0 * (f * m ^ 2 * N ^ 2) →
    (∀ u ρ, |nτ u ρ - (if ρ ∈ TT then aT u ρ else 0)| ≤
      C0 * ((if ρ ∈ TT then b' else 0) + S + m * η + N)) →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →

    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 0 ≤ b' → 0 ≤ C0 → |logOm| ≤ La →

    m ^ 3 * N ^ 2 * L ≤ b → k * N ≤ b → k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b →
    m * k * b' ≤ a →
      ∀ u u', |(hu u + ∑ t ∈ TT, aT u t * logT u) - (hu u' + ∑ t ∈ TT, aT u' t * logT u')| ≤
        (7 * C0 ^ 2 + 18) * ((TT.card : ℝ) * a * La + m * B0)

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.DivIntoDual
section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

def DivIntoDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ) (R : Submodule (𝓞 K) (Fin D → K))
    (B : (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (ι : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K),
    (∀ w, ζ w ≠ 0) → (∀ w, vw w (ζ w) = 0) →
    (∀ w (F : Fin (n w) → K), P w F = ζ w * B ((ι w).mulVec ((π w).mulVec F))) →
    (∀ w, ∀ F ∈ M w, P w F = 0 ∨ 0 ≤ vw w (P w F)) →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι w) (matLat (π w) (M w)))) →
    ∀ x ∈ R, B x ∈ Set.range (algebraMap (𝓞 K) K)

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.DivIntoDualShift
section
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def smulLat {d : ℕ} (a : K) (N : Submodule (𝓞 K) (Fin d → K)) : Submodule (𝓞 K) (Fin d → K) :=
  N.map ((LinearMap.lsmul K (Fin d → K) a).restrictScalars (𝓞 K))

def IsShiftAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ) :
    Prop :=
  ∃ a : K, a ≠ 0 ∧ vw w a = -s ∧
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N)

def IsShift {d : ℕ} (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℤ) : Prop :=
  ∀ w, IsShiftAt w N N' (σ w)

def shiftIdeal (σ : HeightOneSpectrum (𝓞 K) → ℤ) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-σ w)

def Above (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop := (p : 𝓞 K) ∈ w.asIdeal

end Defs

def ShiftAtIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ),
    (∃ a : K, a ≠ 0 ∧ vw w a = -s) ∧
    (IsShiftAt w N N' s ↔ ∀ a : K, a ≠ 0 → vw w a = -s →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N))

def ShiftIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N N' : Submodule (𝓞 K) (Fin d → K)), Submodule.IsLattice K N →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (s : ℤ), IsShiftAt w N N' s →
      idx w N N' = -((d : ℤ) * s)

def MuLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ N : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K N →
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N = -(lcv X N) / d

def ShiftMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ N N' : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K N → Submodule.IsLattice K N' →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, IsShift N N' σ →
      lcv X N' = lcv X N - 2 * (d : ℝ) * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ) ∧
      (0 < d → (Function.support σ).Finite ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' =
          Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
            2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ))

def ShiftEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N : Submodule (𝓞 K) (Fin d → K)), Submodule.IsLattice K N →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, (Function.support σ).Finite →
      IsShift N (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) σ ∧
      Submodule.IsLattice K (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) ∧
      ∀ N' : Submodule (𝓞 K) (Fin d → K), IsShift N N' σ →
        N' = Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N

def LwSumPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (p : ℕ), p.Prime →
    {w : HeightOneSpectrum (𝓞 K) | Above p w}.Finite ∧
    (∃ w : HeightOneSpectrum (𝓞 K), Above p w) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), Above p w ↔ 0 < vw w (p : K)) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), 0 < lw w) ∧
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (p : K) : ℝ) = Real.log p ∧
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w ≤ Real.log p ∧
    ∀ e : ℤ, (∀ w : HeightOneSpectrum (𝓞 K), Above p w → vw w (p : K) = e) →
      ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w = Real.log p / e

def RoundingSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (σ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
    (∀ w, ((⌊σ w⌋ : ℤ) : ℝ) ≠ σ w → ∃ p ∈ S, Above p w) →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (σ w - (⌊σ w⌋ : ℤ))).Finite ∧
      0 ≤ 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w - (⌊σ w⌋ : ℤ)) ∧
      2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w - (⌊σ w⌋ : ℤ)) ≤
        ∑ p ∈ S, 2 * ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w ∧
      ∑ p ∈ S, 2 * ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w ≤
        ∑ p ∈ S, 2 * Real.log p

def RoundingCost : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ N N' : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K N → Submodule.IsLattice K N' →
    ∀ (σ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
    (∀ w, ((⌊σ w⌋ : ℤ) : ℝ) ≠ σ w → ∃ p ∈ S, Above p w) →
    IsShift N N' (fun w => ⌊σ w⌋) →
      (Function.support σ).Finite ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' ≤
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
          2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * σ w ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
                2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * σ w) - ∑ p ∈ S, 2 * Real.log p ≤
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N'

def RoundingUp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ N N' : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K N → Submodule.IsLattice K N' →
    ∀ (σ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
    (∀ w, ((⌈σ w⌉ : ℤ) : ℝ) ≠ σ w → ∃ p ∈ S, Above p w) →
    IsShift N N' (fun w => ⌈σ w⌉) →
      (Function.support σ).Finite ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
                2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * σ w ≤
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' ≤
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
          2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * σ w) + ∑ p ∈ S, 2 * Real.log p

def RoundingTheta : Prop :=
  ∀ Y : ℝ, 0 ≤ Y → ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1)).filter Nat.Prime, 2 * Real.log p ≤ 3 * Y

def ShiftPairing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ), IsShiftAt w N N' s →
    ∀ f : (Fin d → K) →ₗ[K] K, (∀ φ ∈ N, f φ = 0 ∨ s ≤ vw w (f φ)) →
      ∀ φ ∈ N', f φ = 0 ∨ 0 ≤ vw w (f φ)

def DivIntoDualShift : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d D : ℕ)
    (R : Submodule (𝓞 K) (Fin D → K)) (B : (Fin d → K) →ₗ[K] (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (ι : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin d → K) →ₗ[K] (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K),
    (∀ w, ζ w ≠ 0) → (∀ w, vw w (ζ w) = 0) →
    (∀ w (φ : Fin d → K) (F : Fin (n w) → K),
      P w φ F = ζ w * B φ ((ι w).mulVec ((π w).mulVec F))) →
    ∀ (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℝ)
      (τ : HeightOneSpectrum (𝓞 K) → ℤ),
    (∀ w, ∀ φ ∈ N, ∀ F ∈ M w, P w φ F = 0 ∨ σ w ≤ (vw w (P w φ F) : ℝ)) →
    (∀ w, τ w ≤ ⌈σ w⌉) → IsShift N N' τ →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι w) (matLat (π w) (M w)))) →
    ∀ φ ∈ N', ∀ x ∈ R, B φ x ∈ Set.range (algebraMap (𝓞 K) K)

end Formalism.DivisionValues
end
end

