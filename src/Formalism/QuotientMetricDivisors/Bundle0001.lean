import Mathlib
import Formalism.QuotientMetricDivisors.Statement
import Formalism.HarderNarasimhan.Bundle0002

-- bundled from Formalism.QuotientMetricDivisors.ClassSumDualLe
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def cutLat {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (A : Submodule (𝓞 K) (Fin n → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  A.comap ((Matrix.mulVecLin E).restrictScalars (𝓞 K))

def IsOrthProj {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) : Prop :=
  Pr * E = 1 ∧ Eᴴ * H * (1 - E * Pr) = 0

def valLat {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) (Fin n → K) :=
  (Submodule.pi Set.univ fun _ : Cl => N).comap (I.restrictScalars (𝓞 K))

def IsClassSum {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    (H : Matrix (Fin n) (Fin n) K) (I : (Fin n → K) →ₗ[K] (Cl → V))
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (g : Cl → ℕ) : Prop :=
  ∀ x y, hform H x y = ∑ c, ((g c : K))⁻¹ * pair (I x c) (I y c)

end Defs

def OrthProjExists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (H.map v0.embedding).PosDef →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
      Hᴴ = H ∧ IsUnit H.det ∧ IsUnit (Eᴴ * H * E).det ∧
        IsOrthProj H E ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)) ∧
        ∀ Pr, IsOrthProj H E Pr → Pr = (Eᴴ * H * E)⁻¹ * (Eᴴ * H)

def ProjDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K),
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (matLat Pr A) = cutLat E (Formalism.HermitianLatticesTheory.dual (hform H) A)

def CutDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (cutLat E A) = matLat Pr (Formalism.HermitianLatticesTheory.dual (hform H) A)

def ExpIndexLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (A B : Submodule (𝓞 K) (Fin D → K)), Submodule.IsLattice K A → Submodule.IsLattice K B →
    ∀ a : 𝓞 K, a ≠ 0 → (∀ x ∈ A, a • x ∈ B) →
    ∀ w : HeightOneSpectrum (𝓞 K), idx w A B ≤ (D : ℤ) * vw w (a : K)

def ExpIndexLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (A B : Submodule (𝓞 K) (Fin D → K)), Submodule.IsLattice K A → Submodule.IsLattice K B →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ x ∈ A, a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) →
      idx w A B ≤ (D : ℤ) * vw w (a : K)

def ClassSumDualLe : Prop :=
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
    ∀ Nab Del : Submodule (𝓞 K) V, Submodule.IsLattice K Nab →
    ∀ s : ℕ, (∀ y ∈ Formalism.HermitianLatticesTheory.dual pair Nab, (s : 𝓞 K) • y ∈ Del) →
    (∀ c γ, ∀ y ∈ Del, ρ c γ y ∈ Del) →
    ∀ y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLat I Nab), (s : 𝓞 K) • y ∈ valLat I Del

def ClassSumDualGe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), (∀ c, 0 < g c) → IsClassSum H I pair g →
    ∀ (Nab Del : Submodule (𝓞 K) V) (s : ℕ), (∀ y ∈ Del, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair Nab) →
    ∀ DG : ℕ, (∀ c, g c ∣ DG) →
    ∀ y ∈ valLat I Del, ((DG * s : ℕ) : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLat I Nab)

def ProjIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G0 : Type) [Fintype G0]
    (r : G0 → Matrix (Fin n) (Fin n) K) (c : G0 → K) (G : ℕ),
    (∀ s, ∃ a : 𝓞 K, (a : K) = (G : K) * c s) →
    ∀ B : Submodule (𝓞 K) (Fin n → K), (∀ s, ∀ x ∈ B, (r s).mulVec x ∈ B) →
    ∀ x ∈ B, (G : 𝓞 K) • (∑ s, c s • r s).mulVec x ∈ B

def BoundsI : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n' → K), Submodule.IsLattice K A →
    ∀ s : ℕ, (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H') A, (s : 𝓞 K) • x ∈ B) →
    ∀ G : ℕ, (∀ x ∈ B, (G : 𝓞 K) • (E * Pr).mulVec x ∈ A) →
      Submodule.IsLattice K (cutLat E A) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E A), ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E A

def BoundsIVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n' n D : ℕ) (H' : Matrix (Fin n') (Fin n') K), H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    (∀ i j, (Eᴴ * H' * E) i j ∈ K0) →
    (∀ v : InfinitePlace K, ((Eᴴ * H' * E).map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ A B : Submodule (𝓞 K) (Fin n' → K), Submodule.IsLattice K A →
    ∀ s : ℕ, 0 < s → (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H') A, (s : 𝓞 K) • x ∈ B) →
    ∀ G : ℕ, 0 < G → (∀ x ∈ B, (G : 𝓞 K) • (E * Pr).mulVec x ∈ A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (e : Fin D → Fin D → K),
      IsLocBasis (matLat P (cutLat E A)) w e →
      vw w (gramR (quotGram P (Eᴴ * H' * E)) e) ≤ (D : ℤ) * (vw w (G : K) + vw w (s : K))

def BoundsIVGen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ z ∈ cutLat E A, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsLattice K (matLat Pr A) ∧ Submodule.IsLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * (vw w (a : K) + vw w (DG : K))

def BoundsIV : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E A, (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsLattice K (matLat Pr A) ∧ Submodule.IsLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K))

def BoundsIVReal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E A, (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      (jw (Eᴴ * H * E) w (matLat Pr A) : ℝ) ≤
        ((J : ℝ) + (vw w (DG : K) : ℝ)) * (d : ℝ) +
          (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℝ)

def BoundsIClass : Prop :=
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
    ∀ Nab Del : Submodule (𝓞 K) V, Submodule.IsLattice K Nab →
    ∀ s : ℕ, (∀ y ∈ Formalism.HermitianLatticesTheory.dual pair Nab, (s : 𝓞 K) • y ∈ Del) →
    Del ≤ Nab → (∀ c γ, ∀ y ∈ Del, ρ c γ y ∈ Del) →
    ∀ (G0 : Type) [Fintype G0] (r : G0 → Matrix (Fin n') (Fin n') K) (c : G0 → K) (G : ℕ),
    E * Pr = ∑ t, c t • r t → (∀ t, ∃ a : 𝓞 K, (a : K) = (G : K) * c t) →
    (∀ t, ∀ x ∈ valLat I Del, (r t).mulVec x ∈ valLat I Del) →
      Submodule.IsLattice K (valLat I Nab) ∧ Submodule.IsLattice K (cutLat E (valLat I Nab)) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E (valLat I Nab)),
        ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E (valLat I Nab)

def BoundsIVClass : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), Function.Injective I → (∀ c, 0 < g c) →
    IsClassSum H I pair g →
    ∀ Nab Del : Submodule (𝓞 K) V, Submodule.IsLattice K Nab →
    ∀ s : ℕ, 0 < s → (∀ y ∈ Del, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair Nab) →
    ∀ DG : ℕ, 0 < DG → (∀ c, g c ∣ DG) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E (valLat I Nab),
      (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E (valLat I Del))) →
      Submodule.IsLattice K (matLat Pr (valLat I Nab)) ∧
      jw (Eᴴ * H * E) w (matLat Pr (valLat I Nab)) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr (valLat I Nab)) (cutLat E (valLat I Nab)) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K) + vw w (s : K))

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.DualMu
section
open Module NumberField

noncomputable section

namespace Formalism.DivisionValues

def DualMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame X) (Formalism.HN.dualLat R) =
        lcv X R / D

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.LatticeGlueUnique
section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

def glueLat {K : Type} [Field K] [NumberField K] {D : ℕ}
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)) : Submodule (𝓞 K) (Fin D → K) :=
  ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)

def LatticeGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)),
    Submodule.IsLattice K L0 → (∀ w, Submodule.IsLattice K (L w)) →
    {w : HeightOneSpectrum (𝓞 K) |
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w) ≠ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L0}.Finite →
    Submodule.IsLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (glueLat L) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)

def LatticeGlueUnique : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (R R' : Submodule (𝓞 K) (Fin D → K)),
    ((∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R') → R = R') ∧
    ((∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R') → R ≤ R') ∧
    glueLat (fun _ => R) = R

def LatticeGlueIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (L0 L1 : Submodule (𝓞 K) (Fin D → K)),
    Submodule.IsLattice K L0 → Submodule.IsLattice K L1 →
    ∀ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite →
    ∃! R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R ∧
      (∀ w ∈ S, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L1) ∧
      (∀ w ∉ S, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L0)

def LatticeGlueSemi : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ),
    (∀ (L0 : Submodule (𝓞 K) (Fin D → K))
      (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)),
      Submodule.IsLattice K L0 → (∀ w, Submodule.IsLattice K (L w)) →
      (∀ w, L (conjPl w) = L w) →
      {w : HeightOneSpectrum (𝓞 K) |
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (L w) ≠ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal L0}.Finite →
      Submodule.IsLattice K (glueLat L) ∧
      (∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (glueLat L) = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (L w)) ∧
      glueLat L = ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (L w)) ∧
    (∀ R R' : Submodule (𝓞 K) (Fin D → K),
      (∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal R = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal R') → R = R')

def StepBGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    (∃! R : Submodule (𝓞 K) (Fin D → K), ∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) ∧
    ∀ R : Submodule (𝓞 K) (Fin D → K),
      (∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      Submodule.IsLattice K R ∧
      R = glueLat (fun w => matLat (ι (μ w)) (abelian₂ (μ w))) ∧
      (∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal R =
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) ∧
      {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R ≠
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι μ0) (abelian₂ μ0))}.Finite

def DivIntoDualGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), {w | μ w ≠ μ0}.Finite →
    ∀ (n : Tup → ℕ) (M : ∀ t, Submodule (𝓞 K) (Fin (n t) → K)),
    (∀ t, Submodule.IsLattice K (M t)) →
    ∀ (π : ∀ t, Matrix (Fin D) (Fin (n t)) K), (∀ t, Function.Surjective (π t).mulVec) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∃! R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R ∧
      ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R =
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (matLat (π (μ w)) (M (μ w))))

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.ProdFormula
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def ProdFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (a : K), a ≠ 0 →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)).Finite ∧
    (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ =
      ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w a : ℝ)

def DetCS : Prop :=
  ∀ (n D : ℕ) (Hc : Matrix (Fin n) (Fin n) ℂ), Hc.PosDef →
    ∀ A B : Matrix (Fin D) (Fin n) ℂ,
      ‖(A * Hc * Bᴴ).det‖ ^ 2 ≤ (A * Hc * Aᴴ).det.re * (B * Hc * Bᴴ).det.re

def LcvBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
        lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)).Finite ∧
      lcv X L = (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (gram X v e).det.re +
        2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)

def IdxChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (L : Submodule (𝓞 K) (Fin d → K)), Submodule.IsLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (γ : Matrix (Fin d) (Fin d) K),
      IsLocBasis L w (fun i => ∑ k, γ k i • e k) →
      idx w (Submodule.span (𝓞 K) (Set.range e)) L = vw w γ.det ∧
      idx (conjPl w) (Submodule.span (𝓞 K) (Set.range e)) L = vw (conjPl w) γ.det

def ValBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ a b : K, a ≠ 0 → b ≠ 0 → vw w (a * b) = vw w a + vw w b) ∧
    (∀ a : K, vw w (star a) = vw (conjPl w) a) ∧
    lw (conjPl w) = lw w ∧ conjPl (conjPl w) = w ∧ vw w 1 = 0 ∧
    (∀ a : K, vw w a⁻¹ = - vw w a) ∧
    (∀ a : 𝓞 K, 0 ≤ vw w (a : K))

def GramChange : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (D m : ℕ) (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) (γ : Matrix (Fin m) (Fin m) K),
      gramR Γ (fun i => ∑ k, γ k i • e k) = star γ.det * γ.det * gramR Γ e

def ImageLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ)
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (XS v).det) →
    (∀ v, IsUnit (XT v).det) →
    ∀ φ : Matrix (Fin d) (Fin d) K, IsUnit φ.det →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K L →
      lcv XT (matLat φ L) = lcv XS L + (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (detRatio XS XT φ v)

def IdxLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A B : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K A → Submodule.IsLattice K B →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)).Finite ∧
      lcv X B = lcv X A + 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w A B : ℝ)

def RatHermLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (jw H w T : ℝ)).Finite ∧
      lcv X T = - ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (jw H w T : ℝ)

def JwGram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K), IsLocBasis T w f →
      jw H w T = - vw w (gramR H f)

def FinsumConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (f : HeightOneSpectrum (𝓞 K) → ℝ),
    ∑ᶠ w, f (conjPl w) = ∑ᶠ w, f w

def LocBasisEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (L : Submodule (𝓞 K) (Fin d → K)),
    Submodule.IsLattice K L → ∀ w : HeightOneSpectrum (𝓞 K), ∃ f : Fin d → Fin d → K, IsLocBasis L w f

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.StatementACE
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

def StepA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (n D : ℕ) (M : Submodule (𝓞 K) (Fin n → K)) (π : Matrix (Fin D) (Fin n) K)
    (ι : Matrix (Fin D) (Fin D) K)
    (B : (Fin D → K) →ₗ[K] K) (P : (Fin n → K) →ₗ[K] K) (ζ : K) (σ : ℤ),
    ζ ≠ 0 → vw w ζ = 0 →
    (∀ F : Fin n → K, P F = ζ * B (ι.mulVec (π.mulVec F))) →
    (∀ F ∈ M, P F = 0 ∨ σ ≤ vw w (P F)) →
    ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ι (matLat π M)), B x = 0 ∨ σ ≤ vw w (B x)

def StepC : Prop :=
  ∀ (Φ Cs Q E : Type) [NormedAddCommGroup Φ] [InnerProductSpace ℂ Φ]
    [NormedAddCommGroup Cs] [InnerProductSpace ℂ Cs]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι : Q →ₗ[ℂ] E), Function.Surjective ι →
    ∀ (Ix : Type) [Fintype Ix] (Qp : Ix → Submodule ℂ Q), (⨆ p, Qp p) = ⊤ →
    ∀ (s : Ix → ℝ) (smin : ℝ), 0 < smin → (∀ p, smin ≤ s p) →
    (∀ p, ∀ x ∈ Qp p, ∀ y : Q, ⟪ι x, ι y⟫_ℂ = (s p : ℂ) * ⟪x, y⟫_ℂ) →
    ∀ (col : Φ → Cs) (k : ℝ), (∀ φ, ‖col φ‖ ≤ k * ‖φ‖) →
    ∀ (P : Cs → Q → ℂ) (p : ℝ), (∀ c F, ‖P c F‖ ≤ p * ‖c‖ * ‖F‖) →
    ∀ B : Φ → E → ℂ, (∀ φ F, B φ (ι F) = P (col φ) F) →
      0 ≤ k → 0 ≤ p → ∀ φ e, ‖B φ e‖ ≤ p * k / Real.sqrt smin * ‖φ‖ * ‖e‖

def StepCMean : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (nB p k s : InfinitePlace K → ℝ),
    (∀ v, 0 < nB v) → (∀ v, 0 < p v) → (∀ v, 0 < k v) → (∀ v, 0 < s v) →
    (∀ v, nB v ≤ p v * k v / Real.sqrt (s v)) →
      (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, Real.log (nB v ^ 2) ≤
        (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (Real.log (p v ^ 2) + Real.log (k v ^ 2)) -
          (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, Real.log (s v)

def BoundsSum : Prop :=
  ∀ (Pl J : Type) [Fintype J] (S : Finset Pl) (D : ℕ), 0 < D →
    ∀ (lcvR logκ LG E3 : ℝ) (lcvM L E1 E2 : J → ℝ) (l ell vG g : Pl → ℝ)
      (I Ic jT F err Jx η : Pl → J → ℝ),
    (∀ w, 0 ≤ l w) →
    lcvR ≤ (D : ℝ) * logκ + ∑ j, lcvM j +
      ∑ w ∈ S, l w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) →
    (∀ w ∈ S, vG w ≤ (D : ℝ) * g w) → ∑ w ∈ S, l w * g w ≤ LG →
    (∀ j, lcvM j / D ≤ L j) →
    (∀ w ∈ S, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ S, ∀ j, jT w j ≤ Jx w j * D + η w j) →
    (∀ j, ∑ w ∈ S, l w * (err w j + Jx w j) ≤ E1 j) →
    (∀ j, ∑ w ∈ S, l w * η w j / D ≤ E2 j) →
    ∑ w ∈ S, l w * (2 / ell w ^ 2) ≤ E3 →
      lcvR / D ≤ logκ + ∑ j, L j + 2 * ∑ j, ∑ w ∈ S, l w * F w j + LG + ∑ j, (E1 j + E2 j) + E3

end Formalism.DivisionValues
end
end

