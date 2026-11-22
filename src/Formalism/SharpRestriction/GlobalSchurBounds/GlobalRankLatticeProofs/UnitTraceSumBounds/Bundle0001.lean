import Mathlib

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBFiLower
section
noncomputable section

open Finset MeasureTheory

namespace Formalism.MainNotions.Ext.CutB

abbrev cBNC {N : ℕ} (ε : Fin N → Bool) : Type := {ab : Fin N × Fin N // ab.1 < ab.2 ∧ ε ab.1 ≠ ε ab.2}

def cBpp {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => if h : a < b ∧ ε a ≠ ε b then z ⟨(a, b), h⟩
    else if h' : b < a ∧ ε b ≠ ε a then star (z ⟨(b, a), h'⟩) else 0

theorem cBpp_herm {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ) : (cBpp ε z).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, cBpp]
  by_cases h1 : a < b ∧ ε a ≠ ε b
  · have h2 : ¬ (b < a ∧ ε b ≠ ε a) := fun h => absurd h1.1 (not_lt.2 h.1.le)
    rw [dif_neg h2, dif_pos h1, dif_pos h1, star_star]
  · by_cases h3 : b < a ∧ ε b ≠ ε a
    · rw [dif_pos h3, dif_neg h1, dif_pos h3]
    · simp [h1, h3]

def cBp {N : ℕ} (ε : Fin N → Bool) : ℕ := (univ.filter (fun a => ε a = true)).card

def cBq {N : ℕ} (ε : Fin N → Bool) : ℕ := (univ.filter (fun a => ε a = false)).card

def cBhs {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖ ^ 2

def cBlead {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) (hi : i ≤ N) : Matrix (Fin i) (Fin i) ℂ :=
  A.submatrix (Fin.castLE hi) (Fin.castLE hi)

def cBF {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) (hi : i ≤ N) : ℝ :=
  Real.log ((cBlead (NormedSpace.exp X) i hi).det).re

def cBV {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) : ℝ :=
  cBhs ((1 - Matrix.diagonal (fun a : Fin N => if a.val < i then (1 : ℂ) else 0)) * X *
    Matrix.diagonal (fun a : Fin N => if a.val < i then (1 : ℂ) else 0))

def cBPh {N : ℕ} (lam : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ i : Fin N, if h : i.val + 1 < N then (lam i - lam ⟨i.val + 1, h⟩ + 1) * cBF X (i.val + 1) h.le else 0

def cBsh (u : ℝ) : ℝ := if u = 0 then 1 else Real.sinh u / u

def cBJ {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ) : ℝ :=
  ∏ a, ∏ b ∈ univ.filter (fun b : Fin N => a < b),
    cBsh ((cBpp_herm ε z).eigenvalues a - (cBpp_herm ε z).eigenvalues b)

def cBQ {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) (z : cBNC ε → ℂ) : ℝ :=
  ∑ pr : cBNC ε, (lam pr.1.1 - lam pr.1.2 + ((pr.1.2.val : ℝ) - pr.1.1.val)) * ‖z pr‖ ^ 2

def cBPi {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) : ℝ :=
  ∏ a, ∏ b ∈ univ.filter (fun b : Fin N => a < b ∧ ε a ≠ ε b), Real.pi / (lam a - lam b + ((b.val : ℝ) - a.val))

def cBFiLower : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian →
    (∀ a b, ε a = ε b → X a b = 0) → ∀ ep : ℝ, ep ≤ 1 →
    Real.sqrt (2 * (min (cBp ε) (cBq ε) : ℕ)) * Real.sqrt (cBhs X) ≤ ep →
    ∀ (i : ℕ) (hi : i ≤ N), (1 - ep) / 2 * cBV X i ≤ cBF X i hi

def cBFiUpper : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian →
    (∀ a b, ε a = ε b → X a b = 0) →
    Real.sqrt (2 * (min (cBp ε) (cBq ε) : ℕ)) * Real.sqrt (cBhs X) ≤ 1 →
    ∀ (i : ℕ) (hi : i ≤ N), cBF X i hi ≤ cBV X i

def cBFiScale : Prop :=
  ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian → (∀ a, X a a = 0) →
    ∀ (i : ℕ) (hi : i ≤ N), 0 ≤ cBF X i hi ∧ ∀ t : ℝ, 1 ≤ t → t * cBF X i hi ≤ cBF ((t : ℂ) • X) i hi

def cBInner : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ε₀ h₀ : ℝ),
    1 ≤ cBp ε → 1 ≤ cBq ε → StrictAnti lam → (∀ a b, ε a ≠ ε b → h₀ ≤ |lam a - lam b|) →
    Real.exp (-(N : ℝ)) ≤ ε₀ → ε₀ < 1 / 2 →
    8192 * ((min (cBp ε) (cBq ε) : ℕ) : ℝ) * ((cBp ε : ℝ) * cBq ε) ^ 3 * Real.log N / ε₀ ^ 2 ≤ h₀ →
    ∀ z : cBNC ε → ℂ,
      2 * ((min (cBp ε) (cBq ε) : ℕ) : ℝ) * cBhs (cBpp ε z) ≤ (ε₀ / (8 * ((cBp ε : ℝ) * cBq ε))) ^ 2 →
      (1 - 2 * (ε₀ / (8 * ((cBp ε : ℝ) * cBq ε)))) * cBQ ε lam z ≤
        2 * cBPh lam (cBpp ε z) - Real.log (cBJ ε z)

def cBTail : Prop :=
  ∀ (ι : Type) [Fintype ι] (w : ι → ℝ) (G : (ι → ℂ) → ℝ) (R δ : ℝ), (∀ j, 0 < w j) → 0 < R → 0 ≤ δ →
    (∀ z, 0 ≤ G z) → Measurable G →
    (∀ Y : ι → ℂ, ∑ j, ‖Y j‖ ^ 2 = R ^ 2 → ∃ κ : ℝ, 2 * (Fintype.card ι : ℝ) ≤ κ ∧
      (∀ s : ℝ, 1 ≤ s → G ((s : ℂ) • Y) ≤ Real.exp (-(κ * s))) ∧
      Real.exp (-κ) ≤ δ * (Real.Gamma (Fintype.card ι) / (2 * (∑ j, w j * ‖Y j‖ ^ 2) ^ Fintype.card ι))) →
    IntegrableOn G {z : ι → ℂ | R ^ 2 < ∑ j, ‖z j‖ ^ 2} ∧
      ∫ z in {z : ι → ℂ | R ^ 2 < ∑ j, ‖z j‖ ^ 2}, G z ≤ δ * ∫ z : ι → ℂ, Real.exp (-∑ j, w j * ‖z j‖ ^ 2)

def cBBall : Prop :=
  ∀ (ι : Type) [Fintype ι] (t : ℝ), 0 ≤ t →
    (volume {z : ι → ℂ | ∑ j, ‖z j‖ ^ 2 ≤ t}).toReal =
      Real.pi ^ Fintype.card ι * t ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ)

def cBIntLow : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ε₀ h₀ : ℝ),
    StrictAnti lam → (∀ a b, ε a ≠ ε b → h₀ ≤ |lam a - lam b|) →
    Real.exp (-(N : ℝ)) ≤ ε₀ → ε₀ < 1 / 2 →
    8192 * ((min (cBp ε) (cBq ε) : ℕ) : ℝ) * ((cBp ε : ℝ) * cBq ε) ^ 3 * Real.log N / ε₀ ^ 2 ≤ h₀ →
    Integrable (fun z : cBNC ε → ℂ => Real.exp (-(2 * cBPh lam (cBpp ε z))) * cBJ ε z) ∧
    0 < ∫ z : cBNC ε → ℂ, Real.exp (-(2 * cBPh lam (cBpp ε z))) * cBJ ε z ∧
    ∫ z : cBNC ε → ℂ, Real.exp (-(2 * cBPh lam (cBpp ε z))) * cBJ ε z ≤ (1 + 0.58 * ε₀) * cBPi ε lam

def cBPhBall : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (Λ : ℝ) (z : cBNC ε → ℂ),
    (∀ a b : Fin N, a < b → ((b.val : ℝ) - a.val) ≤ lam a - lam b) → (∀ a b, lam a - lam b ≤ Λ) →
    2 * ((min (cBp ε) (cBq ε) : ℕ) : ℝ) * cBhs (cBpp ε z) ≤ 1 →
    cBPh lam (cBpp ε z) ≤ Λ * cBhs (cBpp ε z)

end Formalism.MainNotions.Ext.CutB
end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FGTorsionFreeGen
section
namespace Formalism.MainNotions.Ext.CutC

open NumberField

def stdLat (R K : Type) [CommRing R] [Field K] [Algebra R K] (r : ℕ) : Submodule R (Fin r → K) :=
  Submodule.span R (Set.range fun i : Fin r => (Pi.single i (1 : K) : Fin r → K))

def vecK (R K : Type) [CommRing R] [Field K] [Algebra R K] {r : ℕ} (x : Fin r → R) : Fin r → K :=
  fun i => algebraMap R K (x i)

def supLat (R K : Type) [CommRing R] [Field K] [Algebra R K] (ϖ : R) {r : ℕ} (x : Fin r → R) :
    Submodule R (Fin r → K) :=
  stdLat R K r ⊔ Submodule.span R {(algebraMap R K ϖ)⁻¹ • vecK R K x}

def SupLatLine : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R), Irreducible ϖ → ∀ r : ℕ,
    (∀ x : Fin r → R, (∃ i, ¬ ϖ ∣ x i) →
      IsSimpleModule R ((supLat R K ϖ x) ⧸ (stdLat R K r).comap (supLat R K ϖ x).subtype)) ∧
    (∀ x y : Fin r → R, (∃ i, ¬ ϖ ∣ x i) → (∃ i, ¬ ϖ ∣ y i) →
      (supLat R K ϖ x = supLat R K ϖ y ↔ ∃ c : R, IsUnit c ∧ ∀ i, ϖ ∣ x i - c * y i)) ∧
    (∀ M : Submodule R (Fin r → K), stdLat R K r ≤ M →
      IsSimpleModule R (M ⧸ (stdLat R K r).comap M.subtype) →
      ∃ x : Fin r → R, (∃ i, ¬ ϖ ∣ x i) ∧ M = supLat R K ϖ x)

def FGTorsionFreeGen : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M],
    ∃ s : Finset M, s.card ≤ Module.finrank R M + 1 ∧ Submodule.span R (s : Set M) = ⊤

def IndexMatNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (A : Matrix (Fin r) (Fin r) (𝓞 E)), A.det ≠ 0 →
    Nat.card ((Fin r → 𝓞 E) ⧸ LinearMap.range A.mulVecLin) = (Algebra.norm ℤ A.det).natAbs

def IndexMulLattice : Prop :=
  ∀ (E Y : Type) [Field E] [NumberField E] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] [NoZeroSMulDivisors (𝓞 E) Y] (M : ℕ), 1 ≤ M →
    Nat.card (Y ⧸ LinearMap.range ((M : 𝓞 E) • LinearMap.id : Y →ₗ[𝓞 E] Y)) = M ^ (Module.finrank ℚ E * Module.finrank (𝓞 E) Y)

def DualIndex : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (B : LinearMap.BilinForm ℚ V),
    B.Nondegenerate → ∀ L₀ L : Submodule ℤ V, L₀ ≤ L → L.FG →
    Submodule.span ℚ (L₀ : Set V) = ⊤ →
    Nat.card ((B.dualSubmodule L₀) ⧸ (B.dualSubmodule L).comap (B.dualSubmodule L₀).subtype) =
      Nat.card (L ⧸ L₀.comap L.subtype)

end Formalism.MainNotions.Ext.CutC
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LocBasisPlace
section
open Finset

namespace Formalism.MainNotions.Ext

def LeafOne : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ t : PowerSeries ℚ, PowerSeries.constantCoeff t = 0 →
    (∀ n : ℕ, ∑ k ∈ range (n + 1), PowerSeries.coeff n (t ^ (p ^ (2 * k))) / (p : ℚ) ^ k = if n = 1 then 1 else 0) →
    (∑ k ∈ range (p ^ 3 + 1), PowerSeries.coeff (p ^ 3) (t ^ (p ^ (2 * k + 1))) / (p : ℚ) ^ (k + 1)) ≠ 0 ∧
    padicValRat p (∑ k ∈ range (p ^ 3 + 1), PowerSeries.coeff (p ^ 3) (t ^ (p ^ (2 * k + 1))) / (p : ℚ) ^ (k + 1))
      = -((p : ℤ) + 1)

end Formalism.MainNotions.Ext

open NumberField

namespace Formalism.MainNotions.Ext

def RayBoundIQ : Prop :=
  ∀ (K0 : Type) [Field K0] [NumberField K0], Module.finrank ℚ K0 = 2 → IsEmpty (K0 →+* ℝ) →
    ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ →
      1 ≤ Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) ∧
      (Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) : ℝ) ≤
        4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ)

def NormOnePow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ x, c (c x) = x) →
    ∀ 𝔞 𝔟 : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) → 𝔞 * 𝔟 = 1 →
      ∃ (h : ℕ) (z : E), 0 < h ∧ z * c z = 1 ∧ 𝔞 ^ h = Submodule.span (𝓞 E) {z}

def LocBasisPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ρ : E →+* ℂ_[p]) (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)), L.FG → Submodule.span E (L : Set (Fin N → E)) = ⊤ →
    ∃ P : Matrix (Fin N) (Fin N) E, P.det ≠ 0 ∧
      (∀ a, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ s • P.transpose a ∈ L) ∧
      ∀ x ∈ L, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, s • x = ∑ a, c a • P.transpose a

def LocBasisSemi : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (p : ℕ), p.Prime →
    ∀ Y : Submodule (𝓞 K) V, Y.FG →
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧
      (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • b i ∈ Y) ∧
      ∀ y ∈ Y, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin r → 𝓞 K, (s : K) • y = ∑ i, ((c i : 𝓞 K) : K) • b i

end Formalism.MainNotions.Ext
end

