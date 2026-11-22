import Mathlib

-- bundled from Formalism.LogVandermondeBounds.EvenOddPowerQuotientEqualityCases
section
namespace Formalism.LogVandermondeBounds.TaylorLogMetric

open Finset

def EvenOddPowerQuotientLowerBound : Prop :=
  ∀ (p i j : ℕ), 2 ≤ p → i ≤ j → (i, j) ≠ (0, 0) →
    ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1) ≤
      (((p : ℚ) ^ 2) ^ i + (p : ℚ) * ((p : ℚ) ^ 2) ^ j) / ((p : ℚ) ^ 2 - 1) - ((i : ℚ) + j + 1)

def EvenOddPowerQuotientEqualityCases : Prop :=
  ∀ (p : ℕ), 2 ≤ p →
    ((((p : ℚ) ^ 2) ^ 0 + (p : ℚ) * ((p : ℚ) ^ 2) ^ 1) / ((p : ℚ) ^ 2 - 1) - (0 + 1 + 1) =
      ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1)) ∧
    ((((p : ℚ) ^ 2) ^ 1 + (p : ℚ) * ((p : ℚ) ^ 2) ^ 1) / ((p : ℚ) ^ 2 - 1) - (1 + 1 + 1) =
      ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1))

def LegendreFactorialBound : Prop :=
  ∀ (p i : ℕ), p.Prime → 1 ≤ i → (p - 1) * padicValNat p i.factorial ≤ i - 1

open Classical in

noncomputable def coefL (p a : ℕ) : ℚ :=
  if h : ∃ j, a = (p ^ 2) ^ j then 1 / (p : ℚ) ^ (Classical.choose h) else 0

open Classical in
noncomputable def coefG (p a : ℕ) : ℚ :=
  if h : ∃ j, a = p * (p ^ 2) ^ j then 1 / (p : ℚ) ^ (Classical.choose h + 1) else 0

open Classical in

noncomputable def coefA (p a b : ℕ) : ℚ :=
  if h : ∃ i j, i ≤ j ∧ a = (p ^ 2) ^ i ∧ b = p * (p ^ 2) ^ j then
    1 / (p : ℚ) ^ (Classical.choose h + Classical.choose (Classical.choose_spec h) + 1) else 0

noncomputable def coefB (p a b : ℕ) : ℚ := coefA p b a

def LogarithmSeriesIdentities : Prop :=
  ∀ (p : ℕ), p.Prime →
    (∀ a : ℕ, (if p ∣ a then coefG p (a / p) else 0) = coefL p a - (if a = 1 then 1 else 0)) ∧
    (∀ a b : ℕ, (if p ∣ a ∧ p ∣ b then coefA p (a / p) (b / p) else 0) =
      (p : ℚ) * (coefG p a * coefL p b - coefB p a b))

def UnitaryDeterminantPhase : Prop :=
  ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) ℂ), δ ∈ Matrix.unitaryGroup (Fin n) ℂ →
    (1 - δ⁻¹).det ≠ 0 →
    (starRingEnd ℂ) (1 - δ⁻¹).det / (1 - δ⁻¹).det = (-1) ^ n * δ.det

end Formalism.LogVandermondeBounds.TaylorLogMetric
end

-- bundled from Formalism.LogVandermondeBounds.FinrankFiberSumZero
section
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Ops

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

def pair (f x : Fin r → k) : k := ∑ i, f i * x i

def opU (ψ : (Fin r → k) → R) (f : Fin r → k) : R :=
  ∑ x ∈ univ.filter (fun x => pair f x = 1), ψ x

def opD (φ : (Fin r → k) → R) (x : Fin r → k) : R :=
  ∑ f ∈ univ.filter (fun f => pair f x = 1), φ f

def diaP (c : kˣ) (φ : (Fin r → k) → R) (f : Fin r → k) : R := φ ((c : k) • f)

def diaV (c : kˣ) (ψ : (Fin r → k) → R) (x : Fin r → k) : R := ψ (((c⁻¹ : kˣ) : k) • x)

def nmP (φ : (Fin r → k) → R) (f : Fin r → k) : R := ∑ c : kˣ, diaP c φ f

def nmV (ψ : (Fin r → k) → R) (x : Fin r → k) : R := ∑ c : kˣ, diaV c ψ x

def trV (ψ : (Fin r → k) → R) : R := ∑ x ∈ univ.filter (fun x => x ≠ 0), ψ x

def trP (φ : (Fin r → k) → R) : R := ∑ f ∈ univ.filter (fun f => f ≠ 0), φ f

end Ops

def AdjointReformulated : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R]
    (ψ φ : (Fin r → k) → R),
    ∑ f, opU ψ f * φ f = ∑ x, ψ x * opD φ x

def DualCompositionReformulated : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R],
    2 ≤ r → ∀ (ψ : (Fin r → k) → R) (x : Fin r → k), x ≠ 0 →
      opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x
        - ((Fintype.card k : R)) ^ (r - 2) * nmV ψ x + ((Fintype.card k : R)) ^ (r - 2) * trV ψ

def CompositionWithDual : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R],
    2 ≤ r → ∀ (φ : (Fin r → k) → R) (f : Fin r → k), f ≠ 0 →
      opU (opD φ) f = ((Fintype.card k : R)) ^ (r - 1) * φ f
        - ((Fintype.card k : R)) ^ (r - 2) * nmP φ f + ((Fintype.card k : R)) ^ (r - 2) * trP φ

def EquivarianceReformulated : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R] (c : kˣ),
    (∀ ψ : (Fin r → k) → R, opU (diaV c ψ) = diaP c (opU ψ)) ∧
    (∀ φ : (Fin r → k) → R, opD (diaP c φ) = diaV c (opD φ))

def UnitsSumZero : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R],
    (∀ ψ : (Fin r → k) → R, (∀ y, y ≠ 0 → nmV ψ y = 0) →
      (∀ f, nmP (opU ψ) f = 0) ∧ trV ψ = 0 ∧
      (2 ≤ r → ∀ x, x ≠ 0 → opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x)) ∧
    (∀ φ : (Fin r → k) → R, (∀ f, f ≠ 0 → nmP φ f = 0) →
      (∀ x, nmV (opD φ) x = 0) ∧ trP φ = 0 ∧
      (2 ≤ r → ∀ f, f ≠ 0 → opU (opD φ) f = ((Fintype.card k : R)) ^ (r - 1) * φ f))

def ramSub (ι H X K : Type) [DecidableEq ι] [Group H] [Fintype H] [MulAction (ι → H) X] [Field K] :
    Submodule K (X → K) where
  carrier := {φ | ∀ (v : ι) (x : X), ∑ c : H, φ ((Pi.mulSingle v c : ι → H) • x) = 0}
  add_mem' := fun {a b} ha hb v x => by
    have h1 : ∑ c : H, a ((Pi.mulSingle v c : ι → H) • x) = 0 := ha v x
    have h2 : ∑ c : H, b ((Pi.mulSingle v c : ι → H) • x) = 0 := hb v x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [h1, h2, add_zero]
  zero_mem' := fun v x => by simp
  smul_mem' := fun s a ha v x => by
    have h1 : ∑ c : H, a ((Pi.mulSingle v c : ι → H) • x) = 0 := ha v x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, h1, mul_zero]

def FinrankFiberSumZero : Prop :=
  ∀ (ι H X K : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] [Field K],
    (∀ (g : ι → H) (x : X), g • x = x → g = 1) →
    Module.finrank K (ramSub ι H X K) * Fintype.card H ^ Fintype.card ι =
      Fintype.card X * (Fintype.card H - 1) ^ Fintype.card ι

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
end

-- bundled from Formalism.LogVandermondeBounds.LogRatioLowerBound
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def vandN (x : ℕ → ℝ) (N : ℕ) : ℝ := ∏ i ∈ range N, ∏ j ∈ Ico (i + 1) N, (x i - x j)

noncomputable def dimVN (x : ℕ → ℝ) (N : ℕ) : ℝ := vandN x N / ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)

noncomputable def zetaR (M : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M

noncomputable def rowPar (k : ℕ) (v b : ℕ → ℝ) : ℕ → ℝ := fun i => if i < k - 1 then v i else - b (i - (k - 1))

def PlaceData (x Δ a B : ℝ) (k m : ℕ) (u v b w : ℕ → ℝ) : Prop :=
  (∀ i, i < k - 1 → 0 ≤ v i ∧ v i ≤ k * (4 * Δ)) ∧
  (∀ i, i + 1 < k - 1 → v i - v (i + 1) = 4 * Δ) ∧
  (∀ i, i < k - 1 → v i < u i ∧ u (i + 1) < v i) ∧
  (- b 0 < u (k - 1)) ∧
  ((u 0 ≤ 2 * a ∧ - a ≤ u (k - 1)) ∨
    (k * (4 * Δ) ≤ u 0 - v 0 ∧ u 0 - v 0 ≤ 2 * k * (4 * Δ) ∧ u (k - 1) = v (k - 2) - 1 / 2)) ∧
  (∀ j, j < m → b j < w j ∧ |w j - b j| ≤ b j / x) ∧
  (∀ j, j + 1 < m → w j < b (j + 1) ∧ 1 ≤ b (j + 1) - b j) ∧
  k * (4 * Δ) ≤ b 0 / x ∧ w (m - 1) ≤ 2 * B

def LogRatioLowerBound : Prop :=
  ∀ (ε C₀ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → ∃ C : ℝ, ∀ (x : ℝ), 1 ≤ x →
    let L := x ^ ε
    let B := Real.exp L
    let a := x * B
    ∀ (f m k : ℕ) (vE Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ)
      (Dstar dstar massk massr Isig Ipi : ℝ) (Lval : ℕ → ℝ),
    1 ≤ f → 1 ≤ m → 2 ≤ k → (k : ℝ) ≤ x ^ C₀ →
    Real.pi ≤ vE → Real.log vE ≤ L → 1 ≤ Δ → 1 ≤ g₁ → 1 ≤ g₂ →
    (∀ ρ, ρ < f → PlaceData x Δ a B k m (u ρ) (v ρ) (b ρ) (w ρ)) →
    0 < massk → 0 < massr → 0 < Isig → 0 < Ipi →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M ∧ |Real.log (Lval M)| ≤ f * Real.log (zetaR M)) →
    (hmass : massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) →
    (hidx : ((2 : ℝ) ^ (2 * f))⁻¹ * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) ≤ Isig / Ipi) →
    (hD : (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m) ≤ Dstar) →
    (hd : dstar = massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k) →
    (∑ j ∈ range m, (1 / (f : ℝ)) * ∑ ρ ∈ range f, Real.log (w ρ j * vE / Real.pi))
        + m * (Real.log g₁ + Real.log g₂) - C * (L + (m : ℝ) ^ 2 * L / k)
      ≤ (1 / ((f : ℝ) * k)) * Real.log (Dstar / dstar)

end Formalism.LogVandermondeBounds.StandardLattice
end

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def BlockDimensionIdentities : Prop :=
  ∀ (k m rS r : ℕ), 2 ≤ m → Even m → rS = m / 2 - 1 → r = k + 1 + 2 * rS →
    let blockOf : ℕ → ℕ := fun i => if i < rS then i else if i < rS + k + 1 then rS else i - k
    let dimN : ℕ := ((range r ×ˢ range r).filter
      (fun p : ℕ × ℕ => p.1 < p.2 ∧ blockOf p.1 ≠ blockOf p.2)).card
    (r : ℤ) = k + m - 1 ∧
    2 * (dimN : ℤ) = (r : ℤ) ^ 2 - ((k : ℤ) + 1) ^ 2 - 2 * rS ∧
    2 * ((r : ℤ) ^ 2 - dimN) - (k : ℤ) * (k - 1) = (r : ℤ) ^ 2 + 3 * k + 1 + 2 * rS ∧
    2 * (k : ℤ) ^ 2 - (k : ℤ) * (k - 1) = (k : ℤ) * (k + 1) ∧
    ((r : ℤ) ^ 2 + 3 * k + 1 + 2 * rS) - (k : ℤ) * (k + 1) = (m : ℤ) * (2 * k + m - 1)

def CardGeneralLinear : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * (n - 1) / 2) * (Fintype.card F : ℝ) ^ (n * (n + 1) / 2) *
        ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1))

def CardUnitriangular : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    Nat.card {A : Matrix (Fin n) (Fin n) F // (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1} =
      Fintype.card F ^ (n * (n - 1) / 2)

def EulerProductBounds : Prop :=
  ∀ (q : ℝ), 3 ≤ q → ∀ n : ℕ,
    1 / 2 ≤ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ∧ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ≤ 1

def CardStabilizerVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (v : Fin n → F), v ≠ 0 →
    Fintype.card {A : GL (Fin n) F // Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v} *
      (Fintype.card F ^ n - 1) = Fintype.card (GL (Fin n) F)

def PrimeOrderFinrank : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n g : ℕ) (A : Matrix (Fin n) (Fin n) K),
    g.Prime → A ^ g = 1 → A ≠ 1 → g - 1 ≤ Module.finrank ℚ K * n

def PrimePowerSubgroupTrivial : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n g : ℕ) (Γ : Subgroup (GL (Fin n) K)),
    g.Prime → Finite Γ → (∃ e : ℕ, Nat.card Γ = g ^ e) → Module.finrank ℚ K * n < g - 1 → Γ = ⊥

noncomputable def vandLog {N : ℕ} (u : Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b ∈ univ.filter (fun b => a < b), Real.log (u a - u b)

def WordPair (n : ℕ) (Δ : ℝ) (u u' : Fin (n + 2) → ℝ) : Prop :=
  0 < Δ ∧
  (∀ a b, a < b → 1 ≤ u a - u b) ∧ (∀ a b, a < b → 1 ≤ u' a - u' b) ∧
  (∀ i, |u i - u' i| ≤ Δ) ∧ u 0 = u' 0 ∧ u (Fin.last (n + 1)) = u' (Fin.last (n + 1)) ∧
  (∀ i j : Fin (n + 2), 1 ≤ i.val → j.val = i.val + 1 → j.val ≤ n →
    3 * Δ ≤ u i - u j ∧ 3 * Δ ≤ u' i - u' j)

def LogVandermondeVariation : Prop :=
  ∀ (n : ℕ) (Δ : ℝ) (u u' : Fin (n + 2) → ℝ), WordPair n Δ u u' →
    |vandLog u - vandLog u'| ≤ 6 * (n + 2) * (1 + Real.log (n + 2)) + 2 * Real.log (1 + Δ)

def LogVandermondeVariationOfLogLe : Prop :=
  ∀ (n : ℕ) (Δ : ℝ) (u u' : Fin (n + 2) → ℝ), WordPair n Δ u u' → Real.log (1 + Δ) ≤ n + 2 →
    |vandLog u - vandLog u'| ≤ 8 * (n + 2) * (1 + Real.log (n + 2))

def LogVandermondeVariationUnbounded : Prop :=
  ∀ M : ℝ, ∃ (Δ : ℝ) (u u' : Fin 4 → ℝ), 1 ≤ Δ ∧ WordPair 2 Δ u u' ∧ M ≤ |vandLog u - vandLog u'|

def CardBilinearLevel : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (M : ℕ) (β : F), 1 ≤ M → β ≠ 0 →
    Fintype.card {p : (Fin M → F) × (Fin M → F) // ∑ i, p.1 i * p.2 i = β} =
      Fintype.card F ^ (M - 1) * (Fintype.card F ^ M - 1)

def CardHermitianLevel : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] [DecidableEq L] (q M : ℕ) (β : L),
    Fintype.card L = q ^ 2 → 1 ≤ M → β ≠ 0 → β ^ q = β →
    (Fintype.card {x : Fin M → L // ∑ i, x i ^ (q + 1) = β} : ℤ) =
      (q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M)

def VandermondeAppendNeg : Prop :=
  ∀ (R : Type) [CommRing R] (a m : ℕ) (v : Fin a → R) (b : Fin m → R),
    (∏ i, ∏ j ∈ univ.filter (fun j => i < j),
        ((Fin.append v (fun j => - b j) : Fin (a + m) → R) i -
          (Fin.append v (fun j => - b j) : Fin (a + m) → R) j)) =
      (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (v i - v j)) *
      (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (b j - b i)) *
      ∏ i, ∏ j, (v i + b j)

def ProdFactorialShift : Prop :=
  ∀ k r : ℕ, k ≤ r →
    (∏ M ∈ Ico (k + 1) (r + 1), (M - 1).factorial) * ∏ i ∈ range k, i.factorial =
      ∏ i ∈ range r, i.factorial

end Formalism.LogVandermondeBounds.StandardLattice
end

-- bundled from Formalism.LogVandermondeBounds.MultinomialPowerBound
section
namespace Formalism.LogVandermondeBounds.flipTwoThree

open Finset

def Interlace {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : Prop :=
  Antitone lam ∧ ∀ i : Fin n, lam i.succ ≤ nu i ∧ nu i ≤ lam i.castSucc

def B0 {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : ℤ := ∑ i, (nu i - lam i.succ)

def len {n : ℕ} (lam : Fin (n + 1) → ℤ) (i : Fin n) : ℤ := lam i.castSucc - lam i.succ

noncomputable def Iset {n : ℕ} (lam : Fin (n + 1) → ℤ) (b : ℤ) (i : Fin n) : Finset ℤ :=
  Icc (lam i.succ) (lam i.succ + min (len lam i) b)

def ev {n : ℕ} (nu' : Fin n → ℤ) (x : ℤ) : ℤ := ∏ j, (nu' j - (j : ℤ) - x)

noncomputable def sep {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu nu' : Fin n → ℤ) : ℤ :=
  ∏ i, ∏ y ∈ (Iset lam (B0 lam nu) i).erase (nu i), ev nu' (y - (i : ℤ))

def InterlacingSeparation : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ), Interlace lam nu →
    (∀ nu' : Fin n → ℤ, Interlace lam nu' → B0 lam nu' = B0 lam nu →
      ∀ i, nu' i ∈ Iset lam (B0 lam nu) i) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint ((Iset lam (B0 lam nu) i).image (fun y => y - (i : ℤ)))
      ((Iset lam (B0 lam nu) j).image (fun y => y - (j : ℤ)))) ∧
    sep lam nu nu ≠ 0 ∧
    |sep lam nu nu| ≤ (lam 0 - lam (Fin.last n) + n + 1) ^
      (n * ∑ i, (min (len lam i) (B0 lam nu)).toNat) ∧
    (∀ nu' : Fin n → ℤ, Interlace lam nu' → B0 lam nu' = B0 lam nu → nu' ≠ nu → sep lam nu nu' = 0)

def MinRatioPowerExponentialBound : Prop :=
  ∀ (n g : ℕ), 1 ≤ g →
    let e : ℝ := if n = 0 then 1 else min 1 ((g : ℝ) / n)
    (e ^ g)⁻¹ * (1 + e) ^ (n + g) ≤ (2 * Real.exp 1 * max 1 ((n : ℝ) / g)) ^ g

def GammaIntegralBound : Prop :=
  ∀ (v : ℝ) (g : ℕ), 0 ≤ v →
    MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g) (Set.Ioi 0) ∧
    ∫ u in Set.Ioi (0 : ℝ), Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g ≤
      (1 + 4 * g * v / Real.pi) ^ g

def AmgmSumLowerBoundOfProd : Prop :=
  ∀ (f : ℕ) (v : ℝ) (x : Fin f → ℝ), 1 ≤ f → 0 < v → (∀ i, 0 < x i) →
    ((2 * v) ^ f)⁻¹ ≤ ∏ i, x i → (f : ℝ) / v ≤ 2 * ∑ i, x i

noncomputable def hookF {N : ℕ} (nu : Fin N → ℕ) : ℝ :=
  (∏ i : Fin N, ((nu i + N - 1 - i : ℕ).factorial : ℝ)) /
    ∏ i : Fin N, ∏ j ∈ univ.filter (fun j => i < j), (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ)

def HookProductBounds : Prop :=
  ∀ (N : ℕ) (nu : Fin (N + 1) → ℕ), Antitone nu →
    hookF nu ≤ ∏ i : Fin (N + 1), ((nu i + N - i : ℕ).factorial : ℝ) ∧
    ∑ i : Fin (N + 1), Real.log ((nu i + N - i : ℕ).factorial : ℝ)
        - ((N : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + N + 1) ≤ Real.log (hookF nu) ∧
    hookF nu / ∏ i : Fin (N + 1), ((nu i).factorial : ℝ) ≤ ((nu 0 : ℝ) + N + 1) ^ ((N + 1) ^ 2)

def MultinomialPowerBound : Prop :=
  ∀ (k : ℕ) (α : Fin k → ℕ),
    ((∑ i, α i).factorial : ℝ) / ∏ i, ((α i).factorial : ℝ) ≤ (k : ℝ) ^ (∑ i, α i)

end Formalism.LogVandermondeBounds.flipTwoThree
end

