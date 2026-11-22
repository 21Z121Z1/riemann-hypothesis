import Formalism.LogVandermondeBounds.Bundle0001

-- bundled from Formalism.LogVandermondeBounds.GaussOperatorProductFormula
section
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Ops

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}

def opGs (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, ψ (c : k) * φ ((c : k) • f)

def opGsStar (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, (starRingEnd ℂ) (ψ (c : k)) * φ (((c⁻¹ : kˣ) : k) • f)

def opFF (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (x : Fin r → k) : ℂ :=
  ∑ f ∈ univ.filter (fun f => f ≠ 0), ψ (pair f x) * φ f

end Ops

def GaussOperatorProductFormula : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (φ : (Fin r → k) → ℂ) (f : Fin r → k),
      opGs ψ (opGsStar ψ φ) f = (Fintype.card k : ℂ) * φ f - nmP φ f

def FourierEqDownGauss : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ),
    ∀ (φ : (Fin r → k) → ℂ), (∀ f, f ≠ 0 → nmP φ f = 0) →
      ∀ x : Fin r → k, opFF ψ φ x = opD (opGs ψ φ) x

def FourierIsometryNormKernel : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (φ φ' : (Fin r → k) → ℂ), (∀ f, f ≠ 0 → nmP φ f = 0) → (∀ f, f ≠ 0 → nmP φ' f = 0) →
      ∑ x ∈ univ.filter (fun x => x ≠ 0), (starRingEnd ℂ) (opFF ψ φ x) * opFF ψ φ' x =
        (Fintype.card k : ℂ) ^ r * ∑ f ∈ univ.filter (fun f => f ≠ 0), (starRingEnd ℂ) (φ f) * φ' f

def GaussOperatorAdjoint : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ) (φ φ' : (Fin r → k) → ℂ),
    ∑ f, (starRingEnd ℂ) (opGs ψ φ f) * φ' f = ∑ f, (starRingEnd ℂ) (φ f) * opGsStar ψ φ' f

def FourierIntertwinesDiagonal : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ),
    ∀ (φ : (Fin r → k) → ℂ) (c : kˣ), opFF ψ (diaP c φ) = diaV c (opFF ψ φ)

def FourierMapsNormKernel : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ),
    ∀ (φ : (Fin r → k) → ℂ), (∀ f, f ≠ 0 → nmP φ f = 0) →
      ∀ x : Fin r → k, x ≠ 0 → nmV (opFF ψ φ) x = 0

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
end

-- bundled from Formalism.LogVandermondeBounds.LogRatioUpperBound
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def plusSign (k i : ℕ) : Bool := decide (i < k - 1 ∨ (i - (k - 1)) % 2 = 0)

def nBetween (k a b : ℕ) : ℕ := ((Ioo a b).filter (fun c => plusSign k c ≠ plusSign k a)).card

noncomputable def dTau (k m : ℕ) (lam : ℕ → ℝ) : ℝ :=
  (∏ a ∈ range (k - 1 + m), ∏ b ∈ (Ico (a + 1) (k - 1 + m)).filter (fun b => plusSign k b = plusSign k a),
      (lam a - lam b + nBetween k a b)) /
    ((∏ i ∈ range (k - 1 + m / 2), ((i.factorial : ℕ) : ℝ)) * ∏ i ∈ range (m / 2), ((i.factorial : ℕ) : ℝ))

def LogRatioUpperBound : Prop :=
  ∀ (ε C₀ C₃ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → 1 ≤ C₃ → ∃ C : ℝ, ∀ (x : ℝ), 1 ≤ x →
    let L := x ^ ε
    let B := Real.exp L
    let a := x * B
    ∀ (f m k : ℕ) (vE Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ)
      (Dstar dstar massk massr Isig Ipi : ℝ) (Lval dsig : ℕ → ℝ),
    1 ≤ f → 2 ≤ m → Even m → 2 ≤ k → (m : ℝ) ^ 2 * L ≤ k → (k : ℝ) ≤ x ^ C₀ →
    Real.pi ≤ vE → Real.log vE ≤ L → 1 ≤ Δ → 1 ≤ g₁ → 1 ≤ g₂ →
    Real.log g₁ ≤ C₀ * L → Real.log g₂ ≤ C₀ * L →
    (∀ ρ, ρ < f → PlaceData x Δ a B k m (u ρ) (v ρ) (b ρ) (w ρ) ∧
      (∀ i j, i < j → j < k → 1 ≤ u ρ i - u ρ j)) →
    0 < massk → 0 < massr → 0 < Isig → 0 < Ipi →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M ∧ |Real.log (Lval M)| ≤ f * Real.log (zetaR M)) →
    (hmass : massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) →
    (hidx : Isig / Ipi ≤ (2 : ℝ) ^ (2 * f) * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2)) →
    (hD : Dstar = massr * Isig * ∏ ρ ∈ range f, dsig ρ) →
    (h3 : ∀ ρ, ρ < f → 0 < dsig ρ ∧ dsig ρ ≤ 4 * dTau k m (rowPar k (v ρ) (b ρ)) *
      (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) *
        (v ρ 0 + b ρ (m - 1))) ^ ((k - 1 + m / 2) * (m / 2))) →
    (hd : dstar = massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k) →
    (1 / ((f : ℝ) * k)) * Real.log (Dstar / dstar) ≤ C * m * L

end Formalism.LogVandermondeBounds.StandardLattice
end

-- bundled from Formalism.LogVandermondeBounds.VandPlace
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def VandPlace : Prop :=
  ∀ (ε x : ℝ), 0 < ε → 1 ≤ x → ∀ (k m : ℕ) (Δ : ℝ) (u v b w : ℕ → ℝ), 2 ≤ k → 1 ≤ m → 1 ≤ Δ →
    PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w →
    0 < vandN u k ∧ 0 < vandN (rowPar k v b) (k - 1 + m) ∧
    ((k : ℝ) - 1) * ∑ j ∈ range m, Real.log (b j)
      - 2 * k * Real.log (8 * (x * Real.exp (x ^ ε))) - 2 * k * (1 + Real.log k)
      ≤ Real.log (vandN (rowPar k v b) (k - 1 + m)) - Real.log (vandN u k)

end Formalism.LogVandermondeBounds.StandardLattice
end

