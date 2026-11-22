import Mathlib

-- bundled from Formalism.SharpRestriction.Divisibility.RankTruncation.KapDLemma
section
noncomputable section

namespace ConditionalKappaBounds.KapD

def sigParC (k m : ℕ) (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (i : ℕ) : ℚ :=
  if h : i < k - 1 then v ⟨i, h⟩
  else if hb : i - (k - 1) < m then -b ⟨i - (k - 1), hb⟩ else 0

def aPlusC (k m t j : ℕ) (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (e : ℚ) (i : ℕ) : ℚ :=
  sigParC k m v b i + e - (((k + m - 1 + t : ℕ) : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((k : ℚ) + j - 1) - ((m : ℚ) - j)) / 2

def aMinusC (m t j : ℕ) (b : Fin m → ℚ) (e : ℚ) (c : ℕ) : ℚ :=
  (if h : j + c < m then b ⟨j + c, h⟩ else 0) - e - ((t : ℚ) + 1 + 2 * (c : ℚ)) / 2

def DProp : Prop := ∃ C : ℝ, ∀ (k m t j : ℕ), m + 3 ≤ k → 1 ≤ j → j ≤ m →
  ∀ (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (e : ℚ) (S η : ℝ),
    (∀ i, 0 ≤ ((v i : ℚ) : ℝ) ∧ ((v i : ℚ) : ℝ) ≤ S) → (∀ i, |((b i - e : ℚ) : ℝ)| ≤ η) →
    |((((∑ i : Fin (k + j - 1), aPlusC k m t j v b e i) + ∑ c : Fin (m - j), aMinusC m t j b e c : ℚ)) : ℝ) -
        ((k : ℝ) - 1) * ((e : ℚ) : ℝ)| ≤
      C * ((k : ℝ) * S + (m : ℝ) * η + (k : ℝ) * (((k + m * (t + 1) : ℕ) : ℝ) + t))

end ConditionalKappaBounds.KapD
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.RankTruncation.LocalAdditiveCharacterExpansion
section
noncomputable section

namespace ConditionalKappaBounds.L2

def LocalAdditiveCharacterExpansion : Prop := ∀ (p : ℕ) [Fact p.Prime] (f n : ℕ) (R : Type) [CommRing R] [IsDomain R] (ζ : R),
  IsPrimitiveRoot ζ p →
  ∀ φ : (Fin f × Fin n → ℚ_[p]) → R,
    (∀ x, φ x ≠ 0 → ∀ a, ‖x a‖ ≤ 1) →
    (∀ (x : Fin f × Fin n → ℚ_[p]) (z : Fin f × Fin n → ℤ_[p]),
      φ (fun a => x a + (p : ℚ_[p]) * (z a : ℚ_[p])) = φ x) →
    ∃ c : (Fin f × Fin n → ZMod p) → R, ∀ x : Fin f × Fin n → ℚ_[p],
      (p : R) ^ (f * n) * φ x =
        open Classical in
        if h : ∀ a, ‖x a‖ ≤ 1 then
          ∑ y : Fin f × Fin n → ZMod p,
            c y * ζ ^ (∑ a, PadicInt.toZMod (⟨x a, h a⟩ : ℤ_[p]) * y a).val
        else 0

end ConditionalKappaBounds.L2
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.RankTruncation.RkLemma
section
noncomputable section

namespace ConditionalKappaBounds.Rk

def RkProp : Prop := ∀ (dp f m r t : ℕ) (x Ct q d rd CRd : ℝ), 1 < x → 6 ≤ CRd →
  dp ≤ 2 * f * m → f ≤ r → m ≤ r → r < t → 2 ≤ t → (t : ℝ) ≤ x ^ Ct →
  x ^ (2 * Ct + 5) < q → x ^ (2 * Ct + 5) < d → Real.sqrt (q * d) ≤ rd →
  (dp : ℝ) ^ 2 ≤ rd ^ (CRd - 2)

end ConditionalKappaBounds.Rk
end
end

