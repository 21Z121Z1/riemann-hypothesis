import Mathlib

-- bundled from Formalism.LogFactorialBounds.DepthIIExponent
section
noncomputable section

namespace Formalism.LogFactorialBounds

open Finset

def HeightSteps : Prop :=
  ∀ (D : ℕ) (hZ I ε : ℕ → ℝ) (δ lρ g : ℝ),
    (∀ l < D, hZ (l + 1) = hZ l + I l - ε l) →
    (∀ l < D, δ * (lρ - g) ≤ I l ∧ I l ≤ δ * (Real.log 2 + lρ)) →
    (∀ l < D, 0 ≤ ε l ∧ ε l ≤ δ) →
    hZ 0 + D * δ * (lρ - g - 1) ≤ hZ D ∧ hZ D ≤ hZ 0 + D * δ * (Real.log 2 + lρ)

def HSAssembly : Prop :=
  ∀ (D T : ℕ) (δ d h J g lρ lβ lΛD lΛT c₁ rkZ cor hS degLc degZ degQ degMT : ℝ)
    (degGr : ℕ → ℝ),
    1 ≤ D → 2 * D ≤ T → 0 < δ → 0 < d → 0 ≤ g → 0 ≤ lρ → 0 ≤ lβ → 0 ≤ lΛD → 0 ≤ lΛT →
    0 ≤ rkZ → 0 ≤ cor →
    rkZ + cor = (1 - ((T - 1).choose D : ℝ) * δ / d) * d →
    ((D : ℝ) + 1) * δ * h + D * δ * (lρ - g - 1) ≤ hS →
    hS ≤ ((D : ℝ) + 1) * δ * h + D * δ * (Real.log 2 + lρ) →
    -(δ * J) - ((D : ℝ) + 3) * hS ≤ degLc →
    (∀ a < T - D, ((a + D - 1).choose (D - 1) : ℝ) *
        (degLc + ((T : ℝ) - a) * hS - δ * (a * (Real.log 2 + lρ) + c₁)) ≤ degGr a) →
    -(rkZ * (((T - D : ℕ) : ℝ) * (Real.log 2 + lρ + lβ / 2) + lΛD)) ≤ degZ →
    -(cor * lΛT) ≤ degQ →
    (∑ a ∈ range (T - D), degGr a) + degZ + degQ ≤ degMT →
    (((T - 1).choose D : ℝ) * δ / d) *
        ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - 2 * D * lρ - D * ((D : ℝ) + 3) * Real.log 2
          - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2) - c₁)
      - (1 - ((T - 1).choose D : ℝ) * δ / d) * ((T : ℝ) * (Real.log 2 + lρ + lβ / 2) + lΛD + lΛT)
      ≤ degMT / d

def ShareBound : Prop :=
  ∀ (D T A : ℕ) (ρ δ d : ℝ), 1 ≤ D → 2 * D ≤ T → 0 ≤ ρ → ρ < 1 →
    (A : ℝ) ≤ ((T : ℝ) + D + 3) / (1 - ρ) →
    0 < δ → 0 < d → d ≤ ((A + D).choose D : ℝ) * δ →
    1 - ((T - 1).choose D : ℝ) * δ / d ≤ D * ρ + 6 * (D : ℝ) ^ 2 / T

def ShareBound4 : Prop :=
  ∀ (D T A : ℕ) (ρ δ d : ℝ), 1 ≤ D → 2 * D ≤ T → 0 ≤ ρ → ρ < 1 →
    (A : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) →
    0 < δ → 0 < d → d ≤ ((A + D).choose D : ℝ) * δ →
    1 - ((T - 1).choose D : ℝ) * δ / d ≤ D * ρ + 7 * (D : ℝ) ^ 2 / T

def AbsorbExact : Prop :=
  ∀ (T D c h : ℝ), 0 ≤ D → 0 ≤ c → -c ≤ h →
    (T - 3 * D - 3) * (h + c) - (T + 3 * D + 3) * c ≤ T * h - 3 * (D + 1) * |h|

def DepthRadii : Prop :=
  ∀ (p : ℝ) (n : ℕ), 2 ≤ p → 1 ≤ n →
    2 / (p - 1) ≤ p ^ n * (2 / (p * (p - 1))) - ((n : ℝ) - 1) ∧
    2 / (p - 1) ≤ p ^ n * (2 / (p - 1)) - n

def DepthIIExponent : Prop :=
  ∀ p r : ℕ, 2 ≤ p →
    (p ^ 2 - 1) ∣ (p ^ (2 * r) - 1) ∧
    (p : ℝ) ^ (2 * r + 1) / ((p : ℝ) ^ 2 - 1)
        - p * (((p ^ (2 * r) - 1) / (p ^ 2 - 1) : ℕ) : ℝ) = p / ((p : ℝ) ^ 2 - 1)

def LegendreBounds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k c : ℕ) (α : Fin k → ℕ), (∀ j, α j ≤ c) →
    ((p : ℝ) - 1) * (∑ j, (padicValNat p (α j).factorial : ℝ)) ≤ ∑ j, (α j : ℝ) ∧
    (∑ j, (α j : ℝ)) / ((p : ℝ) - 1) - k * ((Nat.log p c : ℝ) + 1)
      ≤ ∑ j, (padicValNat p (α j).factorial : ℝ)

def TTDiffUnit : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (ζ : A) (ℓ : ℕ), ℓ.Prime → IsPrimitiveRoot ζ ℓ →
    ∀ i j : ℕ, i < j → j < ℓ →
      IsUnit ((∑ k ∈ range j, ζ ^ k) - ∑ k ∈ range i, ζ ^ k)

def CardLeExpPow : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] (e : ℕ) (s : Finset G), 1 ≤ e →
    (∀ x : G, e • x = 0) → AddSubgroup.closure (s : Set G) = ⊤ →
    Fintype.card G ≤ e ^ s.card

end Formalism.LogFactorialBounds
end
end

-- bundled from Formalism.LogFactorialBounds.LocalFactorSplit
section
noncomputable section

namespace Formalism.LogFactorialBounds

open Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def CardGLForm : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ),
    (Nat.card (GL (Fin n) F) : ℝ) = (Fintype.card F : ℝ) ^ (n * n) * qE (Fintype.card F) 1 n

def blockUpper {F : Type} [Field F] (a t : ℕ) (J' : Set (GL (Fin a) F)) :
    Set (GL (Fin a ⊕ Fin t) F) :=
  {A | (∀ i j, (A : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) (Sum.inr i) (Sum.inl j) = 0) ∧
       ∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = (A : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F).toBlocks₁₁}

def CardBlockUpper : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Nat.card (blockUpper (F := F) a t (J' : Set (GL (Fin a) F))) =
      Nat.card J' * Nat.card (GL (Fin t) F) * Fintype.card F ^ (a * t)

def ParabolicIndex : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (r s : ℕ),
    (Nat.card (GL (Fin r ⊕ Fin s) F) : ℝ) / (Nat.card (blockUpper (F := F) r s Set.univ) : ℝ) =
      (Fintype.card F : ℝ) ^ (r * s) * qE (Fintype.card F) 1 (r + s) /
        (qE (Fintype.card F) 1 r * qE (Fintype.card F) 1 s)

def LocalFactorSplit : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    let q : ℝ := Fintype.card F
    ((Nat.card (GL (Fin a ⊕ Fin t) F) : ℝ) /
        (Nat.card (blockUpper (F := F) a t (J' : Set (GL (Fin a) F))) : ℝ)) *
      (qE q 1 (a + t))⁻¹ *
      ((Nat.card J' : ℝ) * q ^ (-((a * a : ℕ) : ℤ)) * q ^ (-((a * t : ℕ) : ℤ))) =
    (qE q 1 t)⁻¹

def LocalFactorTame : Prop :=
  ∀ (q : ℝ), 1 < q → ∀ (r t j : ℕ), 1 ≤ j → ∀ L : ℝ,
    (q ^ (r * j * t) * qE q 1 (r + j * t) / (qE q 1 r * qE q 1 (j * t))) *
        (qE q 1 (r + j * t))⁻¹ *
        (q ^ (-((j * t * r : ℕ) : ℤ)) * qE q 1 r * L / (qE q (t + 1) (j * t))⁻¹) =
      (qE q 1 t)⁻¹ * L

def LocalExponents : Prop :=
  ∀ (r j t c : ℕ) (e : Fin c → ℤ),
    let b : ℚ := r + j * t
    (-(b / 2) * ∑ i, (e i : ℚ) - b * ∑ i, (max 0 (-(e i)) : ℚ)) +
        ((r / 2 : ℚ) * ∑ i, (e i : ℚ) - r * ∑ i, (max 0 (e i) : ℚ)) +
        ((r : ℚ) * ∑ i, (max 0 (-(e i)) : ℚ) + r * ∑ i, (max 0 (e i) : ℚ)) =
      -((j * t : ℚ) / 2) * ∑ i, (|e i| : ℚ)

def HookBound : Prop :=
  ∀ (l : ℕ) (hl : 1 ≤ l) (a : Fin l → ℕ), Antitone a →
    |Real.log ((∏ i : Fin l, ((a i + (l - 1 - i.val)).factorial : ℝ)) /
        ∏ p ∈ (univ.filter fun p : Fin l × Fin l => p.1 < p.2),
          ((a p.1 - a p.2 + (p.2.val - p.1.val) : ℕ) : ℝ)) -
      ∑ i : Fin l, Real.log ((a i).factorial : ℝ)| ≤
    2 * (l : ℝ) ^ 2 * Real.log ((a ⟨0, hl⟩ : ℝ) + l)

end Formalism.LogFactorialBounds
end
end

-- bundled from Formalism.LogFactorialBounds.LogFactorialSandwich
section
noncomputable section

namespace Formalism.LogFactorialBounds

open Finset Real

def ph (y : ℝ) : ℝ := y * Real.log y - y

def PhSup : Prop :=
  ∀ ν : ℝ, 0 < ν →
    (∀ s : ℝ, 0 ≤ s → s ^ ν * Real.exp (-(s ^ 2) / 2) ≤ Real.exp (ph ν / 2)) ∧
      (Real.sqrt ν) ^ ν * Real.exp (-((Real.sqrt ν) ^ 2) / 2) = Real.exp (ph ν / 2)

def LogFactorialSandwich : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ph n + Real.log (2 * π * n) / 2 ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤ ph n + Real.log n / 2 + 1

def PhLipschitz : Prop :=
  ∀ x y Y : ℝ, 1 ≤ x → 1 ≤ y → x ≤ Y → y ≤ Y → |ph x - ph y| ≤ |x - y| * Real.log Y

def PhShift : Prop :=
  ∀ a w : ℝ, 1 ≤ a → 0 ≤ w → 0 ≤ ph (a + w) - ph a ∧ ph (a + w) - ph a ≤ w * Real.log (a + w)

def PhLowerBound : Prop :=
  ∀ y : ℝ, 0 ≤ y → -1 ≤ ph y

def FELogDeriv : Prop :=
  ∀ (L : ℂ → ℂ) (d : ℝ), 0 < d →
    DifferentiableAt ℂ L 0 → DifferentiableAt ℂ L 1 → L 0 ≠ 0 → L 1 ≠ 0 →
    (∀ᶠ s in nhds (0 : ℂ),
        ((d / π : ℝ) : ℂ) ^ ((s + 1) / 2) * Complex.Gamma ((s + 1) / 2) * L s =
          ((d / π : ℝ) : ℂ) ^ (((1 - s) + 1) / 2) * Complex.Gamma (((1 - s) + 1) / 2) * L (1 - s)) →
    logDeriv L 0 =
      -logDeriv L 1 - ((Real.log (d / π) : ℝ) : ℂ) + ((Real.eulerMascheroniConstant : ℝ) : ℂ)
        + ((Real.log 2 : ℝ) : ℂ)

def KWCancelOffTop : Prop :=
  ∀ (n nb j m : ℕ) (c₀ : ℝ) (c c' : Fin n → ℝ) (β : Fin nb → ℝ)
    (w L logOm Sc Bt C₀ U E₃ E₄ logK logLam cov : ℝ),
    1 ≤ w → 0 ≤ c₀ → (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ c' i) → (∀ l, 0 ≤ β l) →
    Real.log (w + c₀) ≤ L → (∀ i, Real.log (w + c i) ≤ L) → (∀ i, Real.log (w + c' i) ≤ L) →
    (∀ l, Real.log (β l) ≤ L) →
    |logOm| ≤ L → (∑ i, |c i - c' i|) ≤ Sc → (∑ l, β l) ≤ Bt →
    logK ≤ ph (w + c₀) + (∑ i, ph (w + c i)) + (∑ l, ph (β l))
        - (((n : ℝ) + 1) * w + c₀ + (∑ i, c i) + (∑ l, β l)) * logOm + E₃ →
    (∑ i, ph (w + c' i)) - E₄ ≤ logLam →
    cov ≤ ((((n : ℝ) + 1) + j - 1) - ((m : ℝ) - j)) * w * logOm + C₀ * U * L →
    logK - logLam + cov ≤
      (2 * (j : ℝ) - 1 - m) * w * logOm
        + (w + 2 * c₀ + (∑ i, c i) + Sc + 2 * Bt) * L + C₀ * U * L + E₃ + E₄

def KWCancelTop : Prop :=
  ∀ (n nb j m : ℕ) (a ρ : ℝ) (c : Fin n → ℝ) (c' : Fin (n + 1) → ℝ) (β : Fin nb → ℝ)
    (w L logOm Sc Bt C₀ U E₃ E₄ logK logLam cov : ℝ),
    1 ≤ w → 1 ≤ a → 0 ≤ ρ → (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ c' i) → (∀ l, 0 ≤ β l) →
    Real.log (a + w) ≤ L → Real.log ρ ≤ L → (∀ i, Real.log (w + c i) ≤ L) →
    (∀ i, Real.log (w + c' i) ≤ L) → (∀ l, Real.log (β l) ≤ L) →
    |logOm| ≤ L → (∑ i : Fin n, |c i - c' (Fin.castSucc i)|) ≤ Sc → (∑ l, β l) ≤ Bt →
    logK ≤ ph (a + w) + (∑ i, ph (w + c i)) + ph ρ + (∑ l, ph (β l))
        - (a + w + (∑ i, (w + c i)) + ρ + (∑ l, β l)) * logOm + E₃ →
    (∑ i, ph (w + c' i)) - E₄ ≤ logLam →
    cov ≤ ((((n : ℝ) + 2) + j - 1) - ((m : ℝ) - j)) * w * logOm + C₀ * U * L →
    logK - logLam + cov ≤
      ph a - a * logOm + (2 * (j : ℝ) - m) * w * logOm
        + (w + Sc + (∑ i, c i) + 2 * ρ + 2 * Bt) * L + C₀ * U * L + E₃ + E₄ + 1

end Formalism.LogFactorialBounds
end
end

