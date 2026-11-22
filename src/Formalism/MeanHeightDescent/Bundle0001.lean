import Mathlib
import Formalism.MeanHeightDescent.BadRowsNumeric
import Formalism.LogFactorialBounds.Bundle0001

-- bundled from Formalism.MeanHeightDescent.CombinedAverageDegreeBound
section
open Finset

noncomputable section

namespace Formalism.ExtensionFiltration

def HSRearranged : Prop :=
  ∀ T D h J C0 lρ l0 lβ g lΛD lΛT zc z dc Bd degc : ℝ,
    0 ≤ T → 0 ≤ D → 0 ≤ C0 → 0 ≤ zc → zc ≤ z → z ≤ 1 / 2 → 0 < dc → dc * (1 - zc) = Bd →
    lρ ≤ l0 + C0 * Real.log (2 + |h|) →
    0 ≤ T * (Real.log 2 + l0 + lβ / 2) + lΛD + lΛT →
    (1 - zc) * (T * h - 3 * (D + 1) * |h| - J - C0 * D ^ 2 * (lρ + Real.log T) - (T + D + 1) * lβ
        - (T + D ^ 2) * (g + 2))
      - zc * (T * (Real.log 2 + lρ + lβ / 2) + lΛD + lΛT) ≤ degc / dc →
    Bd * (T * h - 3 * (D + 1) * |h| - (C0 * (C0 * D ^ 2 + 2 * z * T)) * Real.log (2 + |h|)
        - (J + C0 * D ^ 2 * (l0 + Real.log T) + (T + D + 1) * lβ + (T + D ^ 2) * (g + 2))
        - 2 * z * (T * (Real.log 2 + l0 + lβ / 2) + lΛD + lΛT)) ≤ degc

def CombinedAverageDegreeBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (T D A cs X cc z ρ R1 R2 Bn δ' : ℝ)
    (h sl δ dc degc : ι → ℝ) (LL0 U b Ca Cb PPf e1 e2 muU : ℝ),
    0 ≤ D → 3 * D + 5 ≤ T → 0 < A → 0 ≤ cs → 0 ≤ X → 0 ≤ cc → 0 ≤ z → z < 1 → 0 ≤ ρ → ρ < 1 →
    0 ≤ R1 → 0 ≤ R2 → 0 < Bn → 0 < δ' →
    (∀ c, δ' ≤ δ c ∧ δ c ≤ δ' / (1 - ρ)) →
    (∀ c, Bn * δ c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δ c) →

    (∀ c, 0 ≤ h c + cs) →
    (∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc) →
    -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) →

    (∀ c, Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R1 - 2 * z * R2)
      ≤ degc c) →

    T * X ≤ Ca * LL0 * U + e1 → T * cc ≤ Cb * LL0 * U + e2 →
    cs * (6 * D + 10 + T * (z + 2 * ρ)) + (A * Real.log (max A 1) + 4) + R1 + 2 * z * R2 + PPf
      + e1 + e2 ≤ b / 4 →

    2 * ((∑ c, degc c) / (∑ c, dc c) - PPf) ≤ muU →
    -(2 * ((Ca + Cb) * LL0 * U + b / 4)) ≤ muU

end Formalism.ExtensionFiltration
end
end

-- bundled from Formalism.MeanHeightDescent.FlatDefect
section
noncomputable section

namespace Formalism.ExtensionFiltration

def RankShare : Prop :=
  ∀ (D T a : ℕ) (ρ δ dA dB dtop : ℝ), 1 ≤ D → 2 * D ≤ T → 0 ≤ ρ → ρ < 1 →
    (a : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) → 0 < δ →
    ((T - 1).choose D : ℝ) * δ ≤ dA → 0 < dB → dB ≤ dtop → dtop ≤ ((a + D).choose D : ℝ) * δ →
    (D : ℝ) * ρ + 7 * (D : ℝ) ^ 2 / T ≤ 1 →
    (1 - ((D : ℝ) * ρ + 7 * (D : ℝ) ^ 2 / T)) * dB ≤ dA

def BadCount : Prop :=
  ∀ db db1 db2 sh1 sh2 d d' H ε δ : ℝ,
    0 < H → 0 ≤ d' → d' ≤ H * d → 0 ≤ ε → ε ≤ 1 / 2 → 0 ≤ sh1 → 0 ≤ sh2 → sh1 + sh2 ≤ δ →
    db1 ≤ (1 + ε) * sh1 * d' / H → db2 ≤ (1 + ε) * sh2 * d' / H → db ≤ db1 + db2 →
    db ≤ 3 * δ * d

def FlatDefect : Prop :=
  ∀ w q' t2 tq td lrd : ℝ, 0 ≤ w → 0 ≤ q' → 0 ≤ t2 → 0 ≤ tq → 0 ≤ td → lrd = t2 + tq + td →
    |w * q' * (t2 + tq - td)| ≤ w * q' * lrd

end Formalism.ExtensionFiltration
end
end

