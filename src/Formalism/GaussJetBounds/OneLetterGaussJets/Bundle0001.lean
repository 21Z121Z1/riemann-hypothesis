import Formalism.GaussJetBounds.OneLetterGaussJets.OddLevelGainSum
import Formalism.GaussJetBounds.Bundle0001

-- bundled from Formalism.GaussJetBounds.OneLetterGaussJets.StatementA
section
noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

def ThmAAssembly7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
  ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu2 s ≤ nu1 s) →
    (∀ s, nu1 s ≤ size s) →
  ∀ sig : ZMod d → ℝ, IsOptDual l d (fun s => (Dl d TT nu1 size s : ℝ)) sig →
  ∀ (ι : Type) [Fintype ι] (lt : ι → ZMod d) (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ))
    (κ : ι → ℕ),
    (∀ i, isTop i = true → lt i ∈ TT ∧ spec i = none) →
    (∀ s ∈ TT, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = true), (κ i : ℝ)) =
      (nu1 s : ℝ)) →
    (∀ s, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = false), (κ i : ℝ)) =
      (Dl d TT nu1 size s : ℝ)) →
    (∀ i s j, spec i = some (s, j) → s ∈ TT ∧ Odd j ∧ lt i = s + (j : ZMod d) ∧
      (0 < j → l ^ j.toNat ≤ nu1 s) ∧ (j < 0 → l ^ (-j).toNat ≤ Dl d TT nu1 size (lt i))) →
    (∀ (s : ZMod d) (j : ℤ), (∑ i ∈ Finset.univ.filter (fun i => spec i = some (s, j)), (κ i : ℝ)) ≤
      (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ)) →
    ∃ eps : ZMod d → ℝ, (∀ s, 0 ≤ eps s) ∧
      (∀ s ∈ TT, ∀ e : ℕ, dTop d TT s = (e : ℕ∞) → ((l : ℝ) ^ e)⁻¹ ≤ eps s) ∧
      (∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) ≤
        ∑ i, (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i)

def LabelCountBound : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 size : ZMod d → ℕ) (a : ℝ), 2 ≤ a →
    (∀ s ∈ TT, (nu1 s : ℝ) ≤ 2 * a) → ∀ s, (Dl d TT nu1 size s : ℝ) ≤ a ^ 2 →
      (JnumOneLetter l d TT nu1 size s : ℝ) ≤ 2 * Real.logb l a + 1

def LabFinite7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 size : ZMod d → ℕ) (s : ZMod d),
    {q : ZMod d × ℤ | IsLabOneLetter l d TT nu1 size s q.1 q.2}.Finite

def WcapLe7 : Prop :=
  ∀ (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ) (s : ZMod d),
    WcapOneLetter l d TT nu1 nu2 size s ≤ Wcap l d TT nu1 nu2 size s

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
end
end

-- bundled from Formalism.GaussJetBounds.OneLetterGaussJets.StatementN
section
noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

def PropSix7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (TT : Finset (ZMod d)) (k : ℕ) (D w E : ZMod d → ℝ), 3 ≤ k →
      (∀ s, 0 < w s) → (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ TT → D s = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ TT → D s = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      Fnum l d (fun s => ((k : ℝ) - 1) * w s) - 2 * gam l * (∑ s ∈ TT, w s) -
          8 / (l : ℝ) * (∑ s : ZMod d, w s) ≤ Fnum l d D ∧
        Fnum l d (fun s => ((k : ℝ) - 1) * w s) - 11 / (l : ℝ) * (∑ s : ZMod d, w s) ≤
          Fnum l d (fun s => ((k : ℝ) - 1) * w s) - 2 * gam l * (∑ s ∈ TT, w s) -
            8 / (l : ℝ) * (∑ s : ZMod d, w s)

def GainDominatesInnerSum : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 nu2 : ZMod d → ℕ) (s : ZMod d),
    oddLevelGainSum l d TT nu1 nu2 s ≤ topTerm l d TT nu1 nu2 s

def NormCor7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ) (k : ℕ) (L : ℝ)
      (w E : ZMod d → ℝ) (pi y : ℝ), 0 < pi → pi < 1 → 3 ≤ k →
      (∀ s, 0 < w s) → (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      y ≤ pi ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) - L) →
      y ≤ pi ^ ((∑ s ∈ TT, oddLevelGainSum l d TT nu1 nu2 s) + Fnum l d (fun s => ((k : ℝ) - 1) * w s) -
          11 / (l : ℝ) * (∑ s : ZMod d, w s) -
          gam l * (∑ s ∈ TT, (WcapOneLetter l d TT nu1 nu2 size s : ℝ)) - L)

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
end
end

