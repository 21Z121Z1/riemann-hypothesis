import Formalism.GaussJetBounds.Bundle0002

-- bundled from Formalism.GaussJetBounds.StatementG
section
noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def LemmaRA : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → Odd l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K),
      (∀ x i, ‖M x i‖ ≤ 1) → (∀ x i, M x i ≠ 0 → lt i = x.1) →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (entLog (K := K) l x) = MvPowerSeries.X x) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U →
    ∀ (ε : K), (ε = 1 ∨ ε = -1) → ∀ (sig : ι → ℝ), (∀ i, 0 ≤ sig i) → ∀ (κ : ι →₀ ℕ) (a : ℕ),
      1 ≤ a → (∀ i, κ i ≤ a) →
      (∀ (i j : ι) (α β : ℕ), pureMon l i j α β ≤ κ →
        ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
            (MvPowerSeries.coeff (pureMon l i j α β) (bSum M be)) →
        1 ≤ (l : ℝ) ^ α * sig i + (l : ℝ) ^ β * sig j) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
          (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U) * mvExp (ε • bSum M be))‖ ≤
        ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) * (gam l - sig i)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1))

def ThmAJetA : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0),
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ x : ZMod d × Fin N0 × Fin N0 → K, (∀ y, ‖x y‖ ≤ 1) →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu2 s ≤ nu1 s) →
      (∀ s, nu1 s ≤ size s) → ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) →
    ∀ (spec : ZMod d × Fin N0 → Option (ZMod d × ℤ)) (κ : ZV d N0 N1 →₀ ℕ),
      (∀ s ∈ TT, (∑ b : Fin N1, κ (s, ⟨0, h0⟩, b)) = nu1 s) →
      (∀ s, (∑ y ∈ Finset.univ.filter (fun y : ZV d N0 N1 => y.1 = s ∧ frameTop TT y = false), κ y) =
        Dl d TT nu1 size s) →
      (∀ (s : ZMod d) (k : Fin N0) (s0 : ZMod d) (j : ℤ), spec (s, k) = some (s0, j) →
        s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ ¬ (s ∈ TT ∧ k.val = 0) ∧
        (0 < j → l ^ j.toNat ≤ nu1 s0) ∧ (j < 0 → l ^ (-j).toNat ≤ size s)) →
      (∀ (s0 : ZMod d) (j : ℤ),
        (∑ y ∈ Finset.univ.filter (fun y : ZV d N0 N1 => spec (y.1, y.2.1) = some (s0, j)), κ y) ≤
          capL d TT nu1 nu2 (s0 + (j : ZMod d))) →
      (∀ s0 ∈ TT, ∀ (s : ZMod d) (k : Fin N0) (j : ℤ), ¬ (s ∈ TT ∧ k.val = 0) → Odd j →
        s = s0 + (j : ZMod d) → (0 < j → l ^ j.toNat ≤ nu1 s0) → (j < 0 → l ^ (-j).toNat ≤ size s) →
        spec (s, k) ≠ some (s0, j) →
        (if 0 ≤ j then ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) ^ (l ^ j.toNat) * x (s, k, a)‖
          else ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) * x (s, k, a) ^ (l ^ (-j).toNat)‖) ≤ ‖(l : K)‖) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) x)) (MvPowerSeries.subst g U) *
            mvExp (ε • bSum (frameM (N1 := N1) x) be))‖ ≤
        ‖(l : K)‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.StatementR
section
noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def OrbitsAddFam : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (O : Type w) [Fintype O] (ι : O → Type v) [∀ o, Fintype (ι o)]
      (sig : ∀ o, ι o → ℝ) (κ : (Σ o, ι o) →₀ ℕ) (a : ℕ), 1 ≤ a → (∀ i, κ i ≤ a) →
    ∀ (B : ∀ o, MvPowerSeries (ι o) K) (U : MvPowerSeries (Σ o, ι o) K),
      (∀ o, MvPowerSeries.constantCoeff (B o) = 0) →
      (∀ o, ∀ n : ι o →₀ ℕ, (∀ i, n i ≤ κ ⟨o, i⟩) →
        MonoWtGe ‖(l : K)‖ (fun i => rho l + sig o i) (1 / ((l : ℝ) - 1)) n
          (MvPowerSeries.coeff n (B o))) →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun x : (Σ o, ι o) => rho l + sig x.1 x.2) 0 n
        (MvPowerSeries.coeff n U)) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (U * mvExp
          (∑ o, MvPowerSeries.subst
            (fun i : ι o => (MvPowerSeries.X ⟨o, i⟩ : MvPowerSeries (Σ o, ι o) K)) (B o)))‖ ≤
        ‖(l : K)‖ ^ ((∑ o, ∑ i, (κ ⟨o, i⟩ : ℝ) * (gam l - sig o i)) -
          (∑ o, (Fintype.card (ι o) : ℝ)) * (Real.logb l (a : ℝ) + 1))

def OneLetterWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l N0 N1 : ℕ),
    l.Prime → Odd l → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ be : MvPowerSeries (ZMod 2) K, BHyp l 2 K0 ζ be →
    ∀ (ep : K), ‖ep‖ = 1 →
    ∀ (ι : Type v) [Fintype ι] (M : Fin N0 × Fin N1 → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ (sgn : K), (sgn = 1 ∨ sgn = -1) →
      MvPowerSeries.constantCoeff ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
              (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
                ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be : MvPowerSeries ι K) = 0 ∧
      WtGe ‖(l : K)‖ (fun _ : ι => rho l + 1 / ((l : ℝ) + 1)) (1 / ((l : ℝ) - 1))
        ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
              (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
                ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be)

end Formalism.DworkPowerSeriesWeights
end
end

