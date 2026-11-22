import Formalism.GaussJetBounds.Bundle0001

-- bundled from Formalism.GaussJetBounds.StatementE
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def frameTop {d N0 N1 : ℕ} (TT : Finset (ZMod d)) (y : ZV d N0 N1) : Bool :=
  decide (y.1 ∈ TT ∧ y.2.1.val = 0)

def ThmAJet : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0),
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ x : ZMod d × Fin N0 × Fin N0 → K, (∀ y, ‖x y‖ ≤ 1) →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu2 s ≤ nu1 s) →
      (∀ s, nu1 s ≤ size s) →
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
          (Fintype.card (ZV d N0 N1) : ℝ) * (Real.logb l (κ.degree : ℝ) + 1))

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.StatementO
section
noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def LemmaRWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → Odd l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ZV d N0 N1 → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ (ε : K), (ε = 1 ∨ ε = -1) → ∀ (sig : ι → ℝ), (∀ i, 0 ≤ sig i) → ∀ κ : ι →₀ ℕ,
      (∀ (i j : ι) (α β : ℕ), pureMon l i j α β ≤ κ →
        ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
            (MvPowerSeries.coeff (pureMon l i j α β) (bSum M be)) →
        1 ≤ (l : ℝ) ^ α * sig i + (l : ℝ) ^ β * sig j) →
      MvPowerSeries.constantCoeff (ε • bSum M be) = 0 ∧
      ∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) n
        (MvPowerSeries.coeff n (ε • bSum M be))

def UWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (τ : Type w) [Finite τ] [DecidableEq τ] (p : τ → τ)
    (g : τ → MvPowerSeries τ K), (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (genLog (K := K) l p x) = MvPowerSeries.X x) →
    ∀ U : MvPowerSeries τ K, Integral U →
    ∀ (ι : Type v) [Fintype ι] (M : τ → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ (sig : ι → ℝ), (∀ i, 0 ≤ sig i) →
      WtGe ‖(l : K)‖ (fun i => rho l + sig i) 0
        (MvPowerSeries.subst (fun x => (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i :
          MvPowerSeries ι K)) (MvPowerSeries.subst g U))

def RCoreA : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) [Fintype ι] (sig : ι → ℝ) (κ : ι →₀ ℕ) (a : ℕ), 1 ≤ a →
      (∀ i, κ i ≤ a) → ∀ (B U : MvPowerSeries ι K), MvPowerSeries.constantCoeff B = 0 →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) n
        (MvPowerSeries.coeff n B)) →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + sig i) 0 n (MvPowerSeries.coeff n U)) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (U * mvExp B)‖ ≤
        ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) * (gam l - sig i)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1))

def OrbitsAddA : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι₁ : Type v) (ι₂ : Type w) [Fintype ι₁] [Fintype ι₂] (sig₁ : ι₁ → ℝ)
      (sig₂ : ι₂ → ℝ) (κ : (ι₁ ⊕ ι₂) →₀ ℕ) (a : ℕ), 1 ≤ a → (∀ i, κ i ≤ a) →
    ∀ (B₁ : MvPowerSeries ι₁ K) (B₂ : MvPowerSeries ι₂ K) (U : MvPowerSeries (ι₁ ⊕ ι₂) K),
      MvPowerSeries.constantCoeff B₁ = 0 → MvPowerSeries.constantCoeff B₂ = 0 →
      (∀ n : ι₁ →₀ ℕ, (∀ i, n i ≤ κ (Sum.inl i)) →
        MonoWtGe ‖(l : K)‖ (fun i => rho l + sig₁ i) (1 / ((l : ℝ) - 1)) n
          (MvPowerSeries.coeff n B₁)) →
      (∀ n : ι₂ →₀ ℕ, (∀ i, n i ≤ κ (Sum.inr i)) →
        MonoWtGe ‖(l : K)‖ (fun i => rho l + sig₂ i) (1 / ((l : ℝ) - 1)) n
          (MvPowerSeries.coeff n B₂)) →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + Sum.elim sig₁ sig₂ i) 0 n
        (MvPowerSeries.coeff n U)) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (U * mvExp
          (MvPowerSeries.subst (fun i : ι₁ => (MvPowerSeries.X (Sum.inl i) : MvPowerSeries (ι₁ ⊕ ι₂) K)) B₁ +
            MvPowerSeries.subst (fun i : ι₂ => (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (ι₁ ⊕ ι₂) K)) B₂))‖ ≤
        ‖(l : K)‖ ^ ((∑ i, (κ (Sum.inl i) : ℝ) * (gam l - sig₁ i)) +
          (∑ i, (κ (Sum.inr i) : ℝ) * (gam l - sig₂ i)) -
          ((Fintype.card ι₁ : ℝ) + Fintype.card ι₂) * (Real.logb l (a : ℝ) + 1))

end Formalism.DworkPowerSeriesWeights
end
end

