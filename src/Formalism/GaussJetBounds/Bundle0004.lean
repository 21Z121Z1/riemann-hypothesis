import Formalism.GaussJetBounds.StatementI

-- bundled from Formalism.GaussJetBounds.StatementJ
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def JetPairLin : Prop :=
  ∀ (K : Type u) [Field K] (ι ι' : Type) [Fintype ι] [Fintype ι'] (A : ι → ι' → K)
    (P : MvPolynomial ι K) (F : MvPowerSeries ι' K),
    jetPair P (MvPowerSeries.subst
        (fun j : ι' => (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K)) F) =
      jetPair (MvPolynomial.aeval
        (fun i : ι => (∑ j : ι', MvPolynomial.C (A i j) * MvPolynomial.X j : MvPolynomial ι' K)) P) F

def effMat {K : Type u} [Field K] {d N0 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (i k : Fin N0) : K :=
  if s ∈ TT ∧ i.val = 0 then (if k = i then 1 else 0)
  else if s ∈ TT ∧ k.val = 0 then 0 else T s i k

def ThmAGen : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0),
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ x : ZMod d × Fin N0 × Fin N0 → K, (∀ y, ‖x y‖ ≤ 1) →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1)
      (T : ZMod d → Fin N0 → Fin N0 → K), (∀ s i k, ‖T s i k‖ ≤ 1) →
    ∀ xg : ZMod d × Fin N0 × Fin N0 → K,
      (∀ s i a, xg (s, i, a) = ∑ k : Fin N0, effMat TT T s i k * x (s, k, a)) →
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) →
    ∀ (spec : ZMod d × Fin N0 → Option (ZMod d × ℤ)),
      (∀ (s : ZMod d) (k : Fin N0) (s0 : ZMod d) (j : ℤ), spec (s, k) = some (s0, j) →
        s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ ¬ (s ∈ TT ∧ k.val = 0) ∧
        (0 < j → l ^ j.toNat ≤ nu1 s0) ∧ (j < 0 → l ^ (-j).toNat ≤ size s)) →
      (∀ r r' : ZMod d × Fin N0, spec r ≠ none → spec r = spec r' → r = r') →
      (∀ s0 ∈ TT, ∀ (s : ZMod d) (k : Fin N0) (j : ℤ), ¬ (s ∈ TT ∧ k.val = 0) → Odd j →
        s = s0 + (j : ZMod d) → (0 < j → l ^ j.toNat ≤ nu1 s0) → (j < 0 → l ^ (-j).toNat ≤ size s) →
        spec (s, k) ≠ some (s0, j) →
        (if 0 ≤ j then ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) ^ (l ^ j.toNat) * x (s, k, a)‖
          else ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) * x (s, k, a) ^ (l ^ (-j).toNat)‖) ≤ ‖(l : K)‖) →
      ‖jetPair (∏ s : ZMod d, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K))
            (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) xg)) (MvPowerSeries.subst g U) *
            mvExp (ε • bSum (frameM (N1 := N1) xg) be))‖ ≤
        ‖(l : K)‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.StatementN
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def linForm {K : Type u} [Field K] {ι : Type} [Fintype ι] (L : ι → K) : MvPolynomial ι K :=
  ∑ x, MvPolynomial.C (L x) * MvPolynomial.X x

def quadSer {K : Type u} [Field K] {ι : Type} [Fintype ι] (c : ι → ι → K) : MvPowerSeries ι K :=
  ∑ x, ∑ y, MvPowerSeries.C (c x y) * MvPowerSeries.X x * MvPowerSeries.X y

def polar {K : Type u} [Field K] {ι : Type} [Fintype ι] (c : ι → ι → K) (L L' : ι → K) : K :=
  ∑ x, ∑ y, c x y * (L x * L' y + L y * L' x)

def Matchings : Prop :=
  ∀ (K : Type u) [NormedField K] [CharZero K] (ι : Type) [Fintype ι] (c : ι → ι → K) (S : K)
    (sg : MvPowerSeries ι K) (n : ℕ) (L : Fin n → ι → K),
    jetPair (∏ i, linForm (L i)) (mvExp ((-S) • quadSer c) * sg) =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ * σ = 1),
        (∏ i ∈ Finset.univ.filter (fun i => i < σ i), (-S * polar c (L i) (L (σ i)))) *
          jetPair (∏ i ∈ Finset.univ.filter (fun i => σ i = i), linForm (L i)) sg

def JetsIntegral {K : Type u} [NormedField K] {ι : Type} (sg : MvPowerSeries ι K) : Prop :=
  ∀ κ : ι →₀ ℕ, ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ sg‖ ≤ 1

def PairJet : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (pi : ℝ), 0 < pi → pi < 1 →
    ∀ (ι : Type) [Fintype ι] (S : K) (u : ι → K), ‖S‖ ≤ pi ^ (-(1 / 2 : ℝ)) → (∀ i, ‖u i‖ ≤ 1) →
    ∀ sg : MvPowerSeries (Bool × ι) K, JetsIntegral sg → ∀ κ : (Bool × ι) →₀ ℕ,
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
          (mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
            MvPowerSeries.X (true, i)) * sg)‖ ≤
        pi ^ (-(1 / 2 : ℝ) * ∑ i, (min (κ (false, i)) (κ (true, i)) : ℝ))

def OneRowBasis : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (N0 : ℕ) (h0 : 0 < N0) (x1 : Fin N0 → K),
    (∀ a, ‖x1 a‖ ≤ 1) → (∃ a, ‖x1 a‖ = 1) →
    ∃ f : Matrix (Fin N0) (Fin N0) K, (∀ a a', ‖f a a'‖ ≤ 1) ∧ ‖f.det‖ = 1 ∧
      ∀ a, (∑ a', x1 a' * f a a') = if a = ⟨0, h0⟩ then 1 else 0

def OneRow : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (N0 N1 C : ℕ)
    (f : Matrix (Fin N0) (Fin N0) K), (∀ a a', ‖f a a'‖ ≤ 1) → ‖f.det‖ = 1 →
    ∀ (x : Fin N0 → Fin N0 → K), (∀ i a, ‖x i a‖ ≤ 1) → ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
      (I : ∀ c, Fin (p c) → Fin N1),
    ∃ Q : MvPolynomial (Fin N0 × Fin N1) K, (∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1) ∧
      minorProd (fun (i : Fin N0) (b : Fin N1) =>
          (∑ a, MvPolynomial.C (x i a) * MvPolynomial.X (a, b) : MvPolynomial (Fin N0 × Fin N1) K))
          p hp I =
        MvPolynomial.aeval (fun y : Fin N0 × Fin N1 =>
          (∑ a', MvPolynomial.C (f y.1 a') * MvPolynomial.X (a', y.2) :
            MvPolynomial (Fin N0 × Fin N1) K)) Q ∧
      ∀ mono ∈ Q.support, ∀ a : Fin N0, (∑ b : Fin N1, mono (a, b)) ≤ C

def ThmB : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (pi : ℝ), 0 < pi → pi < 1 →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (S : K) (u : H → K),
      ‖S‖ ≤ pi ^ (-(1 / 2 : ℝ)) → (∀ t, ‖u t‖ ≤ 1) →
    ∀ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K, JetsIntegral sg →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) K), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
      (hp : ∀ τ c, p τ c ≤ N0), (∀ τ c, 1 ≤ p τ c) → ∀ (I : ∀ τ c, Fin (p τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ p τ c)).card) → (∀ τ, size τ = ∑ c, p τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ))
          (mvExp ((-S) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
              MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)) * sg)‖ ≤
        pi ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))

def SizesB : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (TT : Finset H) (c wt wt' : H → ℝ) (f k b b' : ℝ),
    (Fintype.card H : ℝ) = f / 2 → 1 ≤ k → 0 ≤ b → 0 ≤ b' →
    (∀ t, t ∉ TT → c t ≤ 4 * k * b') → (∀ t, t ∈ TT → c t ≤ 4 * k * b' + 2 * b) →
    (∀ t, 0 ≤ wt t ∧ wt t ≤ 2 * b') → (∀ t, 0 ≤ wt' t) →
    (∑ t, c t) ≤ 2 * (TT.card : ℝ) * b + 2 * f * k * b' ∧
      |-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)| ≤ f * k * b'

end Formalism.DworkPowerSeriesWeights
end
end

