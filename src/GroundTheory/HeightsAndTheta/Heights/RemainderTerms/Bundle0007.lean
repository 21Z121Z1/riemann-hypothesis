import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
import GroundTheory.HeightsAndTheta.Heights.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PShiftSumRule
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

namespace ShiftSumRule

def flagIntegralLinear (f N : ℕ) : RootRing f N →ₗ[ℚ] ℚ where
  toFun := flagIntegral f N
  map_add' Φ Ψ := by simp only [flagIntegral, coeff_add, add_mul, Finset.sum_add_distrib]
  map_smul' b Φ := by
    simp only [flagIntegral, coeff_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem pderiv_blockPowerSum (N k : ℕ) (i : Fin N) :
    pderiv ((0 : Fin 1), i) (blockPowerSum 1 N k 0) =
      (k : RootRing 1 N) * X ((0 : Fin 1), i) ^ (k - 1) := by
  classical
  rw [blockPowerSum, map_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [pderiv_pow, pderiv_X_of_ne (show ((0 : Fin 1), j) ≠ ((0 : Fin 1), i) by simp [hj]), mul_zero]
  · simp

theorem sum_first_pow (r a m : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        (X ((0 : Fin 1), i) : RootRing 1 (r + a)) ^ m =
      blockPowerSum 1 (r + a) m 0 - smallPowerSum 1 r a .last m 0 := by
  classical
  rw [eq_sub_iff_add_eq, blockPowerSum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin (r + a) => (i : ℕ) < a)]
  congr 1
  simp only [smallPowerSum, yRoot, SmallBlock.sign, map_one, one_mul, yIndex]
  refine Finset.sum_bij (fun j _ => (⟨a + (j : ℕ), by have := j.isLt; omega⟩ : Fin (r + a)))
    ?_ ?_ ?_ ?_
  · intro j _; simp
  · intro j₁ _ j₂ _ h
    simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at h
    exact Fin.ext h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact ⟨⟨(i : ℕ) - a, by have := i.isLt; omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
  · intro j _; rfl

end ShiftSumRule

open ShiftSumRule in

theorem ShiftSumRule.proof (hS : ShiftTotalValues.Statement)
    (h1 : FlagIntegralKillsPowerSums.Statement) : ShiftSumRule.Statement := by
  classical
  intro r a hr ha Q hQ
  have h0 : flagIntegralLinear 1 (r + a)
      (∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        pderiv ((0 : Fin 1), i) (restPolynomial 1 r a .last)) = 0 :=
    (hS 1 r a 0).1.1
  have hnat : ∀ (n : ℕ) (G : RootRing 1 (r + a)),
      flagIntegralLinear 1 (r + a) ((n : RootRing 1 (r + a)) * G) =
        n * flagIntegralLinear 1 (r + a) G := by
    intro n G
    rw [show (n : RootRing 1 (r + a)) = C (n : ℚ) from (map_natCast C n).symm, C_mul', map_smul,
      smul_eq_mul]
  have hexp : ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        pderiv ((0 : Fin 1), i) (restPolynomial 1 r a .last) =
      ∑ k ∈ Icc 1 (r + a),
        (blockPowerSum 1 (r + a) k 0 *
            ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
              pderiv ((0 : Fin 1), i) (Q k 0) +
          (k : RootRing 1 (r + a)) *
            (blockPowerSum 1 (r + a) (k - 1) 0 - smallPowerSum 1 r a .last (k - 1) 0) *
              Q k 0) := by
    rw [hQ]
    simp only [Fin.sum_univ_one]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← sum_first_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pderiv_mul, pderiv_blockPowerSum]; ring
  rw [hexp, map_sum] at h0
  have hval : ∀ k ∈ Icc 1 (r + a),
      flagIntegralLinear 1 (r + a)
        (blockPowerSum 1 (r + a) k 0 *
            ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
              pderiv ((0 : Fin 1), i) (Q k 0) +
          (k : RootRing 1 (r + a)) *
            (blockPowerSum 1 (r + a) (k - 1) 0 - smallPowerSum 1 r a .last (k - 1) 0) *
              Q k 0) =
        (k : ℚ) * (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) -
          flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (k - 1) 0 * Q k 0)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [map_add, show flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) k 0 * _) = 0 from
      h1 1 (r + a) k 0 _ hk.1 hk.2, zero_add, mul_assoc, hnat, sub_mul, map_sub]
  rw [Finset.sum_congr rfl hval] at h0
  have hI : Icc 1 (r + a) = insert 1 (Icc 2 (r + a)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.sum_insert (by simp)] at h0
  have hk1 : ((1 : ℕ) : ℚ) *
      (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (1 - 1) 0 * Q 1 0) -
        flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (1 - 1) 0 * Q 1 0)) =
      (a : ℚ) * flagIntegral 1 (r + a) (Q 1 0) := by
    have e1 : blockPowerSum 1 (r + a) 0 0 = ((r + a : ℕ) : RootRing 1 (r + a)) := by
      simp [blockPowerSum]
    have e2 : smallPowerSum 1 r a .last 0 0 = ((r : ℕ) : RootRing 1 (r + a)) := by
      simp [smallPowerSum]
    rw [Nat.sub_self, e1, e2, hnat, hnat]
    change ((1 : ℕ) : ℚ) * (((r + a : ℕ) : ℚ) * flagIntegral 1 (r + a) (Q 1 0) -
      (r : ℚ) * flagIntegral 1 (r + a) (Q 1 0)) = _
    push_cast; ring
  have hk2 : ∀ k ∈ Icc 2 (r + a),
      (k : ℚ) * (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) -
          flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (k - 1) 0 * Q k 0)) =
        -restTerm 1 (r + a) Q k 0 (smallPowerSum 1 r a .last (k - 1) 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [show flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) = 0 from
      h1 1 (r + a) (k - 1) 0 _ (by omega) (by omega), zero_sub, restTerm, mul_neg]
    rfl
  rw [hk1, Finset.sum_congr rfl hk2, Finset.sum_neg_distrib] at h0
  linarith

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

def IsBlockAlternating (f N : ℕ) (P : RootRing f N) : Prop :=
  ∀ w : Fin f → Equiv.Perm (Fin N), blockPermute f N w P = blockSign f N w • P

def IsBlockSymmetric (f N : ℕ) (P : RootRing f N) : Prop :=
  ∀ w : Fin f → Equiv.Perm (Fin N), blockPermute f N w P = P

theorem isBlockAlternating_blockVandermonde (f N : ℕ) :
    IsBlockAlternating f N (blockVandermonde f N) :=
  fun w => Flag.blockPermute_blockVandermonde f N w

theorem isBlockAlternating_antisymmetrize (f N : ℕ) (H : RootRing f N) :
    IsBlockAlternating f N (antisymmetrize f N H) :=
  fun w => Flag.blockPermute_antisymmetrize f N w H

def FlagCoeffBlockPermute.Statement : Prop :=
  ∀ (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (P : RootRing f N) (α : Fin f × Fin N →₀ ℕ),
    coeff α (blockPermute f N w P) =
      coeff (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) P

def FlagAltCoeffInjective.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N) (α : Fin f × Fin N →₀ ℕ),
    IsBlockAlternating f N P → coeff α P ≠ 0 → ∀ τ : Fin f, Function.Injective fun i : Fin N => α (τ, i)

def FlagInjSumBound.Statement : Prop :=
  ∀ (N : ℕ) (g : Fin N → ℕ), Function.Injective g →
    N * (N - 1) / 2 ≤ ∑ i, g i ∧ (∑ i, g i = N * (N - 1) / 2 → ∀ i, g i < N)

def FlagStaircaseOrbit.Statement : Prop :=
  ∀ (f N : ℕ) (α β : Fin f × Fin N →₀ ℕ), (∀ τ i, α (τ, i) < N) → (∀ τ i, β (τ, i) < N) →
    (∀ τ, Function.Injective fun i : Fin N => α (τ, i)) →
    (∀ τ, Function.Injective fun i : Fin N => β (τ, i)) →
    ∃ w : Fin f → Equiv.Perm (Fin N), ∀ τ i, α (τ, w τ i) = β (τ, i)

def FlagVandermondeHomogeneous.Statement : Prop :=
  ∀ f N : ℕ, (blockVandermonde f N).IsHomogeneous (topDegree f N)

def FlagAltTopDegree.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N), IsBlockAlternating f N P → P.IsHomogeneous (topDegree f N) →
    ∃ e : ℚ, P = C e * blockVandermonde f N

def FlagIntegralPermute.Statement : Prop :=
  ∀ (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N),
    flagIntegral f N (blockPermute f N w H) = blockSign f N w * flagIntegral f N H

def FlagIntegralAntisymmetrize.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N),
    flagIntegral f N (antisymmetrize f N H) = (N.factorial : ℚ) ^ f * flagIntegral f N H

def FlagIntegralVandermondePos.Statement : Prop :=
  ∀ f N : ℕ, 0 < flagIntegral f N (blockVandermonde f N)

def FlagAntisymHomogeneous.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N) (d : ℕ), H.IsHomogeneous d → (antisymmetrize f N H).IsHomogeneous d

def FlagHomogeneousComponentMul.Statement : Prop :=
  ∀ (σ : Type) (P G : MvPolynomial σ ℚ) (k n : ℕ), P.IsHomogeneous k →
    homogeneousComponent n (P * G) = if k ≤ n then P * homogeneousComponent (n - k) G else 0

def FlagIntegralTopComponent.Statement : Prop :=
  ∀ (f N : ℕ) (Φ : RootRing f N),
    flagIntegral f N Φ = flagIntegral f N (homogeneousComponent (topDegree f N) Φ)

def FlagIntegralVandermondeMul.Statement : Prop :=
  ∀ (f N : ℕ) (R : RootRing f N),
    flagIntegral f N (blockVandermonde f N * R) = constantCoeff R * flagIntegral f N (blockVandermonde f N)

def FlagIntegralViaQuotient.Statement : Prop :=
  ∀ (f N : ℕ) (H R : RootRing f N), antisymmetrize f N H = blockVandermonde f N * R →
    flagIntegral f N H =
      flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f * constantCoeff R

def FlagIntegralTopDegree.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N), H.IsHomogeneous (topDegree f N) →
    algebraMap ℚ (FractionRing (RootRing f N)) (flagIntegral f N H) =
      algebraMap ℚ (FractionRing (RootRing f N))
          (flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f) *
        dividedDifference f N H

def FlagSymmetricMulAntisym.Statement : Prop :=
  ∀ (f N : ℕ) (P H : RootRing f N), IsBlockSymmetric f N P →
    antisymmetrize f N (P * H) = P * antisymmetrize f N H

def FlagPowerSumSymmetric.Statement : Prop :=
  ∀ (f N k : ℕ) (τ : Fin f), IsBlockSymmetric f N (blockPowerSum f N k τ)

def FlagSwapDivisible.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (P : MvPolynomial σ ℚ) (a b : σ), a ≠ b →
    rename (Equiv.swap a b) P = -P → (X a - X b : MvPolynomial σ ℚ) ∣ P

def FlagDiffPrime.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (a b : σ), a ≠ b → Prime (X a - X b : MvPolynomial σ ℚ)

def FlagDiffNotDvd.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (a b c d : σ), a ≠ b → c ≠ d → ¬ (a = c ∧ b = d) →
    ¬ (a = d ∧ b = c) → ¬ (X a - X b : MvPolynomial σ ℚ) ∣ (X c - X d)

def FlagProdPrimesDvd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ι : Type) (s : Finset ι) (p : ι → R) (x : R),
    (∀ i ∈ s, Prime (p i)) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ p i ∣ p j) → (∀ i ∈ s, p i ∣ x) →
      (∏ i ∈ s, p i) ∣ x

def FlagVandermondeDvd.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N), IsBlockAlternating f N P → blockVandermonde f N ∣ P

def FlagDividedDifferencePoly.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N), ∃ R : RootRing f N,
    antisymmetrize f N H = blockVandermonde f N * R ∧ IsBlockSymmetric f N R

def FlagQuotientHomogeneous.Statement : Prop :=
  ∀ (σ : Type) (A R : MvPolynomial σ ℚ) (m k : ℕ), A ≠ 0 → A.IsHomogeneous m →
    (A * R).IsHomogeneous (m + k) → R.IsHomogeneous k

def FlagRestrictSymmetric.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N), IsBlockSymmetric f N R →
    (restrictToBlock f N τ R).IsSymmetric

def FlagRestrictPowerSum.Statement : Prop :=
  ∀ (f N k : ℕ) (τ σ : Fin f), 1 ≤ k →
    restrictToBlock f N τ (blockPowerSum f N k σ) = if σ = τ then psum (Fin N) ℚ k else 0

def FlagRestrictConstantCoeff.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N),
    constantCoeff (restrictToBlock f N τ R) = constantCoeff R

def FlagRestrictHomogeneous.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N) (k : ℕ), R.IsHomogeneous k →
    (restrictToBlock f N τ R).IsHomogeneous k

def FlagRestrictDecomposition.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : ℕ → Fin f → RootRing f N),
    restrictToBlock f N τ (∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ) =
      ∑ l ∈ Finset.Icc 1 N, psum (Fin N) ℚ l * restrictToBlock f N τ (R l τ)

def FlagPowerSumPreimage.Statement : Prop :=
  ∀ (N : ℕ) (T : ℕ → MvPolynomial (Fin N) ℚ), (∀ l, (T l).IsSymmetric) →
    ∃ S : MvPolynomial (Fin N) ℚ,
      powerSumHom N S = ∑ l ∈ Finset.Icc 1 N, psum (Fin N) ℚ l * T l ∧
      ∀ (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N),
        coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) S = constantCoeff (T k)

def FlagAntisymDecomposition.Statement : Prop :=
  ∀ (f N : ℕ) (F G : RootRing f N) (Q R : ℕ → Fin f → RootRing f N),
    IsPowerSumDecomposition f N F Q →
    (∀ l σ, antisymmetrize f N (G * Q l σ) = blockVandermonde f N * R l σ) →
    antisymmetrize f N (G * F) =
      blockVandermonde f N * ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def SchStrictAntiSplit.Statement : Prop :=
  ∀ (r n : ℕ) (d : Fin r → ℕ), StrictAnti d → ∑ i, d i = r * (r - 1) / 2 + n →
    (∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i) ∧
      (fun i : Fin r => d i - (r - 1 - (i : ℕ))) ∈ partitionsOf r n

def SchAltPartitionExpansion.Statement : Prop :=
  ∀ (r n : ℕ) (P : MvPolynomial (Fin r) ℚ), Comb.IsAlt P →
    P.IsHomogeneous (r * (r - 1) / 2 + n) →
    P = ∑ lam ∈ partitionsOf r n,
      C (coeff (Finsupp.equivFunOnFinite.symm fun i : Fin r => lam i + (r - 1 - (i : ℕ))) P) *
        (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam)

def rootOfUnity (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / k)

def rootOfUnityPoint (N k : ℕ) : Fin N → ℂ :=
  fun i => if (i : ℕ) < k then rootOfUnity k ^ (i : ℕ) else 0

def rootOfUnityJTMatrix (k : ℕ) {r : ℕ} (nu : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j =>
    if 0 ≤ (nu i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) ∧
        (k : ℤ) ∣ (nu i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) then 1 else 0

def SchProdOneSubRootsOfUnity.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∏ i ∈ range k, (1 - Polynomial.C (rootOfUnity k ^ i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ)

def SchCompleteGenerating.Statement : Prop :=
  ∀ (N : ℕ) (y : Fin N → ℂ) (d : ℕ),
    ∑ c ∈ range (d + 1), (∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X)).coeff c *
      aeval y (hsymm (Fin N) ℚ (d - c)) = if d = 0 then 1 else 0

def SchCompleteAtRootsOfUnity.Statement : Prop :=
  ∀ N k d : ℕ, 1 ≤ k → k ≤ N →
    aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ d) = if k ∣ d then 1 else 0

def SchPowerSumAtRootsOfUnity.Statement : Prop :=
  ∀ N k j : ℕ, 1 ≤ k → k ≤ N → 1 ≤ j →
    aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ j) = if k ∣ j then (k : ℂ) else 0

def SchPowerSumHomWeighted.Statement : Prop :=
  ∀ (N d : ℕ) (S : MvPolynomial (Fin N) ℚ),
    S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) d → (powerSumHom N S).IsHomogeneous d

def SchWeightedPreimage.Statement : Prop :=
  ∀ (N k : ℕ) (P : MvPolynomial (Fin N) ℚ), P.IsSymmetric → P.IsHomogeneous k →
    ∃ S, powerSumHom N S = P ∧ S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) k

def SchEvalPowerSumHom.Statement : Prop :=
  ∀ (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (S : MvPolynomial (Fin N) ℚ),
    S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) k →
      aeval (rootOfUnityPoint N k) (powerSumHom N S) =
        (k : ℂ) * ((coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) S : ℚ) : ℂ)

def SchSchurHomogeneous.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r : ℕ) (lam : Fin r → ℕ),
    (schur σ lam).IsHomogeneous (∑ i, lam i)

def SchSchurRowsToK.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k : ℕ) (nu : Fin r → ℕ), Antitone nu →
    ∑ i, nu i = k →
    schur σ nu = schur σ (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)

def SchSchurEvalMatrix.Statement : Prop :=
  ∀ (N k r : ℕ) (nu : Fin r → ℕ), 1 ≤ k → k ≤ N →
    aeval (rootOfUnityPoint N k) (schur (Fin N) nu) = (rootOfUnityJTMatrix k nu).det

def SchRootOfUnityBialternant.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k →
    (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
      (rootOfUnityJTMatrix k nu).det * vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ))

def SchRootOfUnityRowsPerm.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ) (π : Equiv.Perm (Fin k)), 1 ≤ k →
    (∀ i, l i % k = k - 1 - (π i : ℕ)) →
      (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det

def SchRootOfUnityRowsEq.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ) (i i' : Fin k), i ≠ i' → l i % k = l i' % k →
    (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)).det = 0

def SchHookResidues.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    (∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1) →
    ∃ π : Equiv.Perm (Fin k), (∀ i, (nu i + (k - 1 - (i : ℕ))) % k = k - 1 - (π i : ℕ)) ∧
      ((Equiv.Perm.sign π : ℤ)) =
        (-1) ^ (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu i = 1).card

def SchResidueCount.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ), (∀ i, l i < 2 * k) → Function.Injective (fun i => l i % k) →
    ∑ i, l i = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card

def SchNonHookResidues.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    ¬ (∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1) →
    ∃ i i' : Fin k, i ≠ i' ∧ (nu i + (k - 1 - (i : ℕ))) % k = (nu i' + (k - 1 - (i' : ℕ))) % k

def SchRootOfUnityVandermondeNe.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) ≠ 0

def SchJTMatrixDetAtRoots.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    (rootOfUnityJTMatrix k nu).det =
      if ∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1 then
        (-1) ^ (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu i = 1).card else 0

def SchSchurAtRootsOfUnity.Statement : Prop :=
  ∀ (N r k : ℕ) (nu : Fin r → ℕ), 1 ≤ k → k ≤ N → Antitone nu → ∑ i, nu i = k →
    aeval (rootOfUnityPoint N k) (schur (Fin N) nu) =
      if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
        (-1) ^ (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card else 0

def smallBlockPlace (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a → Fin 1 × Fin (r + a) :=
  Sum.elim (yIndex 1 r a c 0) (zIndex 1 r a c 0)

def smallBlockOf (r a : ℕ) : SmallBlock → Fin (r + a) → Fin r ⊕ Fin a
  | .last, p =>
    if h : (p : ℕ) < a then Sum.inr ⟨p, h⟩ else Sum.inl ⟨(p : ℕ) - a, by have := p.isLt; omega⟩
  | .first, p =>
    if h : (p : ℕ) < r then Sum.inl ⟨p, h⟩ else Sum.inr ⟨(p : ℕ) - r, by have := p.isLt; omega⟩

def SchAevalSignedRename.Statement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (s : ℚ) (g : ι → κ)
    (d : ℕ) (P : MvPolynomial ι ℚ), P.IsHomogeneous d →
    aeval (fun i => C s * (X (g i) : MvPolynomial κ ℚ)) P = C (s ^ d) * rename g P

def SchAntisymmetrizePlace.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (Q : MvPolynomial (Fin r ⊕ Fin a) ℚ),
    antisymmetrize 1 (r + a) (rename (smallBlockPlace r a c) Q) =
      rename (smallBlockPlace r a c) (antisym Q)

def SchSmallBlockProduct.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (lam : Fin r → ℕ),
    aeval (yRoot 1 r a c 0) (schur (Fin r) lam) * vandermondeOf (yRoot 1 r a c 0) *
        vandermondeOf (zRoot 1 r a c 0) =
      C (c.sign ^ (∑ i, lam i + r * (r - 1) / 2)) *
        rename (smallBlockPlace r a c)
          (rename Sum.inl (alternant fun i : Fin r => lam i + (r - 1 - (i : ℕ))) *
            rename Sum.inr (alternant fun j : Fin a => a - 1 - (j : ℕ)))

def SchAlternantRenamePlace.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (v : Fin r ⊕ Fin a → ℕ),
    rename (smallBlockPlace r a c) (alternant v) =
      rename (fun p : Fin (r + a) => ((0 : Fin 1), p)) (alternant (v ∘ smallBlockOf r a c))

def SchConcatExponent.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock), ∃ τ : Equiv.Perm (Fin (r + a)),
    ∀ lam : Fin r → ℕ, (∀ i, a ≤ lam i) →
      (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) (fun j : Fin a => a - 1 - (j : ℕ)))
          ∘ smallBlockOf r a c =
        (fun p : Fin (r + a) =>
          Schur.padPartition (r + a) (fun i : Fin r => lam i - a) p + (r + a - 1 - (p : ℕ))) ∘ τ

def SchConcatAlternant.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock), ∃ s : ℚ, (s = 1 ∨ s = -1) ∧
    ∀ lam : Fin r → ℕ, (∀ i, a ≤ lam i) →
      rename (smallBlockPlace r a c)
          (alternant (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ)))
            (fun j : Fin a => a - 1 - (j : ℕ)))) =
        C s * rename (fun p : Fin (r + a) => ((0 : Fin 1), p))
          (vandermondeOf (fun p : Fin (r + a) => (X p : MvPolynomial (Fin (r + a)) ℚ)) *
            schur (Fin (r + a)) (fun i : Fin r => lam i - a))

def SchConcatAlternantZero.Statement : Prop :=
  ∀ (r a : ℕ) (lam : Fin r → ℕ), Antitone lam → ¬ (∀ i, a ≤ lam i) →
    alternant (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ)))
      (fun j : Fin a => a - 1 - (j : ℕ))) = 0

def SchBlockVandermondeOne.Statement : Prop :=
  ∀ N : ℕ, blockVandermonde 1 N =
    rename (fun p : Fin N => ((0 : Fin 1), p))
      (vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)))

def SchAlternantHomogeneous.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (e : ι → ℕ), (alternant e).IsHomogeneous (∑ i, e i)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

