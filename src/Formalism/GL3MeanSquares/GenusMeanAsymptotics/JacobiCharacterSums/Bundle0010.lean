import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0001
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0005
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
import Formalism.GL3MeanSquares.HookFormulaTorsion.TwistIsPrimitiveCharacter
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0007
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0009
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0008
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZPair
import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle0001
import Formalism.GL3MeanSquares.Bundle0004
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0007
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0001

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountFinal
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts

open DirichletCharacter

theorem boxCountHyp_of_zeroDensityBox (h : ZeroDensityBox) : ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C := by
  obtain ⟨C₀, hC₀⟩ := h
  refine ⟨max C₀ 0, ?_⟩
  intro t _ θ Q S hθ hθ2 hS
  by_cases hSe : S = ∅
  · subst hSe
    simp only [Finset.card_empty, Nat.cast_zero]
    apply mul_nonneg (le_max_right _ _)
    rcases le_or_gt 0 Q with hQ | hQ
    · exact Real.rpow_nonneg hQ _
    · rw [Real.rpow_def_of_neg hQ]
      apply mul_nonneg (Real.exp_pos _).le
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
  obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.2 hSe
  have htpos : 1 ≤ t := Nat.one_le_iff_ne_zero.2 (NeZero.ne t)
  have hQ3 : (3 : ℝ) ≤ Q := by
    obtain ⟨_, h4, _, hle, _⟩ := hS q₀ hq₀
    have hq3 : 3 ≤ q₀ := by omega
    have : 3 ≤ t * q₀ := le_trans hq3 (Nat.le_mul_of_pos_left _ htpos)
    have h3 : (3 : ℝ) ≤ ((t * q₀ : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  classical
  let f : ℕ → Σ N : ℕ, DirichletCharacter ℂ (N + 1) := fun q =>
    if hq : q.Prime then
      haveI : Fact q.Prime := ⟨hq⟩
      toSig (Formalism.HermitianLattices.ZeroFreeRegionGL2.tw θ q)
    else ⟨0, 1⟩
  have hf : ∀ q (hq : Fact q.Prime), f q = toSig (Formalism.HermitianLattices.ZeroFreeRegionGL2.tw θ q) := by
    intro q hq
    simp only [f, dif_pos hq.out]
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    obtain ⟨ia, -⟩ := hS a ha
    obtain ⟨ib, -⟩ := hS b hb
    rw [hf a ia, hf b ib] at hab
    have := toSig_level_eq _ _ hab
    exact Nat.eq_of_mul_eq_mul_left htpos this
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have key := hC₀ Q (S.image f) hQ3 (by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨iq, h4, hco, hle, hbox⟩ := hS q hq
    rw [hf q iq]
    refine ⟨?_, ?_, ?_⟩
    · rw [toSig_isPrimitive]
      exact (Formalism.HermitianLattices.ThinSetIntegral.twist_is_primitive_character.2 t θ q hθ (by omega) hco).1
    · rw [toSig_fst]; exact hle
    · unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox at hbox
      push Not at hbox
      obtain ⟨s, h1, h2, h3⟩ := hbox
      exact ⟨s, h1, h2, by rw [toSig_LFunction]; exact h3⟩)
  rw [hcard] at key
  calc (S.card : ℝ) ≤ C₀ * Q ^ (1 / 4 : ℝ) := key
    _ ≤ max C₀ 0 * Q ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZAll
section
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem zero_density_box : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZeroDensityBox :=
  final_bound_of_assembly (coefficient_square_bound Formalism.FX.divisor_weight_bound) (zero_detection mollifier_identity)
    (blockCountOf_statement duality_inequality (pair_twist_bound pair_sum_bound)) numeric_constants

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

def MeanSquareHypW (ε C x₀ : ℝ) : Prop :=
  ∀ (x X : ℝ) (m₀ a₀ : ℕ) (κ : ℕ → ℂ), x₀ ≤ x → 8 ∣ m₀ →
    (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ 400 < (p : ℝ)) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ n, ‖κ n‖ ≤ 1) → (∀ a b, κ (a * b) = κ a * κ b) →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) ∧
    (∑ q ∈ PPset m₀ a₀ X,
        ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
      C * x * Real.log x * ((PPset m₀ a₀ X).card : ℝ)

def liX (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def piAP (X : ℝ) (M b : ℕ) : ℕ :=
  ((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card

def IsExcPair {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) : Prop :=
  χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 ∧
    1 - 1 / (8 * Real.log M) < β₁ ∧ β₁ < 1

def mainAP {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (b : ℕ) (X : ℝ) : ℝ :=
  match e with
  | none => liX X / (M.totient : ℝ)
  | some (χ₁, β₁) => (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ)

def PNTAPRelW : Prop :=
  ∃ c₃ A₀ C₀ : ℝ, 0 < c₃ ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M →
    ∃ e : Option (DirichletCharacter ℂ M × ℝ),
      (∀ p : DirichletCharacter ℂ M × ℝ, e = some p → IsExcPair p.1 p.2) ∧
      (e = none → ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), ¬ IsExcPair χ₁ β₁) ∧
      ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X → b.Coprime M →
        |(piAP X M b : ℝ) - mainAP e b X| ≤
          A₀ * (Real.exp (-(c₃ * Real.log X / Real.log M)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            mainAP e b X

def soutPart (m₀ N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors.filter (fun p => Odd (N.factorization p) ∧ ¬ p ∣ m₀), p

def sP (c : ℕ → ℝ) (N p : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), c n

def RR (c : ℕ → ℝ) (m₀ N : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)), c n

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContourA
section
open Complex MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_shift_alg (S R V0 V1 E a b : ℂ) (hS : S = (1 / (2 * Real.pi) : ℂ) * (V0 + E))
    (hrect : a - b + I * V0 - I * V1 = 2 * Real.pi * I * R) :
    (2 * Real.pi : ℂ) * (S - R) = E + I * (a - b) + V1 := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [hS, mul_sub, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  linear_combination (-I) * hrect + (V0 - V1 - 2 * Real.pi * R) * Complex.I_sq

theorem tail_shift_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (y σ₁ T : ℝ)
    (hy : 1 ≤ y) (hσ₁ : 0 < σ₁) (hσ₁' : σ₁ < 1) (hT : 0 < T)
    (hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T → DirichletCharacter.LFunction χ w ≠ 0) :
    (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y - Formalism.ZeroFreeDirichlet.negLD χ 1 * y) =
      (∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      + I * ((∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - ∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (T : ℂ) * I))
      + ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y ((σ₁ : ℂ) + (u : ℂ) * I) := by
  obtain ⟨hint, hS⟩ := Formalism.ZeroFreeDirichlet.perron_formula_character N χ y hy 2 (by norm_num)
  have hrect := Formalism.ZeroFreeDirichlet.rectangle_contour_shift_character N χ hχ y (by linarith) σ₁ 2 T ∅ hσ₁ hσ₁' (by norm_num) hT
    (by simp) (fun w h1 h2 h3 hL => absurd hL (hzf w h1 h2 h3)) (by simp)
  simp only [Finset.sum_empty, sub_zero] at hrect
  unfold Formalism.ZF.rectInt at hrect
  rw [← integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint,
    ← intervalIntegral.integral_of_le (a := -T) (b := T) (by linarith)] at hS
  exact tail_shift_alg _ _ _ _ _ _ _ hS hrect

end Formalism.HermitianLattices.Ext.BoxTail
end
end

