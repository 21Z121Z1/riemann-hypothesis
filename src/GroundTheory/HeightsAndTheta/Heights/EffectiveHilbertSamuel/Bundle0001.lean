import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.JetOfMonomialSumStatement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

def JetOfMonomialSum.Statement : Prop :=
  ∀ (n p : ℕ) (u : Fin p → (Fin n → ℂ) → ℂ) (h : (Fin p → ℕ) → (Fin n → ℂ) → ℂ)
    (z₀ : Fin n → ℂ) (a : ℕ),
    (∀ i, AnalyticAt ℂ (u i) z₀) → (∀ i, u i z₀ = 0) → (∀ α, AnalyticAt ℂ (h α) z₀) →
    (∀ k < a, iteratedFDeriv ℂ k
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ = 0) ∧
    iteratedFDeriv ℂ a
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ =
      ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        h α z₀ • iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ ∧
    ∀ w : Fin n → ℂ, iteratedFDeriv ℂ a
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀
        (fun _ => w) =
      (a.factorial : ℂ) * ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        (∏ i, (fderiv ℂ (u i) z₀ w) ^ α i) * h α z₀

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PConstants
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

theorem log_add_log_two_pi_le : log 280 + log (2 * π) ≤ 7.6 := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_gt_three
  rw [← Real.log_mul (by norm_num) (by positivity)]
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hsplit : exp 7.6 = exp 1 ^ 7 * exp 0.6 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [hsplit]
  have h7 : (2.7182818283 : ℝ) ^ 7 ≤ exp 1 ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 7
  have h06 : (1 + 0.6 + 0.6 ^ 2 / 2 : ℝ) ≤ exp 0.6 :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hpos : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 7 := by positivity
  calc 280 * (2 * π) ≤ (2.7182818283 : ℝ) ^ 7 * (1 + 0.6 + 0.6 ^ 2 / 2) := by
        norm_num; nlinarith
    _ ≤ exp 1 ^ 7 * exp 0.6 :=
        mul_le_mul h7 h06 (by norm_num) (by positivity)

theorem log_two_pi_le : log (2 * π) ≤ 7.6 := by
  have h := log_add_log_two_pi_le
  have h280 : 0 ≤ log (280 : ℝ) := Real.log_nonneg (by norm_num)
  linarith

theorem half_log_add_le (D : ℝ) (hD : 1 ≤ D) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D := by
  have h1 := log_add_log_two_pi_le
  have h2 := log_two_pi_le
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ D - 1)]

theorem seven_point_six_le_log (ρ : ℝ) (hρ : 2 ^ 26 ≤ ρ) : 7.6 ≤ log ρ := by
  have h : log ((2 : ℝ) ^ 26) ≤ log ρ := Real.log_le_log (by positivity) hρ
  rw [Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

theorem three_point_eight_le_half_log (D ρ : ℝ) (hD : 0 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    3.8 * D ≤ (D / 2) * log ρ := by
  have h := seven_point_six_le_log ρ hρ
  nlinarith [mul_le_mul_of_nonneg_left h hD]

theorem half_log_add_le_half_log (D ρ : ℝ) (hD : 1 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D ∧ 3.8 * D ≤ (D / 2) * log ρ :=
  ⟨half_log_add_le D hD, three_point_eight_le_half_log D ρ (by linarith) hρ⟩

def vanishingOrderBound (T D N : ℝ) : ℝ := T + 2 * D + 4 + N

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PCurvature
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Real

noncomputable def curvX (ε v : ℝ) : ℝ := 1 + log (1 + ε ^ 2) - log (exp v + ε ^ 2)

noncomputable def curvEta (x : ℝ) : ℝ := x + log x

noncomputable def curvK (x : ℝ) : ℝ := 1 + 1 / x

noncomputable def curvPhi (x : ℝ) : ℝ := -log (curvEta x)

noncomputable def gradBound (x : ℝ) : ℝ := (x + 1) ^ 2 / ((x + 1) ^ 2 + curvEta x)

noncomputable def thetaCoeff (ε v : ℝ) : ℝ :=
  curvK (curvX ε v) * ε ^ 2 / (curvEta (curvX ε v) * exp v)
    + 1 / (curvX ε v ^ 2 * curvEta (curvX ε v))
    + (curvK (curvX ε v) / curvEta (curvX ε v)) ^ 2

noncomputable def gradSq (ε v : ℝ) : ℝ :=
  (curvK (curvX ε v) / curvEta (curvX ε v)) ^ 2 / thetaCoeff ε v

theorem le_curvEta {x : ℝ} (hx : 1 ≤ x) : x ≤ curvEta x := by
  have := log_nonneg hx
  unfold curvEta
  linarith

theorem sq_add_four_mul_le_two_exp {x : ℝ} (hx : 1 ≤ x) : x ^ 2 + 4 * x ≤ 2 * exp x := by
  set t := x - 1 with ht
  have ht0 : 0 ≤ t := by linarith
  have hxt : x = 1 + t := by linarith
  have he : exp x = exp 1 * exp t := by rw [← exp_add, hxt]
  have hq : 1 + t + t ^ 2 / 2 ≤ exp t := quadratic_le_exp_of_nonneg ht0
  have he1 : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have hp : 0 < 1 + t + t ^ 2 / 2 := by positivity
  have h1 : exp 1 * (1 + t + t ^ 2 / 2) ≤ exp 1 * exp t :=
    mul_le_mul_of_nonneg_left hq (exp_pos 1).le
  have h2 : 2.7 * (1 + t + t ^ 2 / 2) ≤ exp 1 * (1 + t + t ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right he1.le hp.le
  rw [he, hxt]
  nlinarith [sq_nonneg (t - 3 / 17)]

theorem exp_div_ge_of_one_le {x D : ℝ} (hx : 1 ≤ x) (hD : 1 ≤ D) :
    exp (D - 1) / 2 ≤ exp (D * x) / ((x + 1) ^ 2 + curvEta x) := by
  have hlog : log x ≤ x - 1 := log_le_sub_one_of_pos (by linarith)
  have hη : 1 ≤ curvEta x := le_trans hx (le_curvEta hx)
  have hden : 0 < (x + 1) ^ 2 + curvEta x := by positivity
  have hden' : (x + 1) ^ 2 + curvEta x ≤ 2 * exp x := by
    have := sq_add_four_mul_le_two_exp hx
    unfold curvEta
    nlinarith
  have hexp : exp (D - 1) * exp x ≤ exp (D * x) := by
    rw [← exp_add, exp_le_exp]
    nlinarith
  rw [le_div_iff₀ hden]
  have h0 : 0 < exp (D - 1) := exp_pos _
  calc exp (D - 1) / 2 * ((x + 1) ^ 2 + curvEta x)
      ≤ exp (D - 1) / 2 * (2 * exp x) :=
        mul_le_mul_of_nonneg_left hden' (by positivity)
    _ = exp (D - 1) * exp x := by ring
    _ ≤ exp (D * x) := hexp

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsLocUnifAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Set Filter Topology

def LocUnifAnalytic.Statement : Prop :=
  ∀ (D : ℕ) (V : Set (Fin D → ℂ)) (f : ℕ → (Fin D → ℂ) → ℂ) (g : (Fin D → ℂ) → ℂ),
    IsOpen V → (∀ n, AnalyticOnNhd ℂ (f n) V) → TendstoLocallyUniformlyOn f g atTop V →
      AnalyticOnNhd ℂ g V
end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

variable {n : ℕ} {MS : Type} [TopologicalSpace MS]

def normSq (x : Fin n → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

def complementOf (De : MvPolynomial (Fin n) ℂ) : Set (Fin n → ℂ) :=
  {x | MvPolynomial.eval x De ≠ 0}

def HolomorphicAlong (z : MS → (Fin n → ℂ)) (u : MS → ℂ) : Prop :=
  ∀ p : MS, ∃ e : OpenPartialHomeomorph MS (Fin n → ℂ),
    p ∈ e.source ∧ (∀ q ∈ e.source, z q = e q) ∧ AnalyticOnNhd ℂ (u ∘ e.symm) e.target

def OrderGT (z : MS → (Fin n → ℂ)) (u : MS → ℂ) (p : MS) (m : ℕ) : Prop :=
  ∃ C : ℝ, ∀ᶠ q in 𝓝 p, ‖u q‖ ≤ C * Real.sqrt (normSq (z q - z p)) ^ (m + 1)

def IsCoveringOfDegree (z : MS → (Fin n → ℂ)) (B : Set (Fin n → ℂ)) (δ : ℕ) : Prop :=
  ∃ h : ∀ p, z p ∈ B, IsCoveringMap (Set.codRestrict z B h) ∧
    ∀ x ∈ B, (z ⁻¹' {x}).encard = δ

def NormLemma.Statement : Prop :=
  ∀ (n : ℕ) (MS : Type) [TopologicalSpace MS] [T2Space MS] [SecondCountableTopology MS]
    [ConnectedSpace MS] (De : MvPolynomial (Fin n) ℂ) (z : MS → (Fin n → ℂ)) (δ : ℕ)
    (u : MS → ℂ) (C : ℝ) (m : ℕ),
    MvPolynomial.eval 0 De ≠ 0 →
    IsCoveringOfDegree z (complementOf De) δ →
    HolomorphicAlong z u →
    (∀ p, ‖u p‖ ≤ C * (1 + normSq (z p)) ^ ((m : ℝ) / 2)) →
    (∀ p, z p = 0 → OrderGT z u p m) →
    u = 0

def ShareCore.Statement : Prop :=
  ∀ (n : ℕ) (MS : Type) [TopologicalSpace MS] [T2Space MS] [SecondCountableTopology MS]
    [ConnectedSpace MS] (De : MvPolynomial (Fin n) ℂ) (z : MS → (Fin n → ℂ)) (δ : ℕ)
    (f θ τ : MS → ℂ) (C : ℝ) (e a : ℕ),
    MvPolynomial.eval 0 De ≠ 0 →
    IsCoveringOfDegree z (complementOf De) δ →
    HolomorphicAlong z f → HolomorphicAlong z θ → HolomorphicAlong z τ →
    θ ≠ 0 → τ ≠ 0 →
    (∀ p, ‖f p * θ p * τ p ^ a‖ ≤ C * (1 + normSq (z p)) ^ ((e : ℝ) / 2)) →
    (∀ p, z p = 0 → OrderGT z f p e) →
    f = 0

def ShareNumbers.Statement : Prop :=
  ∀ D N T : ℕ, 6 ≤ D → 2 * N ≤ D → 11 * D ^ 2 ≤ T →
    8 * ((T + 2 * D + 4 + N + 15) / 16) ≤ T + 8 ∧
    (T + 2 * D + 4 + N) + D + 1 - T = 3 * D + 5 + N ∧
    2 * (3 * D + 5 + N) ≤ 9 * D

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShellPolar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory

noncomputable section

def ShellPolar.Statement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ a b : ℝ, 0 < a → a ≤ b →
    ∫⁻ w in {w : Fin D → ℂ | a ≤ ∑ i, ‖w i‖ ^ 2 ∧ ∑ i, ‖w i‖ ^ 2 ≤ b},
        ENNReal.ofReal (((∑ i, ‖w i‖ ^ 2) ^ D)⁻¹) =
      ENNReal.ofReal (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (b / a))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

