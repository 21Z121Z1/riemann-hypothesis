import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0001
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0003
import Formalism.LandauZeroFreeBounds.Statement

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountA
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts

open DirichletCharacter

private theorem cast_prim {a b : ℕ} (h : a = b) (χ : DirichletCharacter ℂ a) :
    (cast (congrArg (DirichletCharacter ℂ) h) χ).IsPrimitive ↔ χ.IsPrimitive := by
  subst h; rfl

private theorem cast_L {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (χ : DirichletCharacter ℂ a) (s : ℂ) :
    DirichletCharacter.LFunction (cast (congrArg (DirichletCharacter ℂ) h) χ) s = DirichletCharacter.LFunction χ s := by
  subst h; rfl

def toSig {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : Σ N : ℕ, DirichletCharacter ℂ (N + 1) :=
  ⟨n - 1, cast (congrArg (DirichletCharacter ℂ) (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm) χ⟩

theorem toSig_fst {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : (toSig χ).1 + 1 = n := by
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))

theorem toSig_isPrimitive {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) :
    (toSig χ).2.IsPrimitive ↔ χ.IsPrimitive := by
  exact cast_prim (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm χ

theorem toSig_LFunction {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (s : ℂ) :
    DirichletCharacter.LFunction (toSig χ).2 s = DirichletCharacter.LFunction χ s := by
  exact cast_L (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm χ s

theorem toSig_level_eq {n m : ℕ} [NeZero n] [NeZero m] (χ : DirichletCharacter ℂ n) (ψ : DirichletCharacter ℂ m)
    (h : toSig χ = toSig ψ) : n = m := by
  have h1 := congrArg Sigma.fst h
  have hn := toSig_fst χ
  have hm := toSig_fst ψ
  omega

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.HDSucc
section
open Finset Complex Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

def hD (φ : ℕ → ℂ) (x : ℂ) (b : ℕ) : ℂ := ∑ a ∈ range (b + 1), φ a * x ^ (b - a)

theorem hD_succ (φ : ℕ → ℂ) (x : ℂ) (b : ℕ) : hD φ x (b + 1) = x * hD φ x b + φ (b + 1) := by
  unfold hD
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl (fun a ha => ?_)
  have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [show b + 1 - a = (b - a) + 1 by omega, pow_succ]; ring

theorem hD_tele (φ : ℕ → ℂ) (x ζ : ℂ) (K : ℕ) :
    (1 - x * ζ) * ∑ b ∈ range (K + 1), hD φ x b * ζ ^ b =
      ∑ b ∈ range (K + 1), φ b * ζ ^ b - x * hD φ x K * ζ ^ (K + 1) := by
  induction K with
  | zero => simp [hD]; ring
  | succ K ih =>
    rw [sum_range_succ (fun b => hD φ x b * ζ ^ b) (K + 1), mul_add, ih,
      sum_range_succ (fun b => φ b * ζ ^ b) (K + 1), hD_succ]; ring

theorem Tbound (n m : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (β : ℝ)
    (hβ : ∀ k, m + 1 ≤ k → k ≤ m + n → ‖∑ i, z i ^ k‖ ≤ β) (ζ : ℂ) (hζ1 : 1 ≤ ‖ζ‖)
    (hne : ∀ i, 1 - z i * ζ ≠ 0) :
    ‖∏ i, (1 - z i * ζ)‖ * ‖∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ)‖ ≤
      ‖ζ‖ ^ (m + 1) * (n * (‖ζ‖ ^ n * (2 ^ n * β))) := by
  set φ : ℕ → ℂ := fun a => (tp n z).coeff (n - a) with hφ
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; linarith
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ (m + 1) le_rfl (by omega))
  have hDn : ∀ x, hD φ x n = ∑ a ∈ range (n + 1), (tp n z).coeff a * x ^ a := by
    intro x
    unfold hD
    rw [← Finset.sum_range_reflect (fun a => (tp n z).coeff a * x ^ a) (n + 1)]
    refine sum_congr rfl (fun j hj => ?_)
    have : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [hφ]
    rw [show n + 1 - 1 - j = n - j by omega]
  have hrefl : ∑ b ∈ range (n + 1), φ b * ζ ^ b =
      ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by
    rw [← Finset.sum_range_reflect (fun a => (tp n z).coeff a * ζ ^ (n - a)) (n + 1)]
    refine sum_congr rfl (fun j hj => ?_)
    have : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [hφ]
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
  have perI : ∀ i, (1 - z i * ζ) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b = ∏ l, (1 - z l * ζ) := by
    intro i
    have e1 := hD_tele φ (z i) ζ (n - 1)
    rw [show n - 1 + 1 = n by omega] at e1
    rw [e1]
    have hs := hD_succ φ (z i) (n - 1)
    rw [show n - 1 + 1 = n by omega, hDn (z i), tp_root n z i] at hs
    rw [tp_rev n z ζ hζ0, ← hrefl, sum_range_succ]
    linear_combination ζ ^ n * hs
  have perT : ∀ i, (∏ l, (1 - z l * ζ)) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) =
      ∑ b ∈ range n, ∑ a ∈ range (b + 1), ζ ^ (m + 1) * (ζ ^ b * (φ a * z i ^ (m + 1 + b - a))) := by
    intro i
    rw [← perI i]
    have : (1 - z i * ζ) * (∑ b ∈ range n, hD φ (z i) b * ζ ^ b) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) =
        (z i * ζ) ^ (m + 1) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b := by
      field_simp [hne i]
    rw [this]
    unfold hD
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl (fun b _ => sum_congr rfl (fun a ha => ?_))
    have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
    rw [show m + 1 + b - a = (m + 1) + (b - a) by omega, pow_add, mul_pow]; ring
  have key : (∏ l, (1 - z l * ζ)) * ∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ) =
      ζ ^ (m + 1) * ∑ b ∈ range n, ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a) := by
    rw [mul_sum, sum_congr rfl (fun i _ => perT i)]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun b _ => ?_)
    rw [sum_comm]
  have hφsum : ∑ a ∈ range (n + 1), ‖φ a‖ ≤ 2 ^ n := by
    have : ∑ a ∈ range (n + 1), ‖φ a‖ = ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ := by
      rw [← Finset.sum_range_reflect (fun a => ‖(tp n z).coeff a‖) (n + 1)]
      refine sum_congr rfl (fun j hj => ?_)
      simp only [hφ]
      rw [show n + 1 - 1 - j = n - j by omega]
    rw [this]; exact tp_sum_norm n z hz
  rw [← norm_mul, key, norm_mul, norm_pow]
  gcongr
  calc ‖∑ b ∈ range n, ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖
      ≤ ∑ b ∈ range n, ‖ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ range n, ‖ζ‖ ^ n * (2 ^ n * β) := by
        refine sum_le_sum (fun b hb => ?_)
        have hbn : b < n := mem_range.mp hb
        rw [norm_mul, norm_pow]
        gcongr
        calc ‖∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖
            ≤ ∑ a ∈ range (b + 1), ‖φ a * ∑ i, z i ^ (m + 1 + b - a)‖ := norm_sum_le _ _
          _ ≤ ∑ a ∈ range (b + 1), ‖φ a‖ * β := by
              refine sum_le_sum (fun a ha => ?_)
              have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
              rw [norm_mul]
              gcongr
              exact hβ _ (by omega) (by omega)
          _ ≤ ∑ a ∈ range (n + 1), ‖φ a‖ * β := by
              apply sum_le_sum_of_subset_of_nonneg
              · exact range_subset_range.mpr (by omega)
              · intro a _ _; positivity
          _ = (∑ a ∈ range (n + 1), ‖φ a‖) * β := by rw [sum_mul]
          _ ≤ 2 ^ n * β := by gcongr
    _ = n * (‖ζ‖ ^ n * (2 ^ n * β)) := by rw [sum_const, card_range, nsmul_eq_mul]

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqPage
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem inRegion_of_lt {c Z β : ℝ} {q : ℕ} (hc : 0 < c) (hZ : 3 ≤ Z) (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Z ^ 2)
    (hβ : 1 - c / 3 / Real.log Z < β) : Formalism.ZeroFreeDirichlet.InRegion c q (β : ℂ) := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]
  have hZpos : 0 < Z := by linarith
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have h2q : 0 < Real.log ((q : ℝ) * 2) := Real.log_pos (by linarith)
  have hZ3 : Real.log (Z ^ 3) = 3 * Real.log Z := by rw [Real.log_pow]; norm_num
  have hle : Real.log ((q : ℝ) * 2) ≤ 3 * Real.log Z := by
    rw [← hZ3]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hdiv : c / 3 / Real.log Z ≤ c / Real.log ((q : ℝ) * 2) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le h2q hle
  linarith

theorem isLZero_changeLevel {M q : ℕ} [NeZero M] [NeZero q] (h : M ∣ q) (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1)
    {s : ℂ} (hs : DirichletCharacter.LFunction χ s = 0) :
    Formalism.ZeroFreeDirichlet.IsLZero (DirichletCharacter.changeLevel h χ) s := by
  refine ⟨Or.inl ?_, ?_⟩
  · intro h1
    apply hχ
    apply DirichletCharacter.changeLevel_injective h
    rw [h1, map_one]
  · rw [DirichletCharacter.LFunction_changeLevel h χ (Or.inl hχ), hs, zero_mul]

theorem page_across (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (Z : ℝ) (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (χ₁ : DirichletCharacter ℂ M₁)
      (χ₂ : DirichletCharacter ℂ M₂) (β₁ β₂ : ℝ), 3 ≤ Z → (M₁ : ℝ) ≤ Z → (M₂ : ℝ) ≤ Z →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 →
      DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
      1 - c₀ / Real.log Z < β₁ → 1 - c₀ / Real.log Z < β₂ → β₁ < 1 → β₂ < 1 →
      ∀ n : ℕ, n.Coprime (M₁ * M₂) → χ₁ (n : ZMod M₁) = χ₂ (n : ZMod M₂) := by
  obtain ⟨c, hc, hzfr⟩ := hZ
  refine ⟨c / 3, by positivity, ?_⟩
  intro Z M₁ M₂ _ _ χ₁ χ₂ β₁ β₂ hZ3 hM₁ hM₂ _ _ hne₁ hne₂ hz₁ hz₂ hb₁ hb₂ _ _ n hn
  haveI : NeZero (M₁ * M₂) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hq1 : 1 ≤ M₁ * M₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hqZ : ((M₁ * M₂ : ℕ) : ℝ) ≤ Z ^ 2 := by
    push_cast
    rw [pow_two]
    exact mul_le_mul hM₁ hM₂ (Nat.cast_nonneg _) (by linarith)

  have hr₁ := inRegion_of_lt hc hZ3 hq1 hqZ hb₁
  have hr₂ := inRegion_of_lt hc hZ3 hq1 hqZ hb₂
  have hL₁ := isLZero_changeLevel (dvd_mul_right M₁ M₂) χ₁ hne₁ hz₁
  have hL₂ := isLZero_changeLevel (dvd_mul_left M₂ M₁) χ₂ hne₂ hz₂
  obtain ⟨-, -, -, -, huniq⟩ := hzfr (M₁ * M₂) _ _ hr₁ hL₁
  have heq := (huniq _ _ hr₂ hL₂).1
  have hv := congrArg (fun ψ : DirichletCharacter ℂ (M₁ * M₂) =>
    ψ ((ZMod.unitOfCoprime n hn : (ZMod (M₁ * M₂))ˣ) : ZMod (M₁ * M₂))) heq
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_left M₂ M₁),
    ZMod.cast_natCast (dvd_mul_right M₁ M₂)] at hv
  exact hv.symm

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHFinishB
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem u_disc (η : ℝ) (hη : 0 < η) (w : ℂ) (hw : η ≤ w.re) :
    ‖(η : ℂ) / w‖ ^ 2 ≤ ((η : ℂ) / w).re := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.div_re, Complex.normSq_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  have h1 : η * η ≤ η * w.re := mul_le_mul_of_nonneg_left hw hη.le
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hn.le)

theorem u_sum_re (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) :
    (∑ i, ((η : ℂ) / w i) ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := by
  have h : ∑ i, ((η : ℂ) / w i) ^ j = ((η ^ j : ℝ) : ℂ) * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, div_eq_mul_one_div, Complex.ofReal_pow]
  rw [h, Complex.re_ofReal_mul]

set_option maxHeartbeats 1000000 in
theorem core (c' C : ℝ) (A B : ℕ) (hc'0 : 0 < c') (hc'2 : c' ≤ 1 / 2) (hA1 : 1 ≤ A) (hB1 : 1 ≤ B)
    (hC : 0 < C)
    (hT : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
      (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
      ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c' ^ K ≤ (∑ i, z i ^ k).re)
    (q ε l b c₂ : ℝ) (hq : q = c' / 2 ^ A) (hε : ε = q / 4) (hl : l = -Real.log q)
    (hb : b = 2 * B / ε ^ 2 + 4) (hc₂0 : 0 < c₂) (hc₂ : c₂ ≤ ε ^ 2 / (25 * B * C * (2 * l + 2)))
    (large₂ lam η K0 : ℝ) (hK0 : b + 64 * A * Real.exp (l * b) < K0)
    (hη0 : 0 < η) (hηc : η ≤ q ^ 2 / 200) (hlam0 : 0 < lam) (hlamη : lam / η ≤ Real.exp (-K0))
    (hηL : η * large₂ < c₂ * K0) (hLg0 : 0 < large₂)
    (N : ℕ) (w : Fin N → ℂ) (hw : ∀ i, η ≤ (w i).re) (hi0 : ∃ i, w i = ((η + η : ℝ) : ℂ))
    (hpow : ∀ j : ℕ, 1 ≤ j → (∑ i, 1 / (w i) ^ j).re ≤ 2 * j * lam / η ^ (j + 1) + C * large₂ * 25 ^ j) :
    False := by
  have h2A : (2 : ℝ) ≤ 2 ^ A := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ A := pow_le_pow_right₀ (by norm_num) hA1
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq4 : q ≤ 1 / 4 := by
    rw [hq, div_le_iff₀ (by positivity)]; nlinarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 / 16 := by rw [hε]; linarith
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hl0 : 0 ≤ l := by
    rw [hl]; have := Real.log_nonpos hq0.le (by linarith); linarith
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hK0pos : 0 < K0 := by
    have : 0 ≤ 64 * A * Real.exp (l * b) := by positivity
    linarith
  set u : Fin N → ℂ := fun i => (η : ℂ) / w i with hu_def
  have hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re := fun i => u_disc η hη0 (w i) (hw i)
  have hi : ∃ i, 1 / 2 ≤ ‖u i‖ := by
    obtain ⟨i, hi⟩ := hi0
    refine ⟨i, ?_⟩
    simp only [hu_def, hi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0,
      abs_of_pos (by linarith : (0 : ℝ) < η + η)]
    rw [le_div_iff₀ (by linarith)]; linarith
  set S : ℝ := ∑ i, (u i).re with hS_def
  have hS_eq : S = η * (∑ i, 1 / (w i) ^ 1).re := by
    have := u_sum_re η w 1
    simp only [pow_one] at this ⊢
    rw [hS_def, ← this, Complex.re_sum]
  have hlam1 : lam / η ≤ 1 := le_trans hlamη (by rw [Real.exp_le_one_iff]; linarith)
  have hS : S ≤ 2 * (lam / η) + 25 * C * (η * large₂) := by
    have h1 := hpow 1 le_rfl
    rw [hS_eq]
    have h2 := mul_le_mul_of_nonneg_left h1 hη0.le
    have h3 : η * (2 * ((1 : ℕ) : ℝ) * lam / η ^ (1 + 1) + C * large₂ * 25 ^ 1) = 2 * (lam / η) + 25 * C * (η * large₂) := by
      field_simp; ring
    linarith
  set Sb : ℝ := 2 + 25 * C * c₂ * K0 with hSb_def
  have hSb0 : 0 ≤ Sb := by positivity
  have hηL' : 25 * C * (η * large₂) ≤ 25 * C * (c₂ * K0) :=
    mul_le_mul_of_nonneg_left hηL.le (by positivity)
  have hSSb : S ≤ Sb := by rw [hSb_def]; linarith only [hηL', hS, hlam1]
  set x : ℝ := B * Sb / ε ^ 2 with hx_def
  have hx0 : 0 ≤ x := by positivity
  set K : ℕ := ⌈x⌉₊ + 3 with hK_def
  have hK3 : 3 ≤ K := by omega
  have hKr : (K : ℝ) = ⌈x⌉₊ + 3 := by rw [hK_def]; push_cast; ring
  have hxK : x ≤ ⌈x⌉₊ := Nat.le_ceil x
  have hxK' : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le (by linarith)
  have hSbx : Sb ≤ x := by
    rw [hx_def, le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hε2 hSb0
    have h2 := mul_le_mul_of_nonneg_right hBr hSb0
    linarith only [h1, h2]
  have hBS : (B : ℝ) * S ≤ ε ^ 2 * K := by
    have h1 : (B : ℝ) * S ≤ B * Sb := mul_le_mul_of_nonneg_left hSSb (by positivity)
    have h2 : (B : ℝ) * Sb = ε ^ 2 * x := by rw [hx_def]; field_simp
    have h3 : ε ^ 2 * x ≤ ε ^ 2 * K := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  obtain ⟨j, hKj, hjA, hj⟩ := near_far c' A B hc'0 hT ε hε0 (by linarith) N u hu hi K (by omega) hBS
  have hj1 : 1 ≤ j := by omega
  have hpj := hpow j hj1
  have hsumj : (∑ i, u i ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := u_sum_re η w j
  have hηj : 0 < η ^ j := pow_pos hη0 j
  have hRe : (∑ i, u i ^ j).re ≤ 2 * j * (lam / η) + C * (η * large₂) * 25 * (25 * η) ^ (j - 1) := by
    rw [hsumj]
    have h2 := mul_le_mul_of_nonneg_left hpj hηj.le
    have h3 : η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1) + C * large₂ * 25 ^ j) =
        2 * j * (lam / η) + C * (η * large₂) * 25 * (25 * η) ^ (j - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [mul_pow, pow_succ, pow_succ]
      field_simp
      ring
    linarith

  have hjAK : (j : ℝ) ≤ A * K := by exact_mod_cast hjA
  have hB1' : 2 * j * (lam / η) ≤ 2 * A * K * Real.exp (-K0) := by
    have h0 : 0 ≤ lam / η := by positivity
    have : (j : ℝ) * (lam / η) ≤ (A * K) * Real.exp (-K0) :=
      mul_le_mul hjAK hlamη h0 (by positivity)
    linarith only [this]
  have h25 : 25 * η ≤ q ^ 2 / 8 := by linarith
  have h25' : q ^ 2 / 8 ≤ 1 := by
    have : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le (by linarith)
    linarith only [this]
  have hB2 : C * (η * large₂) * 25 * (25 * η) ^ (j - 1) ≤ K * (q ^ 2 / 8) ^ (K - 1) := by
    have ha : C * (η * large₂) * 25 ≤ K := by
      have : C * (η * large₂) * 25 ≤ 25 * C * c₂ * K0 := by linarith only [hηL']
      linarith only [this, hSbx, hxK, hKr, hSb_def]
    have hp1 : (25 * η) ^ (j - 1) ≤ (25 * η) ^ (K - 1) :=
      pow_le_pow_of_le_one (by positivity) (by linarith) (by omega)
    have hp2 : (25 * η) ^ (K - 1) ≤ (q ^ 2 / 8) ^ (K - 1) := pow_le_pow_left₀ (by positivity) h25 _
    have hp0 : 0 ≤ (25 * η) ^ (j - 1) := by positivity
    have hC0 : 0 ≤ C * (η * large₂) * 25 := by positivity
    calc C * (η * large₂) * 25 * (25 * η) ^ (j - 1) ≤ K * (25 * η) ^ (j - 1) := mul_le_mul_of_nonneg_right ha hp0
      _ ≤ K * (q ^ 2 / 8) ^ (K - 1) := mul_le_mul_of_nonneg_left (le_trans hp1 hp2) (by positivity)
  have hB3 : ε ^ (j - 2) * S ≤ K * (q / 4) ^ K := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => le_trans (by positivity) (hu i))
    have hSK : S ≤ ε ^ 2 * K := by
      have := mul_le_mul_of_nonneg_right hBr hS0
      linarith only [this, hBS]
    have hp1 : ε ^ (j - 2) ≤ ε ^ (K - 2) := pow_le_pow_of_le_one hε0.le (by linarith) (by omega)
    have hp2 : ε ^ (K - 2) * ε ^ 2 = ε ^ K := by rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ K)]
    calc ε ^ (j - 2) * S ≤ ε ^ (K - 2) * S := mul_le_mul_of_nonneg_right hp1 hS0
      _ ≤ ε ^ (K - 2) * (ε ^ 2 * K) := mul_le_mul_of_nonneg_left hSK (by positivity)
      _ = K * ε ^ K := by rw [← hp2]; ring
      _ = K * (q / 4) ^ K := by rw [hε]
  have hLHS : q ^ K ≤ c' ^ K * (1 / 2) ^ j := by
    have h1 : q ^ K = c' ^ K * (1 / 2) ^ (A * K) := by
      rw [hq, div_pow, ← pow_mul, one_div_pow]; ring
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hjA
  have hmain : q ^ K ≤ 2 * A * K * Real.exp (-K0) + K * (q ^ 2 / 8) ^ (K - 1) + K * (q / 4) ^ K := by
    linarith
  set a : ℝ := 25 * B * C * c₂ / ε ^ 2 with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha : a * (2 * l + 2) ≤ 1 := by
    have h1 : c₂ * (25 * B * C * (2 * l + 2)) ≤ ε ^ 2 := by
      rwa [le_div_iff₀ (by positivity)] at hc₂
    rw [ha_def, div_mul_eq_mul_div, div_le_one (by positivity)]
    have : 25 * (B : ℝ) * C * c₂ * (2 * l + 2) = c₂ * (25 * B * C * (2 * l + 2)) := by ring
    linarith only [this, h1]
  have hKab : (K : ℝ) ≤ a * K0 + b := by
    have : x = a * K0 + (b - 4) := by
      rw [hx_def, ha_def, hb, hSb_def]; field_simp; ring
    linarith
  exact final_contra q A K0 a b l K hq0 hq4 hl hAr hK3 hK0pos ha0 ha hb0 hKab hK0 hmain

end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
end
end

