import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006
import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLemmaLfunctionZeros
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma landau_lemma_lfunction_zeros (hLL : LandauLocal3) {C : ℝ}
    (hC : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖))
    (hInv : LInvBound) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hσ1 : 26 / 27 ≤ s.re) (hσ2 : s.re < 11 / 10) (hfs : DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) ∧
        DirichletCharacter.LFunction χ ρ = 0)) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1) ∧
      (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
        Real.log ((q : ℝ) * (|s.im| + 2)) / Real.log 2 ∧
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
          Real.log ((q : ℝ) * (|s.im| + 2))) := by
  set z₀ : ℂ := (21 / 20 : ℂ) + s.im * I with hz₀
  have hz₀re : z₀.re = 21 / 20 := by simp [hz₀]
  set A : ℝ := 21 * (|C| + 1) with hAdef
  have hq1 := one_le_modulus_real q
  have hX : (0 : ℝ) < (q : ℝ) * (|s.im| + 2) := by positivity
  set M : ℝ := 2 * A * ((q : ℝ) * (|s.im| + 2)) with hMdef
  have hA1 : 1 ≤ A := by
    have := abs_nonneg C
    rw [hAdef]
    nlinarith
  have hM1 : 1 ≤ M := by
    have h2 : 2 ≤ (q : ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
    rw [hMdef]
    nlinarith
  have hf0 : DirichletCharacter.LFunction χ z₀ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hz₀re]; norm_num)
  have hinv := hInv q χ z₀ (by rw [hz₀re]; norm_num)
  rw [hz₀re] at hinv
  have h21 : ‖DirichletCharacter.LFunction χ z₀‖⁻¹ ≤ 21 := by
    have e : (21 / 20 : ℝ) / (21 / 20 - 1) = 21 := by norm_num
    linarith
  have hlow : 1 ≤ 21 * ‖DirichletCharacter.LFunction χ z₀‖ := by
    have hp : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := norm_pos_iff.2 hf0
    have := mul_le_mul_of_nonneg_right h21 hp.le
    rwa [inv_mul_cancel₀ hp.ne'] at this
  have hbound : ∀ z ∈ Metric.closedBall z₀ (11 / 20),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre := re_ge_of_mem_closedBall hz
    rw [hz₀re] at hre
    have h1 := hC q χ hχ z (by linarith)
    have hn := norm_le_norm_add_of_mem_closedBall' hz
    have hn0 := norm_disc_center_le s.im
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hz1 : 1 + ‖z‖ ≤ 2 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
    have hY : 0 ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by positivity
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * q * (1 + ‖z‖) := h1
      _ ≤ |C| * q * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hq0)
            (by positivity)
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hq0) hz1 (by positivity)
          positivity
      _ = (|C| + 1) * q * (2 * (|s.im| + 2)) * 1 := by ring
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) * (21 * ‖DirichletCharacter.LFunction χ z₀‖) :=
          mul_le_mul_of_nonneg_left hlow hY
      _ = M * ‖DirichletCharacter.LFunction χ z₀‖ := by
          rw [hMdef, hAdef]
          ring
  obtain ⟨Z, m, hZ, -, -, hm1, hsum, hder⟩ := hLL (DirichletCharacter.LFunction χ) z₀ (11 / 20) M
    (by norm_num) hM1 (DirichletCharacter.differentiable_LFunction hχ).differentiableOn hf0 hbound
  have hlogM : Real.log M ≤ (Real.log (2 * A) / Real.log 2 + 1) * Real.log ((q : ℝ) * (|s.im| + 2)) :=
    log_le_of_le_exp_log_conductor hA1 hM1 (log_two_le_log_analytic_conductor q s.im) (Real.exp_pos _)
      (by rw [Real.exp_log hX, hMdef])
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Z, m, hZ, hm1, ?_, ?_⟩
  · push_cast at hsum
    calc ∑ ρ ∈ Z, (m ρ : ℝ) ≤ Real.log M / Real.log 2 := hsum
      _ ≤ _ := div_le_div_of_nonneg_right hlogM hl2.le
  · have hs6 : s ∈ Metric.closedBall z₀ (11 / 20 / 6) := by
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have e : s - z₀ = ((s.re - 21 / 20 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hz₀]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ ≤ 72 * Real.log M / (11 / 20) := hder s hs6 hfs
      _ = 1440 / 11 * Real.log M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogM (by norm_num)

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LogDerivSubExceptionalZeros
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma log_deriv_sub_exceptional_zeros {c₁ : ℝ} (hc₁ : 0 < c₁) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {B : Finset ℝ} (hχ : χ ≠ 1) (hBcard : B.card ≤ 1)
    (hBmem : ∀ β ∈ B, χ ≠ 1 ∧ InRegion c₁ q (β : ℂ) ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0 ∧
      deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0)
    (hBall : ∀ s : ℂ, InRegion c₁ q s → IsLZero χ s → ∃ β ∈ B, s = (β : ℂ))
    {s : ℂ} (hs : InRegion (c₁ / 2) q s) (hσ1 : 26 / 27 ≤ s.re) (hσ2 : s.re < 11 / 10)
    {Z : Finset ℂ} {m : ℂ → ℕ}
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) ∧
        DirichletCharacter.LFunction χ ρ = 0))
    (hm3 : ∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1)
    {K : ℝ}
    (hsum : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ K * Real.log ((q : ℝ) * (|s.im| + 2)) / Real.log 2)
    (hE : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ 1440 / 11 * (K * Real.log ((q : ℝ) * (|s.im| + 2)))) :
    ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤
      1440 / 11 * (K * Real.log ((q : ℝ) * (|s.im| + 2))) +
      3 * K / (c₁ * Real.log 2) * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 + 120 / 11 := by
  have hs' : 1 - c₁ / 2 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hs
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog2 : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set L := Real.log ((q : ℝ) * (|s.im| + 2)) with hLdef
  have hL2 : Real.log 2 ≤ L :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := hLpos.ne'
  have hfar : ∀ ρ ∈ Z, (∀ β ∈ B, ρ ≠ (β : ℂ)) → ‖1 / (s - ρ)‖ ≤ 3 * L / c₁ := by
    intro ρ hρ hne
    obtain ⟨hball, hzero⟩ := (hZ ρ).mp hρ
    have hnot : ¬ InRegion c₁ q ρ := by
      intro hreg
      obtain ⟨β, hβ, hρβ⟩ := hBall ρ hreg ⟨Or.inl hχ, hzero⟩
      exact hne β hβ hρβ
    simp only [InRegion, not_le] at hnot
    have him : |ρ.im - s.im| ≤ 11 / 60 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      have h1 := Complex.abs_im_le_norm (ρ - ((21 / 20 : ℂ) + s.im * I))
      have hime : (ρ - ((21 / 20 : ℂ) + s.im * I)).im = ρ.im - s.im := by simp
      rw [hime] at h1
      linarith
    set Lρ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLρdef
    have hLρ2 : Real.log 2 ≤ Lρ :=
      Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
    have hLρpos : 0 < Lρ := by linarith
    have hLρ : Lρ ≤ 6 / 5 * L := by
      have h1 : (q : ℝ) * (|ρ.im| + 2) ≤ (q : ℝ) * (|s.im| + 2) * (131 / 120) := by
        have h0 : |ρ.im| ≤ |s.im| + 11 / 60 := by
          have := abs_sub_abs_le_abs_sub ρ.im s.im
          linarith
        nlinarith [abs_nonneg s.im]
      have h2 : Lρ ≤ L + Real.log (131 / 120) := by
        rw [hLρdef, hLdef, ← Real.log_mul (by positivity) (by norm_num)]
        exact Real.log_le_log (by positivity) h1
      have h3 : Real.log (131 / 120) ≤ 131 / 120 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    have h1 : c₁ / (6 / 5 * L) ≤ c₁ / Lρ := div_le_div_of_nonneg_left hc₁.le hLρpos hLρ
    have h1' : c₁ / (6 / 5 * L) = 5 * c₁ / (6 * L) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    have h2 : c₁ / (3 * L) = 5 * c₁ / (6 * L) - c₁ / 2 / L := by
      field_simp
      ring
    have hre : c₁ / (3 * L) ≤ (s - ρ).re := by
      rw [Complex.sub_re]
      linarith
    have hpos : 0 < c₁ / (3 * L) := div_pos hc₁ (by linarith)
    have hnorm : c₁ / (3 * L) ≤ ‖s - ρ‖ := hre.trans (Complex.re_le_norm _)
    rw [norm_div, norm_one]
    calc 1 / ‖s - ρ‖ ≤ 1 / (c₁ / (3 * L)) := one_div_le_one_div_of_le hpos hnorm
      _ = 3 * L / c₁ := by rw [one_div_div]
  have hnear : ∀ β ∈ B, (β : ℂ) ∉ Z → ‖1 / (s - (β : ℂ))‖ ≤ 120 / 11 := by
    intro β hβ hβZ
    have hout : ¬ (β : ℂ) ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) := by
      intro hin
      exact hβZ ((hZ _).mpr ⟨hin, (hBmem β hβ).2.2.1⟩)
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hout
    have hsc : ‖s - ((21 / 20 : ℂ) + s.im * I)‖ ≤ 47 / 540 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have hre' : (s - ((21 / 20 : ℂ) + s.im * I)).re = s.re - 21 / 20 := by simp
      have him' : (s - ((21 / 20 : ℂ) + s.im * I)).im = 0 := by simp
      rw [hre', him', abs_zero, add_zero, abs_le]
      constructor <;> linarith
    have htri := norm_sub_le_norm_sub_add_norm_sub (β : ℂ) s ((21 / 20 : ℂ) + s.im * I)
    rw [norm_sub_rev (β : ℂ) s] at htri
    have hd : (11 : ℝ) / 120 ≤ ‖s - (β : ℂ)‖ := by linarith
    rw [norm_div, norm_one]
    calc 1 / ‖s - (β : ℂ)‖ ≤ 1 / (11 / 120) := one_div_le_one_div_of_le (by norm_num) hd
      _ = 120 / 11 := by norm_num
  have hmsum : ∀ Z' ⊆ Z, (∀ ρ ∈ Z', ∀ β ∈ B, ρ ≠ (β : ℂ)) →
      ‖∑ ρ ∈ Z', (m ρ : ℂ) / (s - ρ)‖ ≤ 3 * K / (c₁ * Real.log 2) * L ^ 2 := by
    intro Z' hZ' hne
    have hc3 : 0 ≤ 3 * L / c₁ := div_nonneg (by linarith) hc₁.le
    calc ‖∑ ρ ∈ Z', (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z', ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z', (m ρ : ℝ) * (3 * L / c₁) := Finset.sum_le_sum fun ρ hρ => by
          rw [div_eq_mul_one_div, norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (hfar ρ (hZ' hρ) (hne ρ hρ)) (Nat.cast_nonneg _)
      _ = (∑ ρ ∈ Z', (m ρ : ℝ)) * (3 * L / c₁) := by rw [Finset.sum_mul]
      _ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) * (3 * L / c₁) :=
          mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum_of_subset_of_nonneg hZ' fun _ _ _ => Nat.cast_nonneg _) hc3
      _ ≤ K * L / Real.log 2 * (3 * L / c₁) := mul_le_mul_of_nonneg_right hsum hc3
      _ = 3 * K / (c₁ * Real.log 2) * L ^ 2 := by ring
  have hdecomp : negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ)) =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) +
        ((∑ β ∈ B, 1 / (s - (β : ℂ))) - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) := by
    unfold negLD
    ring
  have hdiff : ‖(∑ β ∈ B, 1 / (s - (β : ℂ))) - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
      3 * K / (c₁ * Real.log 2) * L ^ 2 + 120 / 11 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hBcard with h0 | h1
    · obtain rfl := Finset.card_eq_zero.mp h0
      rw [Finset.sum_empty, zero_sub, norm_neg]
      have h2 := hmsum Z subset_rfl (fun ρ _ β hβ => by simp at hβ)
      linarith
    · obtain ⟨β, rfl⟩ := Finset.card_eq_one.mp h1
      rw [Finset.sum_singleton]
      by_cases hβZ : (β : ℂ) ∈ Z
      · rw [← Finset.add_sum_erase Z _ hβZ,
          hm3 _ hβZ (hBmem β (Finset.mem_singleton_self β)).2.2.2, Nat.cast_one,
          sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
        have h2 := hmsum (Z.erase (β : ℂ)) (Finset.erase_subset _ _) (fun ρ hρ β' hβ' => by
          rw [Finset.mem_singleton] at hβ'
          subst hβ'
          exact Finset.ne_of_mem_erase hρ)
        linarith
      · refine (norm_sub_le _ _).trans ?_
        have h2 := hnear β (Finset.mem_singleton_self β) hβZ
        have h3 := hmsum Z subset_rfl (fun ρ hρ β' hβ' => by
          rw [Finset.mem_singleton] at hβ'
          subst hβ'
          exact fun h => hβZ (h ▸ hρ))
        linarith
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  linarith [hE, hdiff]

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SameCharacterLFunctionOne
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem prod_one_sub_inv_ge_inv_card_succ (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    1 / ((S.card : ℝ) + 1) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ p ∈ s, 2 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hsub : s ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨hs p hp, ha p hp⟩
    have hcard : s.card + 2 ≤ a := by
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Ico] at h1
      omega
    have hc : (insert a s).card = s.card + 1 := by simp [has]
    rw [Finset.prod_insert has, hc]
    push_cast
    have ih' := ih hs
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have ha' : (s.card : ℝ) + 2 ≤ a := by exact_mod_cast hcard
    have hk : (0 : ℝ) < (s.card : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) ≤ 1 - 1 / (a : ℝ) := by
      have h1 : (1 : ℝ) / a ≤ 1 := by rw [div_le_one ha0]; linarith
      linarith
    have e1 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) - 1 / ((s.card : ℝ) + 1 + 1) =
        ((a : ℝ) - ((s.card : ℝ) + 2)) / ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2)) := by
      field_simp
      ring
    have e2 : 0 ≤ ((a : ℝ) - ((s.card : ℝ) + 2)) /
        ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2)) :=
      div_nonneg (by linarith) (by positivity)
    have e3 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) ≤
        (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left ih' hpos
    linarith

theorem changeLevel_eq_of_agree_coprime {q₁ q : ℕ} [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁)
    (χ : DirichletCharacter ℂ q)
    (h : ∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q)) :
    DirichletCharacter.changeLevel (dvd_mul_right q₁ q) χ₁ =
      DirichletCharacter.changeLevel (dvd_mul_left q q₁) χ := by
  haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  ext a
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.cast_eq_val, ZMod.cast_eq_val]
  exact h _ (ZMod.val_coe_unit_coprime a)

theorem euler_factor_term_norm_le {M : ℕ} (φ : DirichletCharacter ℂ M) (p : ℕ) :
    ‖φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 / (p : ℝ) := by
  rw [norm_mul]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have h1 : ‖(p : ℂ) ^ (-(1 : ℂ))‖ = 1 / (p : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hp]
      simp [Real.rpow_neg_one]
    rw [h1]
    exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one φ _)

theorem euler_factor_product_upper {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ) :
    ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  linarith [euler_factor_term_norm_le φ p]

theorem euler_factor_product_lower {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have h1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  · have h1 := euler_factor_term_norm_le φ p
    have h2 := norm_sub_norm_le (1 : ℂ) (φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))
    rw [norm_one] at h2
    linarith

theorem prod_one_add_mul_one_sub_le_one (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∏ p ∈ S, (1 + 1 / (p : ℝ))) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_one (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have h1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2 : (0 : ℝ) ≤ 1 / p := by positivity
    nlinarith
  · have h2 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    nlinarith

theorem lfunction_one_same_character : SameCharacterLFunctionOne := by
  intro q₁ q _ _ χ₁ χ hχ₁ hχ h
  haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  have hS : ∀ p ∈ (q₁ * q).primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have hL₁ := DirichletCharacter.LFunction_changeLevel (dvd_mul_right q₁ q) χ₁ (s := 1)
    (Or.inl hχ₁)
  have hL := DirichletCharacter.LFunction_changeLevel (dvd_mul_left q q₁) χ (s := 1) (Or.inl hχ)
  rw [changeLevel_eq_of_agree_coprime χ₁ χ h, hL] at hL₁
  have hnorm : ‖DirichletCharacter.LFunction χ₁ 1‖ *
      ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ₁ (p : ZMod q₁) * (p : ℂ) ^ (-(1 : ℂ)))‖ =
      ‖DirichletCharacter.LFunction χ 1‖ *
      ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(1 : ℂ)))‖ := by
    rw [← norm_mul, ← norm_mul, hL₁]
  have hlow := euler_factor_product_lower χ₁ _ hS
  have hup := euler_factor_product_upper χ (q₁ * q).primeFactors
  have hge := prod_one_sub_inv_ge_inv_card_succ _ hS
  have hAB := prod_one_add_mul_one_sub_le_one _ hS
  have hk : (0 : ℝ) < ((q₁ * q).primeFactors.card : ℝ) + 1 := by positivity
  have hA0 : (0 : ℝ) ≤ ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have hB' : 1 ≤ (∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
      (((q₁ * q).primeFactors.card : ℝ) + 1) := by
    have h1 := mul_le_mul_of_nonneg_right hge hk.le
    rwa [one_div, inv_mul_cancel₀ hk.ne'] at h1
  have hx := norm_nonneg (DirichletCharacter.LFunction χ₁ 1)
  have hy := norm_nonneg (DirichletCharacter.LFunction χ 1)
  have h1 : ‖DirichletCharacter.LFunction χ₁ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ)) ≤
      ‖DirichletCharacter.LFunction χ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) := by
    calc _ ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ *
          ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ₁ (p : ZMod q₁) * (p : ℂ) ^ (-(1 : ℂ)))‖ :=
          mul_le_mul_of_nonneg_left hlow hx
      _ = _ := hnorm
      _ ≤ _ := mul_le_mul_of_nonneg_left hup hy
  have hA : ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) ≤
      ((q₁ * q).primeFactors.card : ℝ) + 1 := by nlinarith
  calc ‖DirichletCharacter.LFunction χ₁ 1‖
        ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ * ((∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1)) := le_mul_of_one_le_right hx hB'
    _ = (‖DirichletCharacter.LFunction χ₁ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) := by ring
    _ ≤ (‖DirichletCharacter.LFunction χ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) := mul_le_mul_of_nonneg_right h1 hk.le
    _ ≤ (‖DirichletCharacter.LFunction χ 1‖ * (((q₁ * q).primeFactors.card : ℝ) + 1)) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hy) hk.le
    _ = (((q₁ * q).primeFactors.card : ℝ) + 1) ^ 2 * ‖DirichletCharacter.LFunction χ 1‖ := by ring

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelBoundSameCharacter
section
open Real

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem log_three_mul_le_rpow {N ε : ℝ} (hN : 0 ≤ N) (hε : 0 < ε) :
    Real.log (3 * N) ≤ 2 * (3 : ℝ) ^ (ε / 2) / ε * N ^ (ε / 2) := by
  have h := Real.log_le_rpow_div (x := 3 * N) (by positivity) (half_pos hε)
  rw [Real.mul_rpow (by norm_num) hN] at h
  have e : (3 : ℝ) ^ (ε / 2) * N ^ (ε / 2) / (ε / 2) = 2 * (3 : ℝ) ^ (ε / 2) / ε * N ^ (ε / 2) := by
    field_simp
  linarith

theorem siegel_bound_key_rearrange {C A₁ CL x ℓ a K ε q₁ q : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (hKa : K * a ≤ ε / 2) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) (hA₁ : 0 ≤ A₁) (hx : 0 ≤ x) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ CL * Real.log (3 * (q₁ * q)))
    (hkey : 1 / 2 - C * (A₁ * x * ℓ) * (q₁ * q) ^ (K * a) / a ≤ 0) :
    a / (2 * (max C 1 * max A₁ 1 * max CL 1 * (2 * (3 : ℝ) ^ (ε / 2) / ε)) * q₁ ^ ε) * q ^ (-ε) ≤ x := by
  set Q := q₁ * q with hQ
  set L := 2 * (3 : ℝ) ^ (ε / 2) / ε with hLdef
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 ≤ Q := by linarith
  have hL0 : 0 < L := by rw [hLdef]; positivity
  have hk : a / 2 ≤ C * (A₁ * x * ℓ) * Q ^ (K * a) := by
    have h' : 1 / 2 ≤ C * (A₁ * x * ℓ) * Q ^ (K * a) / a := by linarith
    rw [le_div_iff₀ ha] at h'; linarith
  have hlog0 : 0 ≤ Real.log (3 * Q) := Real.log_nonneg (by linarith)
  have hlogL : Real.log (3 * Q) ≤ L * Q ^ (ε / 2) := log_three_mul_le_rpow hQ0 hε
  have hℓ' : ℓ ≤ max CL 1 * (L * Q ^ (ε / 2)) :=
    hℓ.trans ((mul_le_mul_of_nonneg_right (le_max_left CL 1) hlog0).trans
      (mul_le_mul_of_nonneg_left hlogL (by positivity)))
  have hQK : Q ^ (K * a) ≤ Q ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hQ1 hKa
  have hW0 : 0 ≤ A₁ * x * ℓ * Q ^ (K * a) := by positivity
  have step1 : C * (A₁ * x * ℓ) * Q ^ (K * a) ≤ max C 1 * (A₁ * x * ℓ * Q ^ (K * a)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left C 1) hW0
  have step2 : A₁ * x * ℓ * Q ^ (K * a)
      ≤ max A₁ 1 * x * (max CL 1 * (L * Q ^ (ε / 2))) * Q ^ (ε / 2) := by
    gcongr
    exact le_max_left A₁ 1
  have hQQ : Q ^ (ε / 2) * Q ^ (ε / 2) = q₁ ^ ε * q ^ ε := by
    rw [← Real.rpow_add (by linarith), add_halves, hQ, Real.mul_rpow (by linarith) (by linarith)]
  set M := max C 1 * max A₁ 1 * max CL 1 * L with hM
  have hM0 : 0 < M := by
    rw [hM]
    have : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : (0 : ℝ) < max A₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : (0 : ℝ) < max CL 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  have hmain : a / 2 ≤ M * x * (q₁ ^ ε * q ^ ε) := by
    have h3 := mul_le_mul_of_nonneg_left step2 (le_trans zero_le_one (le_max_right C 1))
    rw [← hQQ, hM]
    calc a / 2 ≤ _ := hk
      _ ≤ _ := step1
      _ ≤ _ := h3
      _ = _ := by ring
  have hq1e : 0 < q₁ ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  have hqe : 0 < q ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, div_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem siegel_bound_same_character {N₀ : ℕ} (hN₀ : N₀ ≠ 0) {A₁ x ε q₁ q : ℝ} (hε : 0 < ε) (hq₁ : 1 ≤ q₁)
    (hq : 1 ≤ q) (hNq : (N₀ : ℝ) = q₁ * q) (hA₁ : 0 < A₁) (hx : 0 ≤ x)
    (hS : A₁ ≤ ((N₀.primeFactors.card : ℝ) + 1) ^ 2 * x) :
    A₁ / (4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε) * q ^ (-ε) ≤ x := by
  set ω := N₀.primeFactors.card with hω

  have hpow : 2 ^ ω ≤ N₀ := by
    have h1 := Finset.pow_card_le_prod N₀.primeFactors (fun p => p) 2
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    exact h1.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hN₀) (Nat.prod_primeFactors_dvd N₀))
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast Nat.pos_of_ne_zero hN₀
  have hpowR : (2 : ℝ) ^ ω ≤ (N₀ : ℝ) := by exact_mod_cast hpow
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hωlog : (ω : ℝ) * Real.log 2 ≤ Real.log N₀ := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hpowR
  have hlog2N : Real.log (2 * N₀) = Real.log 2 + Real.log N₀ := Real.log_mul (by norm_num) hN0.ne'
  have hbound := Real.log_le_rpow_div (x := 2 * (N₀ : ℝ)) (by positivity) (half_pos hε)
  rw [Real.mul_rpow (by norm_num) hN0.le] at hbound
  set R := (2 : ℝ) ^ (ε / 2) * (N₀ : ℝ) ^ (ε / 2) / (ε / 2) with hR
  have hωR : ((ω : ℝ) + 1) * Real.log 2 ≤ R := by nlinarith
  have hω0 : (0 : ℝ) ≤ (ω : ℝ) + 1 := by positivity
  have hsq : (((ω : ℝ) + 1) * Real.log 2) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hωR 2
  have hR2 : R ^ 2 = 4 / ε ^ 2 * (2 : ℝ) ^ ε * (q₁ ^ ε * q ^ ε) := by
    have e1 : (2 : ℝ) ^ (ε / 2) * (2 : ℝ) ^ (ε / 2) = (2 : ℝ) ^ ε := by
      rw [← Real.rpow_add (by norm_num), add_halves]
    have e2 : (N₀ : ℝ) ^ (ε / 2) * (N₀ : ℝ) ^ (ε / 2) = q₁ ^ ε * q ^ ε := by
      rw [← Real.rpow_add hN0, add_halves, hNq, Real.mul_rpow (by linarith) (by linarith)]
    rw [hR, div_pow, mul_pow, sq ((2 : ℝ) ^ (ε / 2)), sq ((N₀ : ℝ) ^ (ε / 2)), e1, e2]
    field_simp
    ring
  have hT : ((ω : ℝ) + 1) ^ 2 ≤ 4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε * q ^ ε := by
    have hl22 : 0 < Real.log 2 ^ 2 := by positivity
    rw [mul_pow, hR2] at hsq
    have e : 4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε * q ^ ε
        = (4 / ε ^ 2 * (2 : ℝ) ^ ε * (q₁ ^ ε * q ^ ε)) / Real.log 2 ^ 2 := by
      field_simp
    rw [e, le_div_iff₀ hl22]
    exact hsq
  have hq1e : 0 < q₁ ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  have hqe : 0 < q ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, div_div, div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right hT hx
  nlinarith

end Formalism.ZeroFreeDirichlet
end
end

