import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0001
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Formalism.HermitianCurvature.Bundle0001

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormIteratedFDerivWithinInvOneLe
section
open MeasureTheory Module Set
open scoped Nat

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_iteratedFDeriv_id_le (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j (id : V → V) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | _ | m
  · rw [norm_iteratedFDeriv_zero]
    simp
  · rw [norm_iteratedFDeriv_one, fderiv_id]
    exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
  · rw [iteratedFDeriv_succ_eq_comp_right]
    have e : (fun y : V => fderiv ℝ (id : V → V) y) = fun _ => ContinuousLinearMap.id ℝ V := by
      funext y
      exact fderiv_id
    rw [e, iteratedFDeriv_const_of_ne (by omega : m + 1 ≠ 0)]
    simp
    positivity

theorem norm_iteratedFDeriv_inner_self_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
  have hB := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear
    (f := (id : V → V)) (g := (id : V → V)) (N := ⊤) contDiff_id contDiff_id x (n := n) le_top
  have e : (fun y : V => (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) (id y) (id y)) = fun y : V => inner ℝ y y := by
    funext y
    simp
  rw [e] at hB
  have hnB : ‖(innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ)‖ ≤ 1 := norm_innerSL_le ℝ
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) * (1 + ‖x‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := norm_iteratedFDeriv_id_le i x
          have h2 := norm_iteratedFDeriv_id_le (n - i) x
          have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
          gcongr
      _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [this]
          ring
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ := Finset.sum_nonneg fun i _ => by positivity
  calc ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ _ := hB
    _ ≤ 1 * (2 ^ n * (1 + ‖x‖) ^ 2) := mul_le_mul hnB hsum hS0 zero_le_one
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := one_mul _

theorem norm_iteratedFDerivWithin_inv_one_le (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t⁻¹) (Ioi 0) 1‖ ≤ i ! := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    (iteratedDerivWithin_of_isOpen isOpen_Ioi) (show (1 : ℝ) ∈ Ioi 0 by norm_num), iteratedDeriv_eq_iterate]
  have e : (fun t : ℝ => t⁻¹) = Inv.inv := rfl
  rw [e, iter_deriv_inv]
  simp

theorem norm_iteratedFDeriv_u_le (k : ℕ) (x₀ : V) :
    ‖iteratedFDeriv ℝ k (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x₀‖ ≤ (k ! * k ! * 4 ^ k) * (1 + ‖x₀‖ ^ 2)⁻¹ := by
  set q₀ : ℝ := 1 + ‖x₀‖ ^ 2 with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  set f : V → ℝ := fun y => q₀⁻¹ * (1 + inner ℝ y y) with hf
  have hfpos : ∀ y, 0 < f y := fun y => by
    simp only [hf, real_inner_self_eq_norm_sq]; positivity
  have hfc : ContDiff ℝ k f :=
    contDiff_const.mul (contDiff_const.add (contDiff_id.inner ℝ contDiff_id))
  have hfx : f x₀ = 1 := by
    simp only [hf, real_inner_self_eq_norm_sq]
    rw [← hq₀]
    exact inv_mul_cancel₀ hq₀pos.ne'
  have hu : (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) = q₀⁻¹ • ((fun t : ℝ => t⁻¹) ∘ f) := by
    funext y
    simp only [hf, Pi.smul_apply, Function.comp, real_inner_self_eq_norm_sq, smul_eq_mul]
    field_simp
  have hgc : ContDiff ℝ k ((fun t : ℝ => t⁻¹) ∘ f) :=
    hfc.inv fun y => (hfpos y).ne'
  rw [hu, iteratedFDeriv_const_smul_apply (hgc.contDiffAt), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hq₀pos), mul_comm]
  gcongr
  have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x₀‖ ≤ 4 ^ i := by
    intro i hi _
    have e : f = (fun _ : V => q₀⁻¹) + q₀⁻¹ • (fun y : V => inner ℝ y y) := by
      funext y; simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hin : ContDiff ℝ i (fun y : V => inner ℝ y y) := contDiff_id.inner ℝ contDiff_id
    have hc2 : ContDiffAt ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)) x₀ :=
      ((hin.const_smul q₀⁻¹ : ContDiff ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)))).contDiffAt
    have hc1 : ContDiffAt ℝ i (fun _ : V => q₀⁻¹) x₀ := contDiffAt_const
    rw [e, iteratedFDeriv_add_apply hc1 hc2,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add,
      iteratedFDeriv_const_smul_apply hin.contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq₀pos)]
    have h1 := norm_iteratedFDeriv_inner_self_le i x₀
    have h2 : (1 + ‖x₀‖) ^ 2 ≤ 2 * q₀ := by
      rw [hq₀]; nlinarith [sq_nonneg (‖x₀‖ - 1)]
    have h3 : (2 : ℝ) ^ i * 2 ≤ 4 ^ i := by
      have : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
      rw [this]
      gcongr
      exact le_self_pow₀ (by norm_num) (by omega)
    calc q₀⁻¹ * ‖iteratedFDeriv ℝ i (fun y : V => inner ℝ y y) x₀‖ ≤ q₀⁻¹ * (2 ^ i * (2 * q₀)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = 2 ^ i * 2 := by field_simp
      _ ≤ 4 ^ i := h3
  have hC : ∀ i, i ≤ k → ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t⁻¹) (Ioi 0) (f x₀)‖ ≤ k ! := by
    intro i hi
    rw [hfx]
    exact (norm_iteratedFDerivWithin_inv_one_le i).trans (by exact_mod_cast Nat.factorial_le hi)
  have hmain := norm_iteratedFDeriv_comp_le' (N := (k : ℕ∞)) (t := Ioi (0 : ℝ))
    (by rintro _ ⟨y, rfl⟩; exact hfpos y) (uniqueDiffOn_Ioi 0)
    (ContDiffOn.mono (contDiffOn_inv (𝕜 := ℝ)) (fun t (ht : t ∈ Ioi (0 : ℝ)) => (ne_of_gt ht : t ≠ 0))) hfc le_rfl x₀ hC hD
  calc ‖iteratedFDeriv ℝ k ((fun t : ℝ => t⁻¹) ∘ f) x₀‖ ≤ k ! * k ! * 4 ^ k := hmain
    _ = k ! * k ! * 4 ^ k := rfl

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RecText
section
namespace Formalism.FourierDecayAlt.P.RecText

open Finset Real

theorem geo (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1/2) :
    ∀ i, 1 ≤ i → ∑ t ∈ Icc 2 i, a ^ (t - 1) ≤ 2 * a - 2 * a ^ i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have : a ^ (n + 1) = a ^ n * a := pow_succ a n
    have h0 : 0 ≤ a ^ n := pow_nonneg ha0 n
    nlinarith

theorem recT : Formalism.FourierDecayAlt.RecursionText := by
  refine ⟨Real.exp 9, ?_⟩
  intro r a ε e σ ha0 ha1 hε hεa hra he hσ hrec
  set lam := 1 + ε + 2 * a with hlam
  set Q : ℕ → ℝ := fun k => ∏ j ∈ Icc 1 k, √(1 + e j) with hQdef
  have hQsucc : ∀ k, Q (k + 1) = Q k * √(1 + e (k + 1)) := by
    intro k; simp only [hQdef]; rw [Finset.prod_Icc_succ_top (by omega)]
  have hsq1 : ∀ j, 1 ≤ √(1 + e j) := fun j => by
    rw [Real.one_le_sqrt]; linarith [he j]
  have hQ0 : Q 0 = 1 := by simp [hQdef]
  have hQ1 : ∀ k, 1 ≤ Q k := by
    intro k; induction k with
    | zero => rw [hQ0]
    | succ k ih => rw [hQsucc]; nlinarith [hsq1 (k + 1)]
  have hQmono : Monotone Q := by
    apply monotone_nat_of_le_succ; intro k; rw [hQsucc]; nlinarith [hsq1 (k + 1), hQ1 k]
  have hlam1 : 1 ≤ lam := by linarith
  have hs0 := hσ 0
  have main : ∀ i, i ≤ r + 1 → σ i ≤ lam ^ i * Q i * σ 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hir
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp [hQ0]
      · have hrec' := hrec i hpos hir
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hk : k + 1 - 1 = k := by omega
        rw [hk] at hrec'
        set M := lam ^ k * Q (k + 1) * σ 0 with hM
        have hM0 : 0 ≤ M := by
          have := pow_nonneg (by linarith : (0:ℝ) ≤ lam) k
          have := hQ1 (k + 1)
          positivity
        have hk' := ih k (by omega) (by omega)
        have h1 : (1 + ε) * √(1 + e (k + 1)) * σ k ≤ (1 + ε) * M := by
          rw [hM, hQsucc]
          have : √(1 + e (k + 1)) * σ k ≤ √(1 + e (k + 1)) * (lam ^ k * Q k * σ 0) :=
            mul_le_mul_of_nonneg_left hk' (Real.sqrt_nonneg _)
          nlinarith
        have h2 : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * σ (k + 1 - t) ≤
            ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * M := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.mem_Icc] at ht
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha0 _)
          have := ih (k + 1 - t) (by omega) (by omega)
          refine this.trans ?_
          rw [hM]
          have e1 : lam ^ (k + 1 - t) ≤ lam ^ k := pow_le_pow_right₀ hlam1 (by omega)
          have e2 : Q (k + 1 - t) ≤ Q (k + 1) := hQmono (by omega)
          have e3 : 0 ≤ lam ^ (k + 1 - t) := pow_nonneg (by linarith) _
          have e4 : 0 ≤ Q (k + 1 - t) := by linarith [hQ1 (k + 1 - t)]
          have e5 : 0 ≤ lam ^ k := pow_nonneg (by linarith) _
          have := mul_le_mul e1 e2 e4 e5
          exact mul_le_mul_of_nonneg_right this hs0
        have h3 : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * M ≤ 2 * a * M := by
          rw [← Finset.sum_mul]
          have := geo a ha0 ha1 (k + 1) (by omega)
          have : 0 ≤ a ^ (k + 1) := pow_nonneg ha0 _
          apply mul_le_mul_of_nonneg_right _ hM0
          linarith
        have : lam ^ (k + 1) * Q (k + 1) * σ 0 = lam * M := by rw [hM]; ring
        rw [this]
        calc σ (k + 1) ≤ (1 + ε) * M + 2 * a * M := by linarith
          _ = lam * M := by rw [hlam]; ring
  have hfin := main (r + 1) le_rfl
  have hQsq : Q (r + 1) ^ 2 = ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by
    simp only [hQdef]; rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Real.sq_sqrt]; linarith [he j]
  have hP : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by rw [← hQsq]; positivity
  have hsr := hσ (r + 1)
  have step1 : σ (r + 1) ^ 2 ≤ (lam ^ (r + 1)) ^ 2 * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
    rw [← hQsq]
    have := pow_le_pow_left₀ hsr hfin 2
    calc σ (r + 1) ^ 2 ≤ (lam ^ (r + 1) * Q (r + 1) * σ 0) ^ 2 := this
      _ = _ := by ring
  set x := ((r : ℝ) + 1) * a with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx32 : x ≤ 3 / 2 := by rw [hxdef]; nlinarith
  have step2 : (lam ^ (r + 1)) ^ 2 ≤ Real.exp (6 * x) := by
    rw [← pow_mul]
    have h1 : lam ≤ Real.exp (ε + 2 * a) := by
      have := Real.add_one_le_exp (ε + 2 * a); rw [hlam]; linarith
    have h2 := pow_le_pow_left₀ (by linarith) h1 ((r + 1) * 2)
    refine h2.trans ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have step3 : Real.exp (6 * x) ≤ 1 + Real.exp 9 * x := by
    have ht0 : 0 ≤ 2 / 3 * x := by positivity
    have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (9:ℝ))
      (by linarith : (0:ℝ) ≤ 1 - 2 / 3 * x) ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have : 6 * x = 2 / 3 * x * 9 := by ring
    rw [this]
    have : 0 ≤ Real.exp 9 := (Real.exp_pos 9).le
    nlinarith
  have : (lam ^ (r + 1)) ^ 2 ≤ 1 + Real.exp 9 * ((r : ℝ) + 1) * a := by
    have := step2.trans step3; rw [hxdef] at this; linarith
  refine step1.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right this hP

end Formalism.FourierDecayAlt.P.RecText

theorem Formalism.FourierDecayAlt.P.coarseBound : Formalism.FourierDecayAlt.RecursionText := Formalism.FourierDecayAlt.P.RecText.recT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleInv
section
namespace Formalism.FourierDecayAlt.R.PInv

open Matrix LevelData

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem comm_mat_prod (x : A) :
    ∀ l : List (Matrix (Fin 2) (Fin 2) A), (∀ M ∈ l, ∀ i j, Commute x (M i j)) →
      ∀ i j, Commute x (l.prod i j)
  | [], _ => by
      intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | M :: l, h => by
      intro i j
      rw [List.prod_cons, Matrix.mul_apply]
      exact Commute.sum_right _ _ _ fun k _ =>
        (h M (by simp) i k).mul_right (comm_mat_prod x l (fun N hN => h N (by simp [hN])) k j)

theorem prod_mul_prod_eq_one : ∀ (n : ℕ) (f g : Fin n → A), (∀ i, f i * g i = 1) →
    (∀ i j, Commute (f i) (g j)) → (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h1, hc => by
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
      have hP : Commute (List.ofFn fun i => f i.succ).prod (g 0) :=
        Commute.list_prod_left _ _ (by
          intro a ha
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
          exact hc _ _)
      have ih := prod_mul_prod_eq_one n (fun i => f i.succ) (fun i => g i.succ)
        (fun i => h1 _) (fun i j => hc _ _)
      calc f 0 * (List.ofFn fun i => f i.succ).prod * (g 0 * (List.ofFn fun i => g i.succ).prod)
          = f 0 * ((List.ofFn fun i => f i.succ).prod * g 0) * (List.ofFn fun i => g i.succ).prod := by
            noncomm_ring
        _ = f 0 * g 0 * ((List.ofFn fun i => f i.succ).prod * (List.ofFn fun i => g i.succ).prod) := by
            rw [hP.eq]; noncomm_ring
        _ = 1 := by rw [h1, ih, one_mul]

variable {r : ℕ} (L : LevelData A r)

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_fcomm {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : Commute x y :=
  L.fns_comm x hx y hy

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_cb (l) : L.cb l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_cbi (l) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_c (l) : L.c l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ci (l) : L.ci l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζ : L.ζ ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζi : L.ζi ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζb : L.ζb ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζbi : L.ζbi ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_GG : L.GG ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_GGi : L.GGi ∈ L.fns := by simp [LevelData.fns]

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_comm_ofFn {x : A} {f : Fin r → A} (h : ∀ i, Commute x (f i)) :
    Commute x (List.ofFn f).prod :=
  Commute.list_prod_right _ _ (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact h i)

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tprod {x : A} (hp : ∀ l, Commute x (L.p l)) (hc : ∀ l, Commute x (L.c l))
    (hci : ∀ l, Commute x (L.ci l)) (Y : ℂ) (i j) : Commute x (L.Tprod Y i j) := by
  apply comm_mat_prod
  intro M hM
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hM)
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, (hp l).add_left, Algebra.commutes, hc l, hci l, Commute.neg_right,
      Commute.add_right, Commute.zero_right]
  exact Commute.add_right (Algebra.commute_algebraMap_right Y x) (hp l)

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tvprod {x : A} (hp : ∀ l, Commute x (L.pb l)) (hc : ∀ l, Commute x (L.cb l))
    (hci : ∀ l, Commute x (L.cbi l)) (Y : ℂ) (i j) : Commute x (L.Tvprod Y i j) := by
  apply comm_mat_prod
  intro M hM
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hM)
  intro i j
  fin_cases i <;> fin_cases j <;> simp [LevelData.Tvl, hc l, hci l]
  exact Commute.sub_right (Algebra.commute_algebraMap_right Y x) (hp l)

theorem comm_alg (x : A) (y : ℂ) : Commute x (algebraMap ℂ A y) := Algebra.commute_algebraMap_right y x

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_S_mem {x : A} (hx : x ∈ L.fns) : x ∈ Algebra.adjoin ℂ L.fns := Algebra.subset_adjoin hx

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_S_prod {f : Fin r → A} (hf : ∀ i, f i ∈ L.fns) :
    (List.ofFn f).prod ∈ Algebra.adjoin ℂ L.fns :=
  Subalgebra.list_prod_mem _ (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact L.inv_S_mem (hf i))

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Drbi_Drb : L.Drbi * L.Drb = 1 :=
  prod_mul_prod_eq_one r L.cbi L.cb L.cbi_cb (fun i j => L.inv_fcomm (L.inv_mem_cbi i) (L.inv_mem_cb j))
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Drb_Drbi : L.Drb * L.Drbi = 1 :=
  prod_mul_prod_eq_one r L.cb L.cbi L.cb_cbi (fun i j => L.inv_fcomm (L.inv_mem_cb i) (L.inv_mem_cbi j))
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Dri_Dr : L.Dri * L.Dr = 1 :=
  prod_mul_prod_eq_one r L.ci L.c L.ci_c (fun i j => L.inv_fcomm (L.inv_mem_ci i) (L.inv_mem_c j))
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Dr_Dri : L.Dr * L.Dri = 1 :=
  prod_mul_prod_eq_one r L.c L.ci L.c_ci (fun i j => L.inv_fcomm (L.inv_mem_c i) (L.inv_mem_ci j))

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_hR_bar (Y : ℂ) :
    L.G * L.Dbi * L.Dbi * L.Ahatv Y = L.Dr * L.GG * (L.ζbi * L.ζbi * L.Avr Y) := by
  letI : CommRing (Algebra.adjoin ℂ L.fns) := Algebra.adjoinCommRingOfComm ℂ L.fns_comm
  let Dr' : Algebra.adjoin ℂ L.fns := ⟨L.Dr, L.inv_S_prod L.inv_mem_c⟩
  let Drb' : Algebra.adjoin ℂ L.fns := ⟨L.Drb, L.inv_S_prod L.inv_mem_cb⟩
  let Drbi' : Algebra.adjoin ℂ L.fns := ⟨L.Drbi, L.inv_S_prod L.inv_mem_cbi⟩
  let GG' : Algebra.adjoin ℂ L.fns := ⟨L.GG, L.inv_S_mem L.inv_mem_GG⟩
  let z' : Algebra.adjoin ℂ L.fns := ⟨L.ζbi, L.inv_S_mem L.inv_mem_ζbi⟩
  have h1 : Drb' * Drbi' = 1 := Subtype.ext L.inv_Drb_Drbi
  have hS : Dr' * Drb' * GG' * (z' * Drbi') * (z' * Drbi') * Drb' = Dr' * GG' * (z' * z') := by
    linear_combination (Dr' * GG' * z' * z' * (Drb' * Drbi' + 1)) * h1
  have hA := congrArg Subtype.val hS
  simp only [LevelData.G, LevelData.Dbi, LevelData.Ahatv]
  calc L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * (L.Drb * L.Avr Y)
      = (L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * L.Drb) * L.Avr Y := by
        noncomm_ring
    _ = (L.Dr * L.GG * (L.ζbi * L.ζbi)) * L.Avr Y := by rw [show L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * L.Drb = L.Dr * L.GG * (L.ζbi * L.ζbi) from hA]
    _ = L.Dr * L.GG * (L.ζbi * L.ζbi * L.Avr Y) := by noncomm_ring

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_hR_hol (Y : ℂ) :
    L.G * L.Di * L.Di * L.Ahat Y = L.Drb * L.GG * (L.ζi * L.ζi * L.Ar Y) := by
  letI : CommRing (Algebra.adjoin ℂ L.fns) := Algebra.adjoinCommRingOfComm ℂ L.fns_comm
  let Dr' : Algebra.adjoin ℂ L.fns := ⟨L.Dr, L.inv_S_prod L.inv_mem_c⟩
  let Drb' : Algebra.adjoin ℂ L.fns := ⟨L.Drb, L.inv_S_prod L.inv_mem_cb⟩
  let Dri' : Algebra.adjoin ℂ L.fns := ⟨L.Dri, L.inv_S_prod L.inv_mem_ci⟩
  let GG' : Algebra.adjoin ℂ L.fns := ⟨L.GG, L.inv_S_mem L.inv_mem_GG⟩
  let z' : Algebra.adjoin ℂ L.fns := ⟨L.ζi, L.inv_S_mem L.inv_mem_ζi⟩
  have h1 : Dr' * Dri' = 1 := Subtype.ext L.inv_Dr_Dri
  have hS : Dr' * Drb' * GG' * (z' * Dri') * (z' * Dri') * Dr' = Drb' * GG' * (z' * z') := by
    linear_combination (Drb' * GG' * z' * z' * (Dr' * Dri' + 1)) * h1
  have hA := congrArg Subtype.val hS
  simp only [LevelData.G, LevelData.Di, LevelData.Ahat]
  calc L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * (L.Dr * L.Ar Y)
      = (L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * L.Dr) * L.Ar Y := by
        noncomm_ring
    _ = (L.Drb * L.GG * (L.ζi * L.ζi)) * L.Ar Y := by rw [show L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * L.Dr = L.Drb * L.GG * (L.ζi * L.ζi) from hA]
    _ = L.Drb * L.GG * (L.ζi * L.ζi * L.Ar Y) := by noncomm_ring

theorem ruleInv : RuleInv := by
  intro A _ _ r L Y

  have zb_p : ∀ l, Commute L.ζbi (L.p l) := fun l => (L.p_ζbi l).symm
  have zb_pb : ∀ l, Commute L.ζbi (L.pb l) := fun l => (L.pb_ζbi l).symm
  have z_p : ∀ l, Commute L.ζi (L.p l) := fun l => (L.p_ζi l).symm
  have z_pb : ∀ l, Commute L.ζi (L.pb l) := fun l => (L.pb_ζi l).symm
  have fc := fun {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) => L.inv_fcomm hx hy
  have zbAr : ∀ i j, Commute L.ζbi (L.Tprod Y i j) :=
    L.inv_comm_Tprod zb_p (fun l => fc L.inv_mem_ζbi (L.inv_mem_c l)) (fun l => fc L.inv_mem_ζbi (L.inv_mem_ci l)) Y
  have zbAv : ∀ i j, Commute L.ζbi (L.Tvprod Y i j) :=
    L.inv_comm_Tvprod zb_pb (fun l => fc L.inv_mem_ζbi (L.inv_mem_cb l)) (fun l => fc L.inv_mem_ζbi (L.inv_mem_cbi l)) Y
  have zAr : ∀ i j, Commute L.ζi (L.Tprod Y i j) :=
    L.inv_comm_Tprod z_p (fun l => fc L.inv_mem_ζi (L.inv_mem_c l)) (fun l => fc L.inv_mem_ζi (L.inv_mem_ci l)) Y
  have zAv : ∀ i j, Commute L.ζi (L.Tvprod Y i j) :=
    L.inv_comm_Tvprod z_pb (fun l => fc L.inv_mem_ζi (L.inv_mem_cb l)) (fun l => fc L.inv_mem_ζi (L.inv_mem_cbi l)) Y
  have zbDr : Commute L.ζbi L.Dr := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζbi (L.inv_mem_c l)
  have zbDrb : Commute L.ζbi L.Drb := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζbi (L.inv_mem_cb l)
  have zDr : Commute L.ζi L.Dr := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζi (L.inv_mem_c l)
  have zDrb : Commute L.ζi L.Drb := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζi (L.inv_mem_cb l)
  have zbGG : Commute L.ζbi L.GG := fc L.inv_mem_ζbi L.inv_mem_GG
  have zGG : Commute L.ζi L.GG := fc L.inv_mem_ζi L.inv_mem_GG
  have zb_l0 : Commute L.ζbi (L.l0 Y) := by
    simp only [LevelData.l0]
    exact ((show Commute L.ζbi L.nab from L.nab_ζbi.symm).neg_right).sub_right ((comm_alg _ _).mul_right
      ((fc L.inv_mem_ζbi L.inv_mem_ζb).mul_right (fc L.inv_mem_ζbi L.inv_mem_GGi)))
  have z_m0 : Commute L.ζi (L.m0 Y) := by
    simp only [LevelData.m0]
    exact ((show Commute L.ζi L.nabs from L.nabs_ζi.symm).neg_right).sub_right ((comm_alg _ _).mul_right
      ((fc L.inv_mem_ζi L.inv_mem_ζ).mul_right (fc L.inv_mem_ζi L.inv_mem_GGi)))
  have hm : L.m0 Y * L.ζbi = L.ζbi * L.m0 Y - L.ζbi * L.ζbi := by
    have hX : Commute L.ζbi (algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) :=
      (comm_alg _ _).mul_right ((fc L.inv_mem_ζbi L.inv_mem_ζ).mul_right (fc L.inv_mem_ζbi L.inv_mem_GGi))
    simp only [LevelData.m0]
    calc (-L.nabs - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) * L.ζbi
        = -(L.nabs * L.ζbi) - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi) * L.ζbi := by noncomm_ring
      _ = -(L.ζbi * L.nabs + L.ζbi * L.ζbi) - L.ζbi * (algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) := by
          rw [L.nabs_ζbi, hX.eq]
      _ = _ := by noncomm_ring
  have hl : L.l0 Y * L.ζi = L.ζi * L.l0 Y + L.ζi * L.ζi := by
    have hX : Commute L.ζi (algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) :=
      (comm_alg _ _).mul_right ((fc L.inv_mem_ζi L.inv_mem_ζb).mul_right (fc L.inv_mem_ζi L.inv_mem_GGi))
    simp only [LevelData.l0]
    calc (-L.nab - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) * L.ζi
        = -(L.nab * L.ζi) - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi) * L.ζi := by noncomm_ring
      _ = -(L.ζi * L.nab - L.ζi * L.ζi) - L.ζi * (algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) := by
          rw [L.nab_ζi, hX.eq]
      _ = _ := by noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (zbDr.mul_right (zbAr 0 0)).eq
  · exact ((zbDrb.mul_right zbGG).mul_right ((zb_l0.mul_right (zbAr 0 0)).add_right (zbAr 1 0))).eq
  · exact (zbDrb.mul_right (zbAv 0 0)).eq
  · rw [inv_hR_bar]
    have e1 : (L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi
        = (L.ζbi * L.m0 Y - L.ζbi * L.ζbi) * L.Avr Y + L.ζbi * L.Bvr Y := by
      have hA1 : Commute L.ζbi (L.Avr Y) := zbAv 0 0
      have hB1 : Commute L.ζbi (L.Bvr Y) := zbAv 1 0
      rw [add_mul, mul_assoc, ← hA1.eq, ← mul_assoc, hm, ← hB1.eq]
    have hDG : Commute L.ζbi (L.Dr * L.GG) := zbDr.mul_right zbGG
    simp only [LevelData.R0v]
    calc L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi - L.ζbi * (L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y))
        = L.Dr * L.GG * ((L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi) - (L.ζbi * (L.Dr * L.GG)) * (L.m0 Y * L.Avr Y + L.Bvr Y) := by
          noncomm_ring
      _ = L.Dr * L.GG * ((L.ζbi * L.m0 Y - L.ζbi * L.ζbi) * L.Avr Y + L.ζbi * L.Bvr Y) - (L.Dr * L.GG * L.ζbi) * (L.m0 Y * L.Avr Y + L.Bvr Y) := by
          rw [e1, hDG.eq]
      _ = _ := by noncomm_ring
  · exact (zDr.mul_right (zAr 0 0)).eq
  · exact (zDrb.mul_right (zAv 0 0)).eq
  · exact ((zDr.mul_right zGG).mul_right ((z_m0.mul_right (zAv 0 0)).add_right (zAv 1 0))).eq
  · rw [inv_hR_hol]
    have e1 : (L.l0 Y * L.Ar Y + L.Br Y) * L.ζi
        = (L.ζi * L.l0 Y + L.ζi * L.ζi) * L.Ar Y + L.ζi * L.Br Y := by
      have hA1 : Commute L.ζi (L.Ar Y) := zAr 0 0
      have hB1 : Commute L.ζi (L.Br Y) := zAr 1 0
      rw [add_mul, mul_assoc, ← hA1.eq, ← mul_assoc, hl, ← hB1.eq]
    have hDG : Commute L.ζi (L.Drb * L.GG) := zDrb.mul_right zGG
    simp only [LevelData.R0]
    calc L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y) * L.ζi - L.ζi * (L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y))
        = L.Drb * L.GG * ((L.l0 Y * L.Ar Y + L.Br Y) * L.ζi) - (L.ζi * (L.Drb * L.GG)) * (L.l0 Y * L.Ar Y + L.Br Y) := by
          noncomm_ring
      _ = L.Drb * L.GG * ((L.ζi * L.l0 Y + L.ζi * L.ζi) * L.Ar Y + L.ζi * L.Br Y) - (L.Drb * L.GG * L.ζi) * (L.l0 Y * L.Ar Y + L.Br Y) := by
          rw [e1, hDG.eq]
      _ = _ := by noncomm_ring

end Formalism.FourierDecayAlt.R.PInv

theorem Formalism.FourierDecayAlt.P.inverseCommutators : Formalism.FourierDecayAlt.R.RuleInv := Formalism.FourierDecayAlt.R.PInv.ruleInv
end

