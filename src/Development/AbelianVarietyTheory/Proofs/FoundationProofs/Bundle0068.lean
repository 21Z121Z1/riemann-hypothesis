import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitPolyOfPeriodicSlashFamilyConst
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.QConst

open Filter Topology

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private theorem natDegree_lt_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p.natDegree < w + 1 := by
  rcases eq_or_ne p 0 with rfl | h
  · simp
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem norm_eval_le_sum_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (x : ℂ) : ‖p.eval x‖ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j‖ * ‖x‖ ^ j := by
  rw [eval_eq_sum_range' (natDegree_lt_of_mem_degreeLT hp)]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [norm_mul, norm_pow]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem eq_C_of_eval_add_natCast_eq {Q : ℂ[X]} {n : ℕ} (hn : 0 < n)
    (hQ : ∀ x : ℂ, Q.eval (x + n) = Q.eval x) : Q = C (Q.coeff 0) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot : ∀ k : ℕ, IsRoot (Q - C (Q.eval 0)) ((k : ℂ) * n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : ((k + 1 : ℕ) : ℂ) * n = (k : ℂ) * n + n := by push_cast; ring
      simp only [IsRoot.def, eval_sub, eval_C] at ih ⊢
      rw [hk, hQ]
      exact ih
  have hinf : Set.Infinite {x | IsRoot (Q - C (Q.eval 0)) x} :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ) * n)
      (fun a b hab => by exact_mod_cast mul_right_cancel₀ hn' hab) hroot
  rw [coeff_zero_eq_eval_zero]
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem tendsto_exp_neg_mul_mul_add_pow_zero {c : ℝ} (hc : 0 < c) (b : ℝ) (m : ℕ) :
    Tendsto (fun y : ℝ => Real.exp (-c * y) * (b + y) ^ m) atTop (𝓝 0) := by
  have h1 := ((isLittleO_pow_exp_pos_mul_atTop m hc).comp_tendsto
    (tendsto_atTop_add_const_left atTop b tendsto_id)).tendsto_div_nhds_zero
  have h2 := h1.const_mul (Real.exp (c * b))
  rw [mul_zero] at h2
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply, id]
  rw [mul_add, Real.exp_add, neg_mul, Real.exp_neg]
  field_simp

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in

theorem _root_.GlobalTheory.HeckeFamilyMatrices.QConst.qconst : ∀ (w n : ℕ) (V : ℍ → ℂ[X]) (Q : ℂ[X]) (C' c : ℝ), 0 < n → 0 < c → Q ∈ degreeLT ℂ (w + 1) →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    Q = C (Q.coeff 0) := by
  intro w n V Q C' c hn hc hQ hV hper h
  have hT : _root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := by
    unfold _root_.GlobalTheory.HeckeFamilyMatrices.mat
    exact ModularGroup.coe_T_zpow _
  have htrans : ∀ (τ : ℍ) (x : ℂ),
      (V τ).eval x = (V (ModularGroup.T ^ (n : ℤ) • τ)).eval (x + n) := by
    intro τ x
    rw [← hper τ, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ x (hV _) (by rw [hT]; simp), hT]
    simp
  have hbound : ∀ τ : ℍ, 1 ≤ τ.im → ∀ b : ℝ, 1 + ‖(τ : ℂ)‖ ≤ b → ∀ x : ℂ,
      ‖(V τ - Q).eval x‖ ≤ C' * Real.exp (-c * τ.im) * b ^ w *
        ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j := by
    intro τ hτ b hb x
    have hC' : 0 ≤ C' := by
      have h0 := h τ hτ 0 (Nat.zero_le _)
      have : 0 < Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by positivity
      nlinarith [norm_nonneg ((V τ - Q).coeff 0)]
    rw [Finset.mul_sum]
    refine (norm_eval_le_sum_of_mem_degreeLT (Submodule.sub_mem _ (hV τ) hQ) x).trans
      (Finset.sum_le_sum fun j hj => ?_)
    have hj' : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact mul_le_mul_of_nonneg_right ((h τ hτ j hj').trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb w)
        (mul_nonneg hC' (Real.exp_pos _).le))) (by positivity)
  refine eq_C_of_eval_add_natCast_eq hn fun x => ?_
  set M : ℝ := ∑ j ∈ Finset.range (w + 1), ‖x + n‖ ^ j + ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j
  have hest : ∀ y : ℝ, 1 ≤ y → ‖Q.eval (x + n) - Q.eval x‖ ≤
      C' * M * (Real.exp (-c * y) * ((1 + n) + y) ^ w) := by
    intro y hy
    let τ : ℍ := ⟨(y : ℂ) * Complex.I, by simp; linarith⟩
    have hτim : τ.im = y := by simp [τ, UpperHalfPlane.im]
    have hτn : ‖(τ : ℂ)‖ = y := by
      simp [τ, abs_of_pos (show (0 : ℝ) < y by linarith)]
    have hτ'c : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = τ + n := by
      rw [ModularGroup.coe_T_zpow_smul_eq]
      simp
    have hτ'im : (ModularGroup.T ^ (n : ℤ) • τ).im = y := by
      rw [← hτim, ← UpperHalfPlane.coe_im, hτ'c, ← UpperHalfPlane.coe_im]
      simp
    have hτ'n : 1 + ‖((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ)‖ ≤ (1 + n) + y := by
      rw [hτ'c]
      have := norm_add_le (τ : ℂ) (n : ℂ)
      rw [hτn, Complex.norm_natCast] at this
      linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 := hbound τ (by rw [hτim]; exact hy) ((1 + n) + y) (by rw [hτn]; linarith) x
    have e2 := hbound _ (by rw [hτ'im]; exact hy) ((1 + n) + y) hτ'n (x + n)
    rw [hτim] at e1
    rw [hτ'im] at e2
    have hsplit : Q.eval (x + n) - Q.eval x =
        (V τ - Q).eval x - (V (ModularGroup.T ^ (n : ℤ) • τ) - Q).eval (x + n) := by
      simp only [eval_sub, htrans τ x]
      ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    simp only [M]
    ring
  have hlim := (tendsto_exp_neg_mul_mul_add_pow_zero hc (1 + n) w).const_mul (C' * M)
  rw [mul_zero] at hlim
  have hle : ‖Q.eval (x + n) - Q.eval x‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hest⟩)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

end GlobalTheory.HeckeFamilyMatrices.QConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDivSqrtLeFourExp
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem badBound_tail (eps C : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in Filter.atTop,
      612 * (x ^ C) ^ 3 * Real.exp (-(x ^ (eps / 6))) ≤ Real.exp (-(x ^ (eps / 7))) := by
  have hb : 0 < eps / 7 := by positivity
  have hab : 0 < eps / 6 - eps / 7 := by linarith
  have h612 : 0 ≤ Real.log 612 := Real.log_nonneg (by norm_num)
  set K : ℝ := 1 + Real.log 612 + 3 * |C| / (eps / 7) with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (K ^ (1 / (eps / 6 - eps / 7)))] with x hx1 hxK
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxb : 1 ≤ x ^ (eps / 7) := Real.one_le_rpow hx1 hb.le
  have hl : Real.log x ≤ x ^ (eps / 7) / (eps / 7) := Real.log_le_rpow_div hx0.le hb
  have hd : K ≤ x ^ (eps / 6 - eps / 7) := by
    calc K = (K ^ (1 / (eps / 6 - eps / 7))) ^ (eps / 6 - eps / 7) := by
          rw [← Real.rpow_mul hK0, one_div_mul_cancel hab.ne', Real.rpow_one]
      _ ≤ x ^ (eps / 6 - eps / 7) := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hxK hab.le
  have hsplit : x ^ (eps / 6) = x ^ (eps / 6 - eps / 7) * x ^ (eps / 7) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hpow : (x ^ C) ^ 3 = Real.exp (3 * (Real.log x * C)) := by
    rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]; norm_num
  rw [hpow, show (612 : ℝ) = Real.exp (Real.log 612) from (Real.exp_log (by norm_num)).symm,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hC1 : Real.log x * C ≤ Real.log x * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hlog
  have hC2 : Real.log x * |C| ≤ x ^ (eps / 7) / (eps / 7) * |C| :=
    mul_le_mul_of_nonneg_right hl (abs_nonneg C)
  have hKx : K * x ^ (eps / 7) ≤ x ^ (eps / 6) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hl612 : Real.log 612 ≤ Real.log 612 * x ^ (eps / 7) := le_mul_of_one_le_right h612 hxb
  have h3 : 3 * (Real.log x * C) ≤ 3 * |C| / (eps / 7) * x ^ (eps / 7) := by
    calc 3 * (Real.log x * C) ≤ 3 * (x ^ (eps / 7) / (eps / 7) * |C|) := by linarith
      _ = 3 * |C| / (eps / 7) * x ^ (eps / 7) := by ring
  have h4 : (1 + Real.log 612 + 3 * |C| / (eps / 7)) * x ^ (eps / 7) =
      x ^ (eps / 7) + Real.log 612 * x ^ (eps / 7) + 3 * |C| / (eps / 7) * x ^ (eps / 7) := by ring
  rw [hK, h4] at hKx
  linarith

theorem log_div_sqrt_le_four_exp {g u : ℝ} (hg : Real.exp (4 * u) ≤ g) :
    Real.log g / Real.sqrt g ≤ 4 * Real.exp (-u) := by
  have hg0 : 0 < g := lt_of_lt_of_le (Real.exp_pos _) hg
  set q := g ^ (1 / 4 : ℝ) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hg0 _
  have h1 : Real.log g ≤ g ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hg0.le (by norm_num)
  have hs : Real.sqrt g = q * q := by
    rw [hqdef, ← Real.rpow_add hg0, Real.sqrt_eq_rpow]; norm_num
  have hq : Real.exp u ≤ q := by
    have : Real.exp u = (Real.exp (4 * u)) ^ (1 / 4 : ℝ) := by
      rw [← Real.exp_mul]; ring_nf
    rw [this]; exact Real.rpow_le_rpow (Real.exp_pos _).le hg (by norm_num)
  have hone : 1 ≤ Real.exp (-u) * q := by
    calc (1 : ℝ) = Real.exp (-u) * Real.exp u := by rw [← Real.exp_add]; simp
      _ ≤ Real.exp (-u) * q := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
  rw [hs, div_le_iff₀ (by positivity)]
  have h1' : Real.log g ≤ 4 * q := by rw [← hqdef] at h1; linarith
  nlinarith [hq0, hone]

theorem badBound_numbers : ∀ eps C : ℝ, 0 < eps → eps ≤ 1 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (g f m N q : ℝ), Real.exp (8 * x ^ eps) ≤ g → x ^ (2 : ℝ) ≤ f → f ≤ x ^ C → 0 ≤ m → m ≤ x ^ C → x ^ eps ≤ N → N ≤ x ^ C → Real.exp (x ^ (eps / 6)) ≤ q → 100000 ≤ N ∧ 0 ≤ badBound g f m N q ∧ 6 * badBound g f m N q ≤ Real.exp (-(x ^ (eps / 7))) := by
  intro eps C he he1
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 (badBound_tail eps C he)
  refine ⟨max (max X1 8) (max (20 * |C| + 1) ((100000 : ℝ) ^ (1 / eps))), ?_⟩
  intro x hx g f m N q hg hf1 hf2 hm1 hm2 hN1 hN2 hq
  have hxX1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx8 : 8 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC : 20 * |C| + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxN : (100000 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx1' : 1 < x := by linarith
  have hNbig : 100000 ≤ N := by
    have e : (100000 : ℝ) = ((100000 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one]
    have h2 : ((100000 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps := Real.rpow_le_rpow (by positivity) hxN he.le
    linarith
  have hTail := hX1 x hxX1
  have hCe : eps ≤ C := (Real.rpow_le_rpow_left_iff hx1').1 (le_trans hN1 hN2)
  have hC0 : 0 ≤ C := by linarith
  set P := x ^ C with hP
  set E := Real.exp (-(x ^ (eps / 6))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hN0 : 0 < N := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hx1 hC0
  have hx2 : x ^ (2 : ℝ) = x * x := by rw [Real.rpow_two, sq]
  rw [hx2] at hf1
  have hf0 : 0 ≤ f := le_trans (by positivity) hf1
  have he6 : x ^ (eps / 6) ≤ x ^ eps := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have he6h : x ^ (eps / 6) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by rw [← Real.rpow_add hx0]; norm_num
  have hs0 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  have hsx : x ^ (1 / 2 : ℝ) ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hxe1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1 he.le
  have hg8 : Real.exp 8 ≤ g := le_trans (Real.exp_le_exp.2 (by linarith)) hg
  have hg2 : 2 ≤ g := by have := Real.add_one_le_exp 8; linarith
  have hg0 : 0 < g := by linarith
  have hEg : 1 ≤ E * g := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * g := mul_le_mul_of_nonneg_left (le_trans (Real.exp_le_exp.2 (by linarith)) hg) hE0.le
  have hginv : 1 / g ≤ E := by rw [div_le_iff₀ hg0]; linarith
  have hT2 : Real.log g / Real.sqrt g ≤ 4 * E := by
    have h := log_div_sqrt_le_four_exp (u := 2 * x ^ eps) (g := g)
      (by rw [show 4 * (2 * x ^ eps) = 8 * x ^ eps by ring]; exact hg)
    refine h.trans ?_
    rw [hE]
    gcongr
    linarith
  have hLg : 0 ≤ Real.log g / Real.sqrt g :=
    div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hq0 : 0 < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hEq : 1 ≤ E * q := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * q := mul_le_mul_of_nonneg_left hq hE0.le
  have hqinv : 1 / (4 * q) ≤ E / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hlogN : 1 + Real.log N ≤ N := by linarith [Real.log_le_sub_one_of_pos hN0]
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hT3b : (1 + Real.log N) / (g - 1) ≤ 2 * N * E := by
    rw [div_le_iff₀ (by linarith)]
    have h1 := mul_nonneg (mul_nonneg hN0.le hE0.le) (show 0 ≤ g - 2 by linarith)
    have h2 : N * 1 ≤ N * (E * g) := mul_le_mul_of_nonneg_left hEg hN0.le
    linarith
  have hT4 : (7 / 8 : ℝ) ^ f ≤ E := by
    rw [Real.rpow_def_of_pos (by norm_num), hE, Real.exp_le_exp]
    have hl78 : Real.log (7 / 8) ≤ -(1 / 8) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num); linarith
    have h1 : Real.log (7 / 8) * f ≤ -(1 / 8) * f := mul_le_mul_of_nonneg_right hl78 hf0
    have h2 : 8 * x ≤ x * x := mul_le_mul_of_nonneg_right hx8 hx0.le
    linarith
  have hT5 : Real.exp (-(f / (10 * Real.log N))) ≤ E := by
    have hlN0 : 0 < Real.log N := Real.log_pos (by linarith)
    rw [hE, Real.exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by linarith)]
    have hlN : Real.log N ≤ C * Real.log x := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log hN0 hN2
    have hlx : Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hx0.le (by norm_num)
    have h1 : x ^ (eps / 6) * (10 * Real.log N) ≤
        x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) := by
      apply mul_le_mul he6h _ (by linarith) hs0
      have : C * Real.log x ≤ C * (x ^ (1 / 2 : ℝ) / (1 / 2)) := mul_le_mul_of_nonneg_left hlx hC0
      linarith
    have h2 : x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) = 20 * C * x := by
      calc x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2))))
          = 20 * C * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
        _ = 20 * C * x := by rw [hsq]
    have h3 : 20 * C * x ≤ x * x := by
      have : 20 * C ≤ x := by have := le_abs_self C; linarith
      exact mul_le_mul_of_nonneg_right this hx0.le
    linarith
  have hgm1 : 0 < g - 1 := by linarith
  unfold badBound
  refine ⟨hNbig, ?_, ?_⟩
  · have t1 : 0 ≤ 3 * f / g := div_nonneg (by linarith) hg0.le
    have t2 : 0 ≤ 23 * f * Real.log g / Real.sqrt g :=
      div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (Real.sqrt_nonneg _)
    have t3 : 0 ≤ 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) :=
      mul_nonneg (mul_nonneg (by linarith) hm1)
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
    have t4 : 0 ≤ N / 2 * (7 / 8 : ℝ) ^ f := mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
    have t5 : 0 ≤ Real.exp (-(f / (10 * Real.log N))) := (Real.exp_pos _).le
    linarith
  · have b1 : 3 * f / g ≤ 3 * P * E := by
      calc 3 * f / g = 3 * f * (1 / g) := by ring
        _ ≤ 3 * P * E := mul_le_mul (by linarith) hginv (div_nonneg zero_le_one hg0.le) (by linarith)
    have b2 : 23 * f * Real.log g / Real.sqrt g ≤ 92 * P * E := by
      calc 23 * f * Real.log g / Real.sqrt g = 23 * f * (Real.log g / Real.sqrt g) := by ring
        _ ≤ 23 * P * (4 * E) := mul_le_mul (by linarith) hT2 hLg (by linarith)
        _ = 92 * P * E := by ring
    have b3 : 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) ≤ 2 * P * P * (E / 4 + 2 * P * E) := by
      have hfm : 2 * f * m ≤ 2 * P * P := mul_le_mul (by linarith) hm2 hm1 (by linarith)
      have hsum : 1 / (4 * q) + (1 + Real.log N) / (g - 1) ≤ E / 4 + 2 * P * E := by
        have : 2 * N * E ≤ 2 * P * E := mul_le_mul_of_nonneg_right (by linarith) hE0.le
        linarith
      exact mul_le_mul hfm hsum
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
        (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    have b4 : N / 2 * (7 / 8 : ℝ) ^ f ≤ P / 2 * E :=
      mul_le_mul (by linarith) hT4 (Real.rpow_nonneg (by norm_num) _) (by linarith)
    have hP0 : 0 ≤ P := by linarith
    have hPP : P ≤ P * P := le_mul_of_one_le_right hP0 hP1
    have hPPP : P * P ≤ P ^ 3 := by
      rw [show P ^ 3 = P * P * P by ring]
      exact le_mul_of_one_le_right (mul_nonneg hP0 hP0) hP1
    have c1 : P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right (hPP.trans hPPP) hE0.le
    have c2 : P * P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right hPPP hE0.le
    have c3 : E ≤ P ^ 3 * E := le_mul_of_one_le_left hE0.le (hP1.trans (hPP.trans hPPP))
    have hnn : 0 ≤ P ^ 3 * E := mul_nonneg (pow_nonneg hP0 3) hE0.le
    linarith

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTowerUnionAdjoinIntegralClosureIffStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_towerUnionAdjoinIntegralClosure_iff : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (s : (integralClosure (O0 p) Ω)), s ∈ towerAlg T ↔ (s : Ω) ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  first | exact @GlobalTheory.towerAlg_mem_iff | exact GlobalTheory.towerAlg_mem_iff | (intros; apply GlobalTheory.towerAlg_mem_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGamma1InterGamma0ExtQExpansionCoeff
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem eq_of_coef_eq : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ f g : ModularForm (GlobalTheory.Hk.lev N l) k,
    (∀ n, GlobalTheory.Hk.coef ⇑f n = GlobalTheory.Hk.coef ⇑g n) → f = g := by
  intro N l k hN f g h
  ext τ
  have hf := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN f τ
  have hg := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN g τ
  simp_rw [h] at hf
  exact hf.unique hg

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularLawOfSAndTStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modular_law_of_s_and_t : ∀ (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ), (∀ x γ, P x → P (act x γ)) → (∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ) → (∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) → ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.modular_law_of_generators | exact GlobalTheory.Sieg.modular_law_of_generators | (intros; apply GlobalTheory.Sieg.modular_law_of_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrder
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_top_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 →
    (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ hv σ hσF l hl hσl ⟨y, hy⟩ r hr
  obtain ⟨d, hdF, _hd0, hrx, hx1⟩ :=
    GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp F hF hp0 hp1 r hr (σ • y - y) (sub_ne_zero.mpr hy)
  set x := (σ • y - y) * d ^ p with hxdef
  refine ⟨x, Subfield.mem_top x, hx1, ?_⟩
  by_contra hle
  push_neg at hle
  have hfix : ∀ j : ℕ, (σ ^ j) • d = d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hσF d hdF, ih]
  have hterm : ∀ j : ℕ, (σ ^ j) • x = ((σ ^ (j + 1)) • y - (σ ^ j) • y) * d ^ p := by
    intro j
    rw [hxdef, smul_mul', smul_pow', hfix, smul_sub, pow_succ, mul_smul]
  have hsum : ∑ j ∈ Finset.range l, (σ ^ j) • x = 0 := by
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_range_sub (fun j => (σ ^ j) • y), hσl, one_smul, pow_zero,
      one_smul, sub_self, zero_mul]
  have hstep : ∀ j : ℕ, v ((σ ^ j) • x - x) ≤ r := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (σ ^ (j + 1)) • x - x = σ • ((σ ^ j) • x - x) + (σ • x - x) := by
        rw [smul_sub, pow_succ', mul_smul]; ring
      rw [e]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hle)
      rw [hv]; exact ih
  have hlx : (l : L) * x = ∑ j ∈ Finset.range l, (x - (σ ^ j) • x) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : v ((l : L) * x) ≤ r := by
    rw [hlx]
    apply Valuation.map_sum_le
    intro j _
    rw [← Valuation.map_neg, neg_sub]
    exact hstep j
  rw [map_mul, GlobalTheory.T.valuation_natCast_eq_one_of_coprime' L v p l hp1 hl, one_mul] at h1
  exact absurd (lt_of_lt_of_le hrx h1) (lt_irrefl _)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusOldformTraceToGammaZeroStatement
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nebentypus_oldformTraceToGammaOne : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → l.Prime → ChiInv k N (N * l) χ G → ChiInv k N N χ (trOld k N l a b h G) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_trOld | exact GlobalTheory.HeckeFamilyMatrices.chiInv_trOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_trOld <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashIntDiagTwoMatrixLevelRaiseStatement
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise : ∀ (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ), 0 < l → ChiInv k N N χ B → ChiInv k N (N * l) χ (B ∣[k] toGL (dg l 1)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | exact GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashOldformLevelRaisingMatrixStatement
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nebentypus_slash_oldformLevelRaisingMatrix : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 → ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G → ChiInv k N (N * l) χ (G ∣[k] toGL (wOld N l a b)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld | exact GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEvalSmulMulImRpowPolyDegreeSlashStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eval_smul_mul_im_rpow_polyDegreeSlash : ∀ (w : ℕ) (σ : SL(2, ℤ)) (P : ℂ[X]) (τ : ℍ), P ∈ degreeLT ℂ (w + 1) → ‖P.eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-(w : ℝ) / 2) = ‖(slP w (mat σ) P).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow | exact GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow | (intros; apply GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelEqZeroIffLatticeStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice : ∀ (τ : ℍ) (z : ℂ), th z τ = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) * (τ : ℂ) + n := by
  first | exact @GlobalTheory.ThZero.th_eq_zero_iff | exact GlobalTheory.ThZero.th_eq_zero_iff | (intros; apply GlobalTheory.ThZero.th_eq_zero_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformLevelRaisingSlashSlashNebentypusStatement
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 → ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G → (G ∣[k] toGL (wOld N l a b)) ∣[k] toGL (wOld N l a b) = ((l : ℂ) ^ (k - 2) * χ (b : ZMod N)) • G := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash | exact GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash | (intros; apply GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash <;> assumption)
end

