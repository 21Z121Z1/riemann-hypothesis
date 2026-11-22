import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowThinSizeGe
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_thinSize_ge : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.Cw ≤ L.sc.w'' D.R.n ∧ L.sc.b ^ C.P.cw ≤ L.sc.w'' D.R.n)) := by
  intro eps he he' C hC
  obtain ⟨x1, h1⟩ := GlobalTheory.scale_poly_comparison eps (5 * |(C.P.Cw : ℝ)|) (1 / 10) he (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 16, fun D L hs hx hV => ?_⟩⟩⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx16 : (16 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hone : (1 : ℝ) ≤ L.sc.x := by linarith
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  obtain ⟨⟨hn1, -⟩, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  rw [hs] at hn1 hk1 hk2
  have h2 : (2 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow (by norm_num) hx16 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have e : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [e] at h
  have hup : ∀ a b : ℝ, 1 / 4 + a ≤ b → 2 * L.sc.x ^ a ≤ L.sc.x ^ b := fun a b hab => by
    calc 2 * L.sc.x ^ a ≤ L.sc.x ^ ((1 : ℝ) / 4) * L.sc.x ^ a :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _)
      _ = L.sc.x ^ (1 / 4 + a) := (Real.rpow_add hx0 _ _).symm
      _ ≤ L.sc.x ^ b := Real.rpow_le_rpow_of_exponent_le hone hab
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := hV.ranks.n_le'.trans (hup _ _ (by norm_num))
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := hk2.trans (hup _ _ (by linarith))
  have hn0 : (1 : ℝ) ≤ D.R.n := (Real.one_le_rpow hone (by linarith)).trans hn1
  have hk0 : (1 : ℝ) ≤ D.R.k := (Real.one_le_rpow hone (by linarith)).trans hk1
  obtain ⟨-, -, -, -, -, hw, -⟩ := h1 L.sc hs hx1
  obtain ⟨hw, -, -⟩ := hw D.R.n (by exact_mod_cast hn0) hn3
  have hb1 : (1 : ℝ) ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hA : (1 : ℝ) ≤ L.sc.b ^ ((1 : ℝ) - 1 / 10) := Real.one_le_rpow hb1 (by norm_num)
  have hB : (1 : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := Real.one_le_rpow hone (by positivity)
  have hcw : C.P.cw = 9 / 10 := hC.2.2.2.2.1
  have hkC : (D.R.k : ℝ) ^ (C.P.Cw : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := by
    calc (D.R.k : ℝ) ^ (C.P.Cw : ℝ) ≤ (D.R.k : ℝ) ^ |(C.P.Cw : ℝ)| :=
          Real.rpow_le_rpow_of_exponent_le hk0 (le_abs_self _)
      _ ≤ (L.sc.x ^ (5 : ℝ)) ^ |(C.P.Cw : ℝ)| :=
          Real.rpow_le_rpow (by linarith) hk5 (abs_nonneg _)
      _ = L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := (Real.rpow_mul hx0.le _ _).symm
  refine ⟨?_, ?_⟩
  · refine hkC.trans (le_trans ?_ hw)
    exact le_mul_of_one_le_left (by linarith) hA
  · rw [hcw, show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num]
    exact le_trans (le_mul_of_one_le_right (by linarith) hB) hw

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTopsBandBottoms
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bandWidth_real_inequality_le_inv_sq {x e n δ k La A c : ℝ} (hx : 1 < x) (hδ : δ ≤ 1)
    (hn : n ≤ 2 * x ^ (2 + 8 * e)) (hn0 : 0 ≤ n) (hk : x ^ (9 / 2 + 10 * e) ≤ k) (hLa0 : 0 ≤ La)
    (hLa : La ≤ A * Real.log x ^ 2 * x ^ e) (hc : 0 ≤ c)
    (h1 : 32 * A * x ^ (2 + 10 * e) * Real.log x ^ 2 ≤ x ^ (5 / 2 + 10 * e))
    (h2 : 2 * c * A * x ^ e * Real.log x ^ 3 ≤ x ^ (5 / 2 + 10 * e)) :
    4 * (2 * n * δ) * x ^ e * La / k + c * Real.log x * La / k ≤ x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hk0 : 0 < k := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hk
  have he0 : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (2 + 10 * e) = x ^ (2 + 8 * e) * x ^ e * x ^ e := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ (5 / 2 + 10 * e) = x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hnδ : n * δ ≤ 2 * x ^ (2 + 8 * e) := (mul_le_of_le_one_right hn0 hδ).trans hn
  have t1 : 4 * (2 * n * δ) * x ^ e * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc 4 * (2 * n * δ) * x ^ e * La = 8 * (n * δ) * x ^ e * La := by ring
      _ ≤ 8 * (2 * x ^ (2 + 8 * e)) * x ^ e * (A * Real.log x ^ 2 * x ^ e) := by
          gcongr
      _ = (32 * A * x ^ (2 + 10 * e) * Real.log x ^ 2) / 2 := by rw [e1]; ring
      _ ≤ _ := by linarith
  have t2 : c * Real.log x * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc c * Real.log x * La ≤ c * Real.log x * (A * Real.log x ^ 2 * x ^ e) := by gcongr
      _ = (2 * c * A * x ^ e * Real.log x ^ 3) / 2 := by ring
      _ ≤ _ := by linarith
  rw [← add_div, div_le_iff₀ hk0]
  have t3 : x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) ≤ x ^ (-2 : ℝ) * k :=
    mul_le_mul_of_nonneg_left hk (Real.rpow_pos_of_pos hx0 _).le
  linarith

theorem szRow_tops_band_bottoms :
    SzRow (fun C D L => ((D.host.TT.card : ℝ) ≤ Nstar L) ∧ (rhoP L C.P.Crho ≤ L.sc.x ^ (-2 : ℝ)) ∧
      (∀ t, (L.bT t : ℝ) ≤ L.sc.b' + Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k)) := by
  intro eps h0 h1 C hC
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hrho : 1 ≤ C.P.Crho := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨CN, x1, hx1⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  obtain ⟨x2, hx2⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (2 + 10 * eps) (5 / 2 + 10 * eps) (32 * (2 * C.GK.La * CN ^ 2)) 2 (by linarith)
  obtain ⟨x3, hx3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (5 / 2 + 10 * eps) (2 * C.P.Crho * (2 * C.GK.La * CN ^ 2)) 3 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 (max x2 x3), fun D L he hx V => ⟨?_, ?_, ?_⟩⟩⟩⟩
  · have := V.host.2.1.2
    unfold LevelStarExponents.Nstar
    linarith
  · have hx1' : x1 ≤ L.sc.x := (le_max_left _ _).trans hx
    have hx2' : x2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
    have hx3' : x3 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
    obtain ⟨-, -, hK⟩ := hx1 L.sc he hx1'
    obtain ⟨hlo, hup⟩ := hK C.GK hLa
    have hxp : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
    have a2 := hx2 _ hx2'
    have a3 := hx3 _ hx3'
    rw [← he] at a2 a3
    unfold rhoP LevelStarExponents.Nstar
    rw [V.La_eq]
    have hδ : L.sc.delta1 ≤ L.sc.x ^ (-(L.sc.eps / 100)) :=
      Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by have := L.sc.eps_pos; linarith)
    have hδ0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hxp.le _
    have hn : (D.R.n : ℝ) * L.sc.delta1 ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) := by
      calc (D.R.n : ℝ) * L.sc.delta1
          ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-(L.sc.eps / 100)) :=
            mul_le_mul V.ranks.n_le hδ hδ0 (by positivity)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hxp]; congr 2; ring
    have key := bandWidth_real_inequality_le_inv_sq (A := 2 * C.GK.La * CN ^ 2) (c := C.P.Crho) L.sc.one_lt_alt (le_refl (1 : ℝ))
      hn (mul_nonneg (Nat.cast_nonneg _) hδ0) V.ranks.2.2.1.1 ((Real.rpow_pos_of_pos hxp _).le.trans hlo)
      (hup.trans (le_of_eq (by ring))) (by linarith) a2 a3
    rw [mul_one, ← mul_assoc 2] at key
    exact key
  · exact V.bT_le

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowWindowLength
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem lA_le_pow_seven {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (hV : Val C cD ch L) :
    lA L ≤ L.sc.x ^ (7 : ℝ) := by
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hk : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ) := by
    have h1 := hV.ranks.2.2.1.2
    have h2 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    exact_mod_cast this
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact hV.host.2.2.1
  have hd' : L.sc.x ^ (-1 : ℝ) ≤ L.de2 :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) hd
  have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hdp := L.thickDensity_pos
  unfold lA
  rw [div_le_iff₀ (by positivity)]
  have e7 : L.sc.x ^ (7 : ℝ) * L.sc.x ^ (-1 : ℝ) = L.sc.x ^ (5 : ℝ) * L.sc.x ^ (1 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  calc (D.R.k : ℝ) * L.sc.x ^ L.sc.eps ≤ (2 * L.sc.x ^ (5 : ℝ)) * L.sc.x ^ (1 : ℝ) := by gcongr
    _ = L.sc.x ^ (7 : ℝ) * (2 * L.sc.x ^ (-1 : ℝ)) := by
        rw [mul_assoc, ← e7]; ring
    _ ≤ L.sc.x ^ (7 : ℝ) * ((D.R.m : ℝ) * L.de2) := by gcongr

theorem nN_div_m_le {C : FC} (hCt : C.Ct = 401) {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (hV : Val C cD ch L) :
    (D.R.n : ℝ) * D.R.N D.R.m / D.R.m ≤ 4 * L.sc.x ^ (404 : ℝ) := by
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hn : (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (3 : ℝ) := by
    have h1 := hV.ranks.n_le'
    have h2 : L.sc.x ^ ((9 : ℝ) / 4) ≤ L.sc.x ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    linarith
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ (401 : ℝ) := by
    have h := L.t_win.2
    rwa [hV.Ct_eq, hCt] at h
  have hm2 := D.R.two_le_m
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hN : D.R.N D.R.m ≤ 2 * D.R.t * D.R.m := by
    have h := D.R.rank_add_five_le
    have h1 : D.R.k + 1 ≤ D.R.t := by omega
    unfold Ranks.N
    nlinarith
  have hN' : (D.R.N D.R.m : ℝ) ≤ 2 * D.R.t * D.R.m := by exact_mod_cast hN
  rw [div_le_iff₀ hm]
  have e : L.sc.x ^ (404 : ℝ) = L.sc.x ^ (3 : ℝ) * L.sc.x ^ (401 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  calc (D.R.n : ℝ) * D.R.N D.R.m ≤ (2 * L.sc.x ^ (3 : ℝ)) * (2 * D.R.t * D.R.m) := by gcongr
    _ ≤ (2 * L.sc.x ^ (3 : ℝ)) * (2 * L.sc.x ^ (401 : ℝ) * D.R.m) := by gcongr
    _ = 4 * L.sc.x ^ (404 : ℝ) * D.R.m := by rw [e]; ring

theorem szRow_windowLength : SzRow (fun C D L => (∀ l : ℕ, 11 ≤ l → ∃ j : ℕ, lA L ≤ ((l : ℝ) - 1) ^ j ∧ 2 * j + 2 ≤ D.host.Lw) ∧ ((D.host.Lw : ℝ) ≤ C.P.CLw * Real.log L.sc.x) ∧ ((L.j0 : ℝ) ≤ C.P.Cj0 * Real.log L.sc.x)) := by
  intro eps h0 h1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (60 / eps + 34), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog : 60 / eps + 34 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hq : 0 < 60 / eps := by positivity
  have hLw : D.host.Lw = Lwv L.sc := hV.host.2.2.2.2.2.1
  have hCt : C.Ct = 401 := by
    have h := hC.1
    unfold FC.Fixed at h
    tauto
  refine ⟨fun l hl => ⟨⌈7 * Real.log L.sc.x⌉₊, ?_, ?_⟩, ?_, ?_⟩
  · have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
    have he1 : Real.exp 1 ≤ (l : ℝ) - 1 := by
      have := Real.exp_one_lt_d9
      linarith
    calc lA L ≤ L.sc.x ^ (7 : ℝ) := lA_le_pow_seven hV
      _ = Real.exp (7 * Real.log L.sc.x) := by rw [Real.rpow_def_of_pos hx0, mul_comm]
      _ ≤ Real.exp ((⌈7 * Real.log L.sc.x⌉₊ : ℕ) * 1) := by
          rw [mul_one]; exact Real.exp_le_exp.2 (Nat.le_ceil _)
      _ = Real.exp 1 ^ ⌈7 * Real.log L.sc.x⌉₊ := Real.exp_nat_mul _ _
      _ ≤ ((l : ℝ) - 1) ^ ⌈7 * Real.log L.sc.x⌉₊ := by gcongr
  · have : ⌈7 * Real.log L.sc.x⌉₊ ≤ ⌈(405 : ℝ) * Real.log L.sc.x⌉₊ := Nat.ceil_mono (by linarith)
    rw [hLw, Lwv]; omega
  · rw [hLw, hC.2.2.1, Lwv, he]
    have a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1 := Nat.ceil_lt_add_one (by positivity)
    have a3 : 60 / eps = 2 * (30 / eps) := by ring
    push_cast
    linarith
  · rw [hV.logFiveDepth_eq, hC.2.2.2.1]
    have hb := nN_div_m_le hCt hV
    have hm2 := D.R.two_le_m
    have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
    have hn : (0 : ℝ) < D.R.n := by
      have : 0 < D.R.n := by unfold Ranks.n; positivity
      exact_mod_cast this
    have hN : (0 : ℝ) < D.R.N D.R.m := by
      have h := D.R.m_add_three_le_k
      have : 0 < D.R.N D.R.m := by unfold Ranks.N; omega
      exact_mod_cast this
    have hy : 0 < (D.R.n : ℝ) * D.R.N D.R.m / D.R.m := by positivity
    have l4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have l2 := Real.log_two_gt_d9
    have l2' := Real.log_two_lt_d9
    have l5 : Real.log 4 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
    have hl : Real.log ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ Real.log 4 + 404 * Real.log L.sc.x := by
      refine (Real.log_le_log hy hb).trans (le_of_eq ?_)
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
    have hlb : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ 400 * Real.log L.sc.x := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    have a1 : (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 400 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : ((⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ : ℕ) : ℝ) ≤ (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) := by
      exact_mod_cast Nat.ceil_mono hlb
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupleChainSharpColumnValuationOfTwisted
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwSharp

variable {D : D7} {u : D.what₂.Word}

theorem weight_eq (X Y : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j)) :
    (X.fm.lam j τ).w a = (Y.fm.lam j τ).w a := by
  have h := (X.fm.lam_eq j hj τ a).trans (Y.fm.lam_eq j hj τ a).symm
  exact_mod_cast h

theorem weightSup_eq (X Y : Ch D u) (τ : D.what₂.Tau) : TauWeight X τ = TauWeight Y τ := by
  unfold TauWeight
  refine Finset.sup_congr rfl fun i hi => Finset.sup_congr rfl fun a _ => ?_
  rw [weight_eq X Y i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) τ a]

theorem exponent_eq (X Y : Ch D u) : ETpi X = ETpi Y := by
  unfold ETpi Wt; simp only [weightSup_eq X Y]

theorem tupleChainSharpColumnValuation_of_twisted : ∀ (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup),
    Step0Tie Tw u μ → Conclusion5Sharp (tw Tw u μ) → TupleChainSharpColumnValuation Tw u μ := by
  intro D u Tw μ hT h w hw c n hc hn x hx
  have hw' : OverT (tw Tw u μ) w := hw.trans (Tw.A_T u μ).symm
  have hown : ET (own D u) w = EatT D u w := rfl
  have hE : ET (tw Tw u μ) w = EatT D u w := by
    rw [← hown]; unfold ET
    rw [exponent_eq (tw Tw u μ) (own D u)]
    show (if (Tw.fm u μ).seenP w = true then _ else _) = _
    rw [(hT w hw).1]
  obtain ⟨y, hy, e⟩ := h w hw' c n hc (hE ▸ hn) (Tw.e0 u μ x) ((hT w hw).2 x hx)
  refine ⟨y, hy, e.trans ?_⟩
  show _ • (D.chTw u μ).col ((Tw.fm u μ).emb 0 (Tw.e0 u μ x)) = _
  rw [Tw.embed_mul_block_embedding]

end GlobalTheory.LvT.TwSharp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValBOfInc
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem valB_of_inc : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT) (v : X.A.vT) (p p₁ : M.Pt), X.fm.seenP w = true → v ∈ V → M.Inc v p p₁ → Co.valB w V p₁ = Co.valB w (V.erase v) p := by
  intro D u X i M Co w V v p p₁ hw hv hI
  obtain ⟨-, hoff, x, -, -, hk, -⟩ := hI
  have key : ∀ v', (if X.fm.seenP w = true ∧ v' ∉ V then ((p₁.2 v').1.L : Set _) else (p₁.2 v').ker) =
      (if X.fm.seenP w = true ∧ v' ∉ V.erase v then ((p.2 v').1.L : Set _) else (p.2 v').ker) := by
    intro v'
    by_cases h : v' = v
    · subst h
      rw [if_neg (fun h => h.2 hv), if_pos ⟨hw, Finset.notMem_erase _ _⟩, hk]
    · rw [hoff v' h]
      have : v' ∈ V.erase v ↔ v' ∈ V := by simp [h]
      simp only [this]
  unfold PtModel.Coord.valB
  simp only [key]

end GlobalTheory.LvT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WtBoundsOfNonneg
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

variable {D : D7} {u : D.what₂.Word}

theorem natAbs_lamT_le_Wt (X : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j))
    (ha : ¬ (a.1 = 0 ∧ τ ∈ tops D)) : ((PtModel.lamT X j τ).w a).natAbs ≤ Wt X τ := by
  unfold Wt TauWeight
  refine le_trans ?_ (Finset.le_sup (f := fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  refine le_trans ?_ (Finset.le_sup (f := fun a : Fin (D.R.N j) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam j τ).w a - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs) (Finset.mem_univ a))
  rw [if_neg ha]
  exact le_rfl

theorem lamT_last (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N (i + 1)))
    (ha : a.1 = D.R.N (i + 1) - 1) : (PtModel.lamT X (i + 1) τ).w a = -X.C.sDiv i τ := by
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  have hm : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + D.R.t + 1 := by ring
  have ha' : a.1 = D.R.k + (D.R.t + i * (D.R.t + 1)) := by omega
  have hk : ¬ a.1 < D.R.k := by omega
  have hq : (a.1 - D.R.k) / (D.R.t + 1) = i := by
    rw [ha', Nat.add_sub_cancel_left, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
      Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h1 := X.fm.lam_eq (i + 1) hi τ a
  rw [dif_neg hk] at h1
  simp only [hq] at h1
  have h2 := X.C.sDiv_eq i hi τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have h3 : (i + 1) * (D.R.t + 1) / 2 = (i + 1) * (c + 1) := by
    have : (i + 1) * (D.R.t + 1) = 2 * ((i + 1) * (c + 1)) := by rw [hc]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcq : (D.R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  change (X.fm.lam (i + 1) τ).w a - (((i + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) = _
  rw [h3]
  have : (((X.fm.lam (i + 1) τ).w a - (((i + 1) * (c + 1) : ℕ) : ℤ) : ℤ) : ℚ) = ((-X.C.sDiv i τ : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  exact_mod_cast this

theorem wtBounds_of_nonneg : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u), (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) →
    (∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ) → WtBounds X := by
  intro D u X hb hs
  refine ⟨hb, fun i hi τ => ?_⟩
  have hpos := D.R.N_pos (i + 1)
  have hlast := lamT_last X i hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ rfl
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  refine ⟨hs i hi τ, ?_, ?_, fun hτ => ?_⟩
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ (fun h => by
      have := h.1
      simp only at this
      omega)
    rw [hlast] at h
    omega
  · unfold DomWeight.detShift
    rw [dif_pos hpos]
    exact hlast
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨0, hpos⟩ (fun h => hτ h.2)
    omega

end GlobalTheory.LvT
end

