import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeanSquareNormalizedThetaTwoTorsion
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCondQdPde
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_cond_qd_pde : SzRow (fun _ _ L => SizeCond L ∧ SizeQD L ∧ SizePde L) := by
  intro eps he he' C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, h1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  obtain ⟨x2, h2⟩ := hostBounds eps C.P.Cpde he he' hC8
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 60150 72 (1 / 2) 2
    (by positivity) (by linarith) (by norm_num)
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 100) 2 0 (by positivity)
  obtain ⟨x6, h6⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) (eps / 5 + eps / 100) 1 2 (by linarith)
  obtain ⟨x7, h7⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) eps (2 * C.P.Cpde) 2 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ =>
    ⟨max (max (max x1 x2) (max x3 x4)) (max (max (Real.exp C.P.Cpde) x6) (max x7 (Real.exp 1))), ?_⟩⟩⟩
  intro D L hse hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, ⟨hx5, hx6⟩, hx7, hx8⟩ := hx
  have hr := h1 L.sc D.R hse hx1 hV.ranks
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ (401 : ℝ) := hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨q1, q2, d1, d2, hN, r1, r2, -, p1, p2⟩ := h2 L.sc D.R D.host hse hx2 hV.ranks hV.host
  have k3 := h3 _ hx3
  have k4 := h4 _ hx4
  have k6 := h6 _ hx6
  have k7 := h7 _ hx7
  subst hse
  have hxpos : 0 < L.sc.x := (Real.exp_pos 1).trans_le hx8
  have hlog : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hxpos).mpr hx8
  have hlog2 : 1 ≤ Real.log L.sc.x ^ 2 := one_le_pow₀ hlog
  have hmul : L.sc.x ^ (L.sc.eps / 5) ≤ L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_nonneg hxpos.le _) hlog2
  simp only [pow_zero, mul_one, one_mul] at k6
  have hx1' : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hez : L.sc.eps / C.P.Cpde ≤ L.sc.ez := hostBounds_ez hV.host
  have hez0 : 0 ≤ L.sc.ez := le_trans (by positivity) hez
  have k40 : 2 ≤ L.sc.x ^ (L.sc.ez / 100) := by
    simp only [pow_zero, mul_one, Real.rpow_zero] at k4
    exact k4.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith))
  have k5 : 2 * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) ≤ L.sc.x ^ (L.sc.ez / 5) := by
    have e : L.sc.x ^ (L.sc.ez / 5) = L.sc.x ^ (L.sc.ez / 100) * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right k40 (Real.rpow_nonneg hxpos.le _)
  have k41 : L.sc.x ^ (L.sc.ez / 6) ≤ L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hmz : L.sc.x ^ (L.sc.ez / 5) ≤ L.sc.x ^ (L.sc.ez / 5) * (Real.log L.sc.x / L.sc.J) ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_nonneg hxpos.le _)
      (one_le_pow₀ (hostBounds_one_le_log_div hV.host hx5))
  refine ⟨?_, ?_, ?_⟩
  · unfold SizeCond szCond Scale.b Scale.L
    have hA : ((D.host.QS : ℝ) * D.host.q * D.host.d) ≤
        Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) :=
      (Real.le_exp_log _).trans (Real.exp_le_exp.mpr hN)
    have hB : (D.R.t : ℝ) ≤ Real.exp (Real.log L.sc.x * 401) := by
      rwa [Real.rpow_def_of_pos hxpos] at ht
    rw [← Real.exp_half]
    calc ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 * (D.R.t : ℝ) ^ 150
        ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) ^ 36 *
            Real.exp (Real.log L.sc.x * 401) ^ 150 := by gcongr
      _ = Real.exp (((36 : ℕ) : ℝ) * (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) +
            ((150 : ℕ) : ℝ) * (Real.log L.sc.x * 401)) := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
      _ ≤ Real.exp (L.sc.x ^ L.sc.eps / 2) := by
          apply Real.exp_le_exp.mpr
          push_cast
          linarith
  · unfold SizeQD szTh
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, hV.dlog, r1, r2⟩
  · unfold SizePde Scale.L
    exact ⟨by linarith, by linarith⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowDelTOGap
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_Del_TO_gap : SzRow (fun C D L => ((((TOv L.sc : ℕ) : ℝ)) ^ 2 ≤ ((D.s.Del : ℚ) : ℝ)) ∧ ((((TOv L.sc : ℕ) : ℝ) + (D.R.f * D.R.r.choose 2 : ℕ) + 2) * (((TOv L.sc : ℕ) : ℝ) + (D.R.f * D.R.r.choose 2 : ℕ) + 2 + 2 * (D.R.N D.R.m : ℝ)) ≤ ((D.s.Del : ℚ) : ℝ))) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  refine ⟨805, fun cD hcD => ⟨0, fun ch _ => ⟨max x0 35, fun D L hs hx hV => ?_⟩⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hDY, -, -, -, -, hN, -⟩ :=
    hx0 L.sc D.R hs (le_trans (le_max_left _ _) hx) hV.ranks
  have hx35 : (35 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ L.sc.x := by linarith
  have hxp : (0 : ℝ) < L.sc.x := by linarith
  set y : ℝ := L.sc.x ^ (402 : ℝ) with hy
  have hy1 : (1 : ℝ) ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have h377 : L.sc.x ^ (377 : ℝ) ≤ y := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h12 : L.sc.x ^ (12 : ℝ) ≤ y := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hT : ((TOv L.sc : ℕ) : ℝ) ≤ y + 1 := by
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hxp.le (377 : ℝ))
    unfold TOv
    linarith
  have hDel : 35 * y ^ 2 ≤ ((D.s.Del : ℚ) : ℝ) := by
    rw [hV.Del_eq]
    have h1 : L.sc.x ^ cD ≤ ((Delv L.sc cD : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : L.sc.x ^ (805 : ℝ) ≤ L.sc.x ^ cD := Real.rpow_le_rpow_of_exponent_le hx1 hcD
    have h3 : L.sc.x ^ (805 : ℝ) = L.sc.x * y ^ 2 := by
      rw [hy, show (805 : ℝ) = 1 + (402 + 402) by norm_num, Real.rpow_add hxp, Real.rpow_add hxp,
        Real.rpow_one, sq]
    have h4 : 35 * y ^ 2 ≤ L.sc.x * y ^ 2 := mul_le_mul_of_nonneg_right hx35 (sq_nonneg _)
    rw [Rat.cast_natCast]
    exact h4.trans (h3.symm.le.trans (h2.trans h1))
  have hT0 : (0 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have : ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ (2 * y) ^ 2 := pow_le_pow_left₀ hT0 (by linarith) 2
    nlinarith
  · refine le_trans ?_ hDel
    calc _ ≤ (5 * y) * (7 * y) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = 35 * y ^ 2 := by ring

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_eta_bounds : SzRow (fun C D L => (L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)) ∧ (Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4)) ∧ ((D.R.t : ℝ) ≤ L.etaSz) ∧ ((D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x) ∧ ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD _ => ⟨401, fun ch hch => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (ch + (1224 : ℕ)) (1 / 2) he0 (by norm_num)
  obtain ⟨x2, h2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) (ch + (3 : ℕ)) 0 1 0 le_rfl
    (by positivity) one_pos
  refine ⟨max (max x1 x2) (max x3 2), fun D L hE hx V => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨-, -, s3, -, -, s6, -⟩ := h1 L.sc hE hx1
  obtain ⟨rf, rm, rr, rk, -, -, -, -, -, -, -, -, -, rt, -⟩ := h2 L.sc D.R hE hx2 V.ranks
  have h3' := h3 L.sc.x hx3
  have heta := V.eta_eq
  have hpos := L.etaSz_pos
  unfold h0v at heta
  push_cast at heta
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn1' : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn1
  obtain ⟨s7, -⟩ := s6 D.R.n hn1 (by linarith)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  have rk' : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast rk) rr
  rw [hE]
  generalize L.sc.x = x at *
  generalize L.sc.b = b at *
  generalize L.sc.X' = X at *
  generalize L.sc.w'' D.R.n = w at *
  generalize L.etaSz = η at *
  generalize (D.R.t : ℝ) = t at *
  generalize (D.R.m : ℝ) = m at *
  generalize (D.R.f : ℝ) = f at *
  generalize (D.R.k : ℝ) = k at *
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have hty : t ≤ x ^ ch := rt.trans (Real.rpow_le_rpow_of_exponent_le hx1' hch)
  have e3 : x ^ (ch + (3 : ℕ)) = x ^ ch * x ^ 3 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have eB : x ^ (ch + (1224 : ℕ)) = x ^ ch * x ^ 1224 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have rf' : f ≤ x ^ 3 := by rw [← Real.rpow_natCast]; exact_mod_cast rf
  have rk'' : k ≤ x ^ 5 := by rw [← Real.rpow_natCast]; exact_mod_cast rk'
  have rt' : t ≤ x ^ 401 := by rw [← Real.rpow_natCast]; exact_mod_cast rt
  have hy1 : 1 ≤ x ^ ch := ht1.trans hty
  have hc1 : x ^ ch ≤ (⌈x ^ ch⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hup : η ≤ x ^ ch * x ^ 3 := by
    rw [heta]
    have a1 : 2 * (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch * x ^ 2 := by
      have : 4 ≤ x ^ 2 := by nlinarith
      nlinarith
    calc m * (2 * (⌈x ^ ch⌉₊ : ℝ)) ≤ x * (x ^ ch * x ^ 2) := by gcongr
      _ = _ := by ring
  have hlo : t ≤ η := by rw [heta]; nlinarith
  have hlog : Real.log η ≤ x ^ (eps / 4) := by
    have a1 : Real.log η ≤ (ch + (3 : ℕ)) * Real.log x := by
      rw [← Real.log_rpow hx0, e3]; exact Real.log_le_log hpos hup
    simp only [zero_mul, add_zero, one_mul] at h3'
    exact a1.trans h3'
  rw [eB] at s3 s7
  generalize x ^ ch = y at *
  have hB0 : 0 ≤ y * x ^ 1224 := by positivity
  have hBb : y * x ^ 1224 ≤ b := by
    have a1 : b ^ (1 / 2 : ℝ) ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
    rw [Real.rpow_one] at a1
    exact (le_mul_of_one_le_right hB0 hX1).trans (s3.trans a1)
  have hBw : y * x ^ 1224 ≤ w :=
    (le_mul_of_one_le_left hB0 (Real.one_le_rpow hb1 (by norm_num))).trans s7
  have hf0 : 0 < f := by linarith
  refine ⟨?_, hlog, hlo, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    calc η * (t ^ 3 * f * k ^ 3) ≤ (y * x ^ 3) * ((x ^ 401) ^ 3 * x ^ 3 * (x ^ 5) ^ 3) := by gcongr
      _ = y * x ^ 1224 := by ring
      _ ≤ b := hBb
  · rw [le_div_iff₀ hx0]
    calc t * η * x ≤ x ^ 401 * (y * x ^ 3) * x := by gcongr
      _ = y * x ^ 405 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw
  · have a1 : t + 1 ≤ x * x ^ 401 :=
      calc t + 1 ≤ t + t := by gcongr
        _ = 2 * t := by ring
        _ ≤ x * x ^ 401 := by gcongr
    calc m * (t + 1) * η ≤ x * (x * x ^ 401) * (y * x ^ 3) := by gcongr
      _ = y * x ^ 406 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaLeW
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem eta_rows_of_pow_bounds {M k m r N L S η d W : ℝ} (hM : 8 ≤ M) (hk : k ≤ M) (hm1 : 1 ≤ m) (hm : m ≤ M)
    (hr0 : 0 ≤ r) (hr : r ≤ M) (hN : N ≤ M) (hL1 : 1 ≤ L) (hL : L ≤ M) (hS0 : 0 ≤ S) (hS : S ≤ M ^ 3)
    (he0 : 0 ≤ η) (he : η ≤ M ^ 3) (hd0 : 0 ≤ d) (hd : 1 ≤ d * M) (hW : M ^ 10 ≤ W) :
    m * (S + η) ≤ W * L ∧ N * η ≤ d * m * W ∧ η ^ 2 * r * L ≤ d * m * W ^ 2 ∧ k * S ≤ W := by
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hW1 : 1 ≤ W := le_trans (one_le_pow₀ hM1) hW
  have h9 : M ^ 9 ≤ d * m * W := by
    calc M ^ 9 = 1 * M ^ 9 := by ring
      _ ≤ (d * M) * M ^ 9 := by gcongr
      _ = d * 1 * M ^ 10 := by ring
      _ ≤ d * m * W := by gcongr
  have h45 : 2 * M ^ 4 ≤ M ^ 10 := by
    calc 2 * M ^ 4 ≤ M * M ^ 4 := by gcongr; linarith
      _ = M ^ 5 := by ring
      _ ≤ M ^ 10 := pow_le_pow_right₀ hM1 (by norm_num)
  have h4 : 0 ≤ M ^ 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc m * (S + η) ≤ M * (M ^ 3 + M ^ 3) := by gcongr
      _ = 2 * M ^ 4 := by ring
      _ ≤ W * 1 := by linarith
      _ ≤ W * L := by gcongr
  · calc N * η ≤ M * M ^ 3 := by gcongr
      _ = M ^ 4 := by ring
      _ ≤ M ^ 9 := pow_le_pow_right₀ hM1 (by norm_num)
      _ ≤ _ := h9
  · calc η ^ 2 * r * L ≤ (M ^ 3) ^ 2 * M * M := by gcongr
      _ = M ^ 8 := by ring
      _ ≤ M ^ 9 := pow_le_pow_right₀ hM1 (by norm_num)
      _ ≤ d * m * W * 1 := by linarith
      _ ≤ d * m * W * W := by gcongr
      _ = _ := by ring
  · calc k * S ≤ M * M ^ 3 := by gcongr
      _ = M ^ 4 := by ring
      _ ≤ W := by linarith

theorem szRow_eta_le_w : SzRow (fun C D L => ((D.R.m : ℝ) * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n * L.sc.L) ∧ ((D.R.N D.R.m : ℝ) * L.etaSz ≤ L.de2 * D.R.m * L.sc.w'' D.R.n) ∧ (L.etaSz ^ 2 * D.R.r * L.sc.L ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ^ 2) ∧ ((D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n)) := by
  intro eps h0 h1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch hch => ?_⟩⟩
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps ((cD + ch + 402) * (10 : ℕ)) 1 h0 one_pos
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  refine ⟨max 8 (max x1 x2), fun D L he hx hV => ?_⟩
  have h8 : 8 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hxa : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxb : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ := hx2 L.sc D.R he hxb hV.ranks
  have hx1' : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hn0 : (0 : ℝ) < D.R.n := by exact_mod_cast hn1
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    simp only [Ranks.f]; push_cast; linarith
  have hW := ((hx1 L.sc he hxa).2.2.2.2.2.1 D.R.n hn1 hn3).1
  rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_mul_natCast hx0.le] at hW
  set M := L.sc.x ^ (cD + ch + 402) with hM
  have key : ∀ a : ℝ, a ≤ cD + ch + 402 → L.sc.x ^ a ≤ M := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx1' ha
  have hxM : L.sc.x ≤ M := by simpa using key 1 (by linarith)
  have hM8 : 8 ≤ M := h8.trans hxM
  have hrM : (D.R.r : ℝ) ≤ M := hr.trans (key _ (by linarith))
  have hkM : (D.R.k : ℝ) ≤ M := le_trans (by exact_mod_cast hkr) hrM
  have hceil : ∀ a : ℝ, 0 ≤ a → a ≤ cD + ch + 402 → (⌈L.sc.x ^ a⌉₊ : ℝ) ≤ 2 * M := by
    intro a ha ha'
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le a)
    have := key a ha'
    linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * (⌈L.sc.x ^ cD⌉₊ : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; simp [Delv]
  have hEta : L.etaSz = (D.R.m : ℝ) * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) := by
    rw [hV.eta_eq]; simp [h0v]
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn0]; exact hV.host.2.2.1
  have hdp : 0 < L.sc.x ^ (-L.sc.eps) := Real.rpow_pos_of_pos hx0 _
  refine eta_rows_of_pow_bounds hM8 hkM ?_ (hm.trans hxM) (Nat.cast_nonneg _) hrM
    (hN.trans (key _ (by linarith))) hL1 (hL.trans hxM) ?_ ?_ ?_ ?_ (hdp.le.trans hd) ?_ hW
  · have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  · rw [hSc]; positivity
  · rw [hSc]
    have := hceil cD hcD (by linarith)
    calc (D.R.k : ℝ) * (4 * (⌈L.sc.x ^ cD⌉₊ : ℝ)) ≤ M * (4 * (2 * M)) := by gcongr
      _ = 8 * M ^ 2 := by ring
      _ ≤ M * M ^ 2 := by gcongr
      _ = M ^ 3 := by ring
  · rw [hEta]; positivity
  · rw [hEta]
    have := hceil ch hch (by linarith)
    have hmM := hm.trans hxM
    calc (D.R.m : ℝ) * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) ≤ M * (2 * (2 * M)) := by gcongr
      _ = 4 * M ^ 2 := by ring
      _ ≤ M * M ^ 2 := by gcongr; linarith
      _ = M ^ 3 := by ring
  · have hLM : L.sc.x ^ L.sc.eps ≤ M := hL.trans hxM
    calc (1 : ℝ) = L.sc.x ^ (-L.sc.eps) * L.sc.x ^ L.sc.eps := by
          rw [← Real.rpow_add hx0]; simp
      _ ≤ L.de2 * M := by gcongr; exact hdp.le.trans hd

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowGapFunFN
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem gap_cube_bound (x t k m r : ℝ) (hx : 4 ≤ x) (ht0 : 0 ≤ t) (hk0 : 0 ≤ k) (hm0 : 0 ≤ m) (hr0 : 0 ≤ r)
    (ht : t ≤ x ^ 401) (hk : k ≤ x ^ 5) (hm : m ≤ x) (hr : r ≤ x ^ 5) :
    t + 2 * (k + m * (t + (r + 6) + 1)) ^ 3 + 1 ≤ x ^ 1210 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have h5 : x ^ 5 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
  have h7 : (7 : ℝ) ≤ x ^ 401 := by
    have : x ^ 2 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
    nlinarith
  have h402 : x ^ 401 ≤ x ^ 402 := pow_le_pow_right₀ hx1 (by norm_num)
  have hA : k + m * (t + (r + 6) + 1) ≤ x ^ 403 := by
    have h1 : m * (t + (r + 6) + 1) ≤ x * (3 * x ^ 401) :=
      mul_le_mul hm (by linarith) (by positivity) hx0
    have h2 : x * (3 * x ^ 401) = 3 * x ^ 402 := by ring
    have h3 : 4 * x ^ 402 ≤ x * x ^ 402 := mul_le_mul_of_nonneg_right hx (by positivity)
    have h4 : x * x ^ 402 = x ^ 403 := by ring
    linarith
  have hA3 : (k + m * (t + (r + 6) + 1)) ^ 3 ≤ (x ^ 403) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hA 3
  have e1 : (x ^ 403) ^ 3 = x ^ 1209 := by rw [← pow_mul]
  have h9 : x ^ 401 ≤ x ^ 1209 := pow_le_pow_right₀ hx1 (by norm_num)
  have h1 : (1 : ℝ) ≤ x ^ 1209 := one_le_pow₀ hx1
  have h3 : 4 * x ^ 1209 ≤ x * x ^ 1209 := mul_le_mul_of_nonneg_right hx (by positivity)
  have h4 : x * x ^ 1209 = x ^ 1210 := (pow_succ' x 1209).symm
  rw [e1] at hA3
  linarith

theorem szRow_gap_fun_fN : SzRow (fun C D L => ((D.R.t : ℝ) + 2 * ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 + 1 ≤ h0 L) ∧ ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ h0 L)) := by
  intro eps he0 he1 C hC
  have hCN : 1 ≤ C.P.Ch0N := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD _ => ⟨max 1210 (3 + 402 * C.P.Ch0N), fun ch hch => ⟨max x0 4, ?_⟩⟩⟩
  intro D L hε hx hV
  have hx4 : 4 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hxp : 0 < L.sc.x := by linarith
  obtain ⟨hf, hm, hr, hkr, -, -, -, -, -, -, -, -, -, ht, hN, hm1, -⟩ :=
    hx0 L.sc D.R hε (le_trans (le_max_left _ _) hx) hV.ranks
  have hmp : (0 : ℝ) < D.R.m := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hm1
  have hh : L.sc.x ^ ch ≤ h0 L := by
    have e : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0
      rw [hV.eta_eq]
      field_simp
    rw [e]
    unfold h0v
    push_cast
    have h1 := Nat.le_ceil (L.sc.x ^ ch)
    have h2 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  constructor
  · have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by exact_mod_cast ht
    have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by exact_mod_cast hr
    have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
    have h1 := gap_cube_bound L.sc.x D.R.t D.R.k D.R.m D.R.r hx4 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) ht' hk' hm hr'
    have h2 : L.sc.x ^ ((1210 : ℕ) : ℝ) ≤ L.sc.x ^ ch :=
      Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (by push_cast; exact le_max_left _ _) hch)
    rw [Real.rpow_natCast] at h2
    linarith
  · have h1 : (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ (L.sc.x ^ (402 : ℝ)) ^ C.P.Ch0N :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by linarith)
    rw [← Real.rpow_mul hxp.le] at h1
    have h2 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ L.sc.x ^ (3 : ℝ) * L.sc.x ^ (402 * C.P.Ch0N) :=
      mul_le_mul hf h1 (by positivity) (by positivity)
    rw [← Real.rpow_add hxp] at h2
    have h3 : L.sc.x ^ (3 + 402 * C.P.Ch0N) ≤ L.sc.x ^ ch :=
      Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (le_max_right _ _) hch)
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeWSizeBmSizeXppStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeW_sizeBm_sizeXpp : SzRow (fun _ _ L => SizeW L ∧ SizeBm L ∧ SizeXpp L) := by
  first | exact @GlobalTheory.EX.szRow_sizeW_sizeBm_sizeXpp | exact GlobalTheory.EX.szRow_sizeW_sizeBm_sizeXpp | (intros; apply GlobalTheory.EX.szRow_sizeW_sizeBm_sizeXpp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaZeroNorm
section
noncomputable section

namespace GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation

theorem normTheta0 : GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic.NormTheta0 := GlobalTheory.ThetaNullNormSquares.normTheta0

end GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistPrimeDatumIntegralSupportAndInvariantStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrimeDatum_integral_support_and_invariant : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  first | exact @GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | exact GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | (intros; apply GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValOUnramifiedDegreeOne
section
open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.LocUnr

variable {K : Type} [Field K] [NumberField K]

theorem valuation_eq_exp_neg_one (P : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (h1 : r ∈ P.asIdeal)
    (h2 : r ∉ P.asIdeal ^ 2) : P.valuation K (algebraMap (𝓞 K) K r) = WithZero.exp (-1 : ℤ) := by
  have e : P.valuation K (algebraMap (𝓞 K) K r) = P.intValuation r := P.valuation_of_algebraMap r
  rw [e]
  have hr : r ≠ 0 := by rintro rfl; exact h2 (Submodule.zero_mem _)
  have a1 := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using h1)
  have a2 := mt (P.intValuation_le_pow_iff_mem r 2).1 h2
  rw [← WithZero.exp_log (P.intValuation_ne_zero r hr)] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  push_cast at a1 a2
  omega

noncomputable def redInt (P : HeightOneSpectrum (𝓞 K)) :
    𝓞 K →+* IsLocalRing.ResidueField (P.valuation K).valuationSubring :=
  (IsLocalRing.residue _).comp
    ((algebraMap (𝓞 K) K).codRestrict (P.valuation K).valuationSubring (fun r => P.valuation_le_one r))

end GlobalTheory.LvT.LocUnr
end

