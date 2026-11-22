import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeKRel
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

set_option maxHeartbeats 800000 in

theorem sizeKRel_of_rankVal {D : D7} (L : SizeData₂ D) (hR : RankVal L.sc D.R)
    (hK : 100 + 8 * |L.CGam| ≤ L.sc.x ^ (L.sc.eps / 1000)) (hrd : Real.log D.host.rdE ≤ L.sc.L) :
    SizeKRel L := by
  unfold SizeKRel szTh rankBudget
  generalize L.sc = s at *
  generalize L.CGam = c at *
  generalize Real.log D.host.rdE = ρ at *
  generalize D.R = R at *
  have hn2 := hR.n_le
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, -⟩ := hR
  have hx := s.one_lt_alt
  have hxp : 0 < s.x := lt_trans one_pos hx
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hc0 := abs_nonneg c
  have hc1 := le_abs_self c
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun h => Real.rpow_le_rpow_of_exponent_le hx.le h
  have pos : ∀ a : ℝ, 0 < s.x ^ a := fun a => Real.rpow_pos_of_pos hxp a
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx.le h
  have mul : ∀ {u v a b : ℝ}, u ≤ s.x ^ a → 0 ≤ v → v ≤ s.x ^ b → u * v ≤ s.x ^ (a + b) := by
    intro u v a b hu hv hv'
    rw [Real.rpow_add hxp]
    exact mul_le_mul hu hv' hv (pos _).le
  have mulL : ∀ {u v a b : ℝ}, s.x ^ a ≤ u → s.x ^ b ≤ v → s.x ^ (a + b) ≤ u * v := by
    intro u v a b hu hv
    rw [Real.rpow_add hxp]
    exact mul_le_mul hu hv (pos _).le ((pos _).le.trans hu)
  have pw : ∀ {u a : ℝ} (j : ℕ), 0 ≤ u → u ≤ s.x ^ a → u ^ j ≤ s.x ^ (a * j) := by
    intro u a j hu h
    rw [Real.rpow_mul_natCast hxp.le]
    exact pow_le_pow_left₀ hu h j
  have ab : ∀ {a C : ℝ}, C ≤ 100 → C * s.x ^ a ≤ s.x ^ (s.eps / 1000 + a) :=
    fun hC => mul (by linarith) (pos _).le le_rfl
  have hsq : Real.sqrt (s.x * s.delta1) = s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
    have : s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hxp, Real.rpow_one]; rfl
    rw [this, Real.sqrt_eq_rpow, ← Real.rpow_mul hxp.le]
    congr 1; ring
  rw [hsq] at hm1 hm2
  have h2m := R.two_le_m
  have hmk := R.m_add_three_le_k
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hkr' : (R.k : ℝ) ≤ R.r := by exact_mod_cast hkr
  have hfk : (R.f : ℝ) ≤ R.k := by exact_mod_cast R.f_le_k
  have hfn : (R.f : ℝ) = 2 * R.n := by unfold Ranks.f; push_cast; ring
  have h2m' : (2 : ℝ) ≤ R.m := by exact_mod_cast h2m
  have k5 : (5 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 5 ≤ R.k)
  have n0 : (0 : ℝ) ≤ R.n := by positivity
  have f0 : (0 : ℝ) ≤ R.f := by positivity
  have m0 : (0 : ℝ) ≤ R.m := by positivity
  have hf : (R.f : ℝ) ≤ s.x ^ (s.eps / 1000 + (2 + 8 * s.eps + s.eps / 100)) := by
    have := ab (C := 4) (a := 2 + 8 * s.eps + s.eps / 100) (by norm_num)
    linarith
  have hf2 : s.x ^ (2 + 8 * s.eps) ≤ (R.f : ℝ) := by linarith
  have hk : (R.k : ℝ) ≤ s.x ^ (s.eps / 1000 + (9 / 2 + 10 * s.eps)) :=
    hk2.trans (ab (by norm_num))
  have hm : (R.m : ℝ) ≤ s.x ^ (s.eps / 1000 + (1 / 2 - s.eps / 16)) :=
    hm2.trans (ab (by norm_num))
  have hL : s.L ≤ s.x ^ s.eps := le_rfl
  have hL1 : 1 ≤ s.L := one e0.le
  have L0 : 0 ≤ s.L := by linarith
  have hlog : ∀ y : ℝ, 5 ≤ y → 1 ≤ Real.log y := by
    intro y hy
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlk := hlog _ k5
  have hlr := hlog R.r (by linarith)
  have hsx : Real.sqrt s.x = s.x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hR0 : s.x ^ ((2 + 8 * s.eps) + -s.eps) ≤ (R.n : ℝ) * s.x ^ (-s.eps) := mulL hn1 le_rfl
  have hlf0 : 0 ≤ Real.log R.f := Real.log_natCast_nonneg _
  have hlf : Real.log R.f ≤ s.x ^ ((1 : ℝ) / 5) := by
    have h1 := Real.log_le_rpow_div f0 (show (0 : ℝ) < 1 / 30 by norm_num)
    have h2 : (R.f : ℝ) ^ ((1 : ℝ) / 30) ≤ s.x ^ ((1 : ℝ) / 10) := by
      calc (R.f : ℝ) ^ ((1 : ℝ) / 30) ≤ (s.x ^ (3 : ℝ)) ^ ((1 : ℝ) / 30) :=
            Real.rpow_le_rpow f0 (hf.trans (mono (by linarith))) (by norm_num)
        _ = _ := by rw [← Real.rpow_mul hxp.le]; norm_num
    have h3 := (ab (C := 30) (a := 1 / 10) (by norm_num)).trans (mono (b := 1 / 5) (by linarith))
    linarith
  have hlf2 : Real.log R.f ^ 2 ≤ s.x ^ ((2 : ℝ) / 5) :=
    (pw 2 hlf0 hlf).trans (mono (by norm_num))
  have hm4 : 4 * s.x ^ ((2 : ℝ) / 5) ≤ R.m :=
    ((ab (by norm_num)).trans (mono (by linarith))).trans hm1
  have h25 : 1 ≤ s.x ^ ((2 : ℝ) / 5) := one (by norm_num)
  have hthL : s.x ^ (s.eps / 100) * s.L ≤ R.f :=
    ((mul le_rfl L0 hL).trans (mono (by linarith))).trans hf2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ hk1
    refine (mul (mul (mul (mul le_rfl (by positivity) (pw 5 m0 hm)) f0 hf) L0 hL) (pos _).le le_rfl).trans (mono ?_)
    push_cast; linarith
  · refine le_trans ?_ hk1
    have h8 : 8 * c ≤ s.x ^ (s.eps / 1000) := by linarith
    refine (mul (mul (mul h8 (by positivity) (pw 5 m0 hm)) f0 hf) L0 hL).trans (mono ?_)
    push_cast; linarith
  · rw [hsx]
    refine hk.trans (le_trans (mono ?_) (mulL (mulL le_rfl hn1) hR0))
    linarith
  · rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith), sq]
    refine hk.trans (le_trans (mono ?_) (mulL (mulL hR0 hR0) hm1))
    linarith
  · refine le_trans ?_ hk1
    refine (mul (pw 2 m0 hm) L0 hL).trans (mono ?_)
    push_cast; linarith
  · refine le_trans ?_ hk1
    have h1 : Real.log s.x ≤ s.x ^ (1 : ℝ) := by
      rw [Real.rpow_one]; linarith [Real.log_le_sub_one_of_pos hxp]
    rw [hsx]
    refine (mul (mul hm (pos _).le le_rfl) (Real.log_nonneg hx.le) h1).trans (mono ?_)
    linarith
  · refine le_trans ?_ (hk1.trans (le_mul_of_one_le_right (by linarith) hlk))
    refine (mul (mul le_rfl (by positivity) (pw 6 m0 hm)) L0 hL).trans (mono ?_)
    push_cast; linarith
  · refine le_trans ?_ (hk1.trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hlk)))
    refine (mul_le_mul_of_nonneg_left hrd (by positivity)).trans ?_
    refine (mul (mul (mul le_rfl (by positivity) (pw 3 m0 hm)) L0 hL) L0 hL).trans (mono ?_)
    push_cast; linarith
  · refine Real.le_sqrt_of_sq_le ?_
    have h1 : R.m ≤ 2 * R.rS + 2 := by
      obtain ⟨j, hj⟩ := R.m_even
      unfold Ranks.rS; omega
    have h2 : (R.m : ℝ) ≤ 2 * R.rS + 2 := by exact_mod_cast h1
    linarith
  · have h1 : (R.m : ℝ) ≤ (R.m : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have h2 : (R.m : ℝ) ^ 2 ≤ (R.m : ℝ) ^ 2 * s.L := le_mul_of_one_le_right (by positivity) hL1
    linarith
  · have h1 : Real.log (Real.log s.b) ≤ s.L := by
      unfold Scale.b
      rw [Real.log_exp]
      linarith [Real.log_le_sub_one_of_pos (show 0 < s.L by linarith)]
    have h2 : (R.f : ℝ) ≤ R.r * R.f := le_mul_of_one_le_left f0 (by linarith)
    have h3 : (R.r : ℝ) * R.f ≤ R.r * R.f * Real.log R.r := le_mul_of_one_le_right (by positivity) hlr
    have h4 := mul_le_mul_of_nonneg_left h1 (pos (s.eps / 100)).le
    linarith
  · exact hthL.trans (le_mul_of_one_le_right f0 hlk)
  · rw [hfn]
    exact mul_le_mul_of_nonneg_right (le_trans h2m' (le_self_pow₀ (by linarith) (by norm_num))) n0
  · exact (hfk.trans hkr').trans (le_self_pow₀ (by linarith) (by norm_num))

theorem szRow_sizeKRel : SzRow (fun _ _ L => SizeKRel L) := by
  intro eps he0 he1 C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, hx1⟩ := hostBounds eps C.P.Cpde he0 he1 hC8
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 ((100 + 8 * |C.CGam|) ^ (eps / 1000)⁻¹), ?_⟩⟩⟩
  intro D L hLe hx hV
  refine sizeKRel_of_rankVal L hV.ranks ?_ ?_
  · rw [hV.CGam_eq, hLe]
    have h0 : (0 : ℝ) ≤ 100 + 8 * |C.CGam| := by positivity
    calc 100 + 8 * |C.CGam| = ((100 + 8 * |C.CGam|) ^ (eps / 1000)⁻¹) ^ (eps / 1000) :=
          (Real.rpow_inv_rpow h0 (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hx) (by positivity)
  · exact (hx1 L.sc D.R D.host hLe ((le_max_left _ _).trans hx) hV.ranks hV.host).2.2.2.2.2.2.2.1

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeWSizeBmSizeXpp
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem window_scale_bounds (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (C : FC) (cD ch : ℝ) :
    ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L →
      2 ≤ L.sc.x ∧ Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n ∧ L.etaSz + 1 ≤ L.sc.w'' D.R.n ∧
      L.sc.w'' D.R.n ≤ L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ L.sc.b := by
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (max ch 0 + 10) (1 / 2) he (by norm_num)
  obtain ⟨CN, x3, h3⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 1 2 (2 * (max 1 C.GK.La * CN ^ 2)) 2 (by norm_num)
  refine ⟨max (max x1 x2) (max (max x3 x4) 2), fun D L hs hx hV => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx2 : x2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx3 : x3 ≤ L.sc.x :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx4 : x4 ≤ L.sc.x :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx5 : 2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  obtain ⟨hf, hm, -⟩ := h1 L.sc D.R hs hx1 hV.ranks
  obtain ⟨-, -, -, hb', -, hw, -⟩ := h2 L.sc hs hx2
  obtain ⟨-, -, hLa⟩ := h3 L.sc hs hx3
  have hLa' := (hLa { C.GK with La := max 1 C.GK.La } (le_max_left _ _)).2
  have h4' := h4 L.sc.x hx4
  clear h1 h2 h3 h4 hLa hx1 hx2 hx3 hx4 hx
  have hetaE := hV.eta_eq
  have hLaE := hV.La_eq
  have hbT := hV.bT_le
  have hx0 : 0 < L.sc.x := by linarith
  have hone : 1 ≤ L.sc.x := by linarith
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn0 : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
  obtain ⟨hw1, hw2, -⟩ := hw D.R.n hn1 (by linarith)
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hsq : L.sc.b ^ (1 - 1 / 2 : ℝ) = Real.sqrt L.sc.b := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hsq1 : 1 ≤ Real.sqrt L.sc.b := Real.one_le_sqrt.2 hb1
  rw [hsq] at hw1
  have hy1 : 1 ≤ L.sc.x ^ (max ch 0) := Real.one_le_rpow hone (le_max_right _ _)
  have hych : L.sc.x ^ ch ≤ L.sc.x ^ (max ch 0) := Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)
  have hsplit : L.sc.x ^ (max ch 0 + 10) = L.sc.x ^ (max ch 0) * L.sc.x ^ 10 := by
    rw [Real.rpow_add hx0]; norm_num
  rw [hsplit] at hw1 hb'
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := Real.exp_pos (L.sc.x ^ (L.sc.eps / 3))
    positivity
  have hf3 : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by
    have : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by norm_num
    rw [← this]; exact hf
  have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
    have := Real.rpow_le_rpow_of_exponent_le hone (show L.sc.eps ≤ 1 by rw [hs]; linarith)
    rwa [Real.rpow_one] at this
  have hxe0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
  have hd1 : L.sc.delta1 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hone (by have := L.sc.eps_pos; linarith)
  have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0.le _
  have hLa2 : L.LaG ≤ L.sc.x ^ 2 := by
    have ha : 0 ≤ Real.log L.sc.a := by
      apply Real.log_nonneg
      unfold Scale.a
      exact one_le_mul_of_one_le_of_one_le hone hb1
    have e1 : L.LaG ≤ G.La { C.GK with La := max 1 C.GK.La } L.sc := by
      rw [hLaE]
      unfold G.La
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) ha
    have e2 : L.sc.x ^ (2 : ℝ) = L.sc.x ^ 2 := by norm_num
    rw [Real.rpow_one, e2] at h4'
    have e3 : 0 ≤ max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 := by
      have : 0 ≤ max 1 C.GK.La := le_trans zero_le_one (le_max_left _ _)
      positivity
    have e4 : max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x) :=
      mul_le_mul_of_nonneg_left (by linarith) e3
    have e5 : G.La { C.GK with La := max 1 C.GK.La } L.sc ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) := hLa'
    linarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hh0 : (h0v L.sc ch : ℝ) ≤ 4 * L.sc.x ^ (max ch 0) := by
    unfold h0v
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le ch)
    push_cast
    linarith
  have hh00 : (0 : ℝ) ≤ h0v L.sc ch := Nat.cast_nonneg _
  have heta : L.etaSz ≤ L.sc.x * (4 * L.sc.x ^ (max ch 0)) := by
    rw [hetaE]; exact mul_le_mul hm hh0 hh00 hx0.le
  have hterm : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
      L.sc.x ^ 6 * L.sc.b' := by
    have e1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps ≤ L.sc.x ^ 3 * 1 * L.sc.x := by
      have e0 : 2 * (D.R.n : ℝ) ≤ L.sc.x ^ 3 := hfn ▸ hf3
      exact mul_le_mul (mul_le_mul e0 hd1 hd0 (by positivity)) hxe hxe0 (by positivity)
    have e2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG ≤ L.sc.x ^ 6 := by
      calc _ ≤ 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x ^ 2 :=
            mul_le_mul_of_nonneg_left hLa2 (by positivity)
        _ ≤ L.sc.x ^ 3 * 1 * L.sc.x * L.sc.x ^ 2 := mul_le_mul_of_nonneg_right e1 (by positivity)
        _ = _ := by ring
    rw [div_le_iff₀ (by linarith)]
    calc _ ≤ L.sc.x ^ 6 * L.sc.b' := mul_le_mul_of_nonneg_right e2 hb'0.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hk1
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hone
  clear hych hsplit hh0 hLa' h4' hw
  generalize L.sc.x ^ (max ch 0) = y at hw1 hb' hy1 heta
  have hp4 : (16 : ℝ) ≤ L.sc.x ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hx5 4
    linarith
  have hp6 : L.sc.x ≤ L.sc.x ^ 6 := le_self_pow₀ hone (by norm_num)
  have hp10 : 16 * L.sc.x ^ 6 ≤ L.sc.x ^ 10 := by
    calc _ ≤ L.sc.x ^ 4 * L.sc.x ^ 6 := mul_le_mul_of_nonneg_right hp4 (by positivity)
      _ = _ := by ring
  have hyx : L.sc.x ^ 10 ≤ y * L.sc.x ^ 10 := le_mul_of_one_le_left (by positivity) hy1
  have hyx1 : 1 ≤ y * L.sc.x ^ 10 := by linarith
  have hA : y * (16 * L.sc.x) ≤ y * L.sc.x ^ 10 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hB : 1 ≤ y * L.sc.x := one_le_mul_of_one_le_of_one_le hy1 hone
  have hC : y * L.sc.x ^ 10 ≤ Real.sqrt L.sc.b * (y * L.sc.x ^ 10) := le_mul_of_one_le_left (by linarith) hsq1
  have hD : L.sc.b' * (L.sc.x ^ 6 + 2) ≤ L.sc.b' * (y * L.sc.x ^ 10) :=
    mul_le_mul_of_nonneg_left (by linarith) hb'0.le
  refine ⟨hx5, le_trans (le_mul_of_one_le_right (by linarith) hyx1) hw1, by linarith, hw2,
    le_trans (le_mul_of_one_le_right hb'0.le hyx1) hb', fun t => ?_⟩
  have := hbT t
  linarith

theorem place_top_or_thick_or_thin (D : D7) (τ : D.what₂.Tau) :
    (∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t) ∨
      (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces ∨ D.host.IsThin (D.eTau τ : D.R.GG) := by
  by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    unfold Host.topPlaces at h1
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
    exact ⟨⟨t, ht⟩, e.symm⟩
  · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨(D.eTau τ).2, h1, h2⟩)

theorem szRow_sizeW_sizeBm_sizeXpp : SzRow (fun _ _ L => SizeW L ∧ SizeBm L ∧ SizeXpp L) := by
  intro eps he he' C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x0, h⟩ := window_scale_bounds eps he he' C cD ch
  refine ⟨x0, fun D L hs hx hV => ?_⟩
  obtain ⟨hx2, hW, heta, hwb, hbb, htop⟩ := h D L hs hx hV
  have heta0 := L.etaSz_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hdiv : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) hx0.le
  refine ⟨hW, ?_, ?_⟩
  · intro τ hm
    obtain ⟨-, -, ⟨b1, hb, h1, h2, h3⟩, -⟩ := hV.hc
    have hlow : L.sc.w'' D.R.n ≤ (b1 τ : ℝ) := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · rw [h1 τ t ht]
        have e1 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.2 hdiv
        have e2 := L.bT_ge t
        push_cast
        linarith
      · have e1 := Int.le_ceil L.sc.b
        have e2 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (h2 τ ht).1
        linarith
      · rw [h3 τ ht]; exact Int.le_ceil _
    rw [(hb τ _).1, (hb τ _).1]
    have e1 : ((D.R.m - 1 : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast Nat.sub_le _ _
    have e2 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz := by
      rw [hV.eta_eq]; exact mul_le_mul_of_nonneg_right e1 (Nat.cast_nonneg _)
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Nat.cast_zero, zero_mul, add_zero]
    linarith
  · intro j τ j' τ' hj1 hj2 hj1' hj2'
    have hup : wj D j τ ≤ 2 * L.sc.b := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j hj1 hj2 τ t ht).2
        have := htop t
        linarith
      · have := (L.win_thick j hj1 hj2 τ ht).2
        linarith
      · have := (L.win_thin j hj1 hj2 τ ht).2
        linarith
    have hlo : L.sc.w'' D.R.n ≤ wj D j' τ' := by
      rcases place_top_or_thick_or_thin D τ' with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j' hj1' hj2' τ' t ht).1
        have := L.bT_ge t
        linarith
      · have := (L.win_thick j' hj1' hj2' τ' ht).1
        linarith
      · exact (L.win_thin j' hj1' hj2' τ' ht).1
    have hw0 : 0 < L.sc.w'' D.R.n := by linarith
    have hb0 : 0 < L.sc.b := by linarith
    have hX0 : 0 ≤ L.sc.X'' D.R.n := by
      unfold Scale.X'' Scale.a; positivity
    have hXw : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b := by
      unfold Scale.X'' Scale.a; exact div_mul_cancel₀ _ hw0.ne'
    calc wj D j τ ≤ 2 * L.sc.b := hup
      _ ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx2 hb0.le
      _ = _ := hXw.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hX0

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistPrimeDatumIntegralSupportAndInvariant
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant

variable {E : Type} [Field E] [NumberField E]

theorem entB_zero (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x : (Fin N' → E) →ₗ[E] (Fin N → E)) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 x p p' =
      Loc.atN (x (Loc.eN E N' (LocE.fIdx k₀ c' n' p'))) (LocE.fIdx k₀ c n p) := by
  simp [LocE.entB, LocE.scE]

theorem intAt_entB {P : HeightOneSpectrum (𝓞 E)} (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ)
    {y : (Fin N' → E) →ₗ[E] (Fin N → E)} (hy : IntHom P y) (p p' : ℕ) :
    IntAt P (LocE.entB q k₀ c' n' c n 0 0 y p p') := by
  rw [entB_zero]
  have h : IntV P (Loc.eN E N' (LocE.fIdx k₀ c' n' p')) := fun l => by
    unfold Loc.eN
    split_ifs
    · exact intAt_one P
    · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  unfold Loc.atN
  split_ifs
  · exact hy _ h _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem entB_add (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x y : (Fin N' → E) →ₗ[E] (Fin N → E)) (a : E) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 (x + a • y) p p' =
      LocE.entB q k₀ c' n' c n 0 0 x p p' + a * LocE.entB q k₀ c' n' c n 0 0 y p p' := by
  rw [entB_zero, entB_zero, entB_zero, LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul]

theorem fIdx_fPos {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) :
    LocE.fIdx k₀ c n (LocE.fPos k₀ c n l) = l ∧ LocE.fPos k₀ c n l < n + c := by
  unfold LocE.fIdx LocE.fPos
  split_ifs <;> omega

theorem unitV_congr {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E}
    (h : redP P a = redP P b) : LocE.unitV ξ a = LocE.unitV ξ b := by
  unfold LocE.unitV
  have key : ∀ u v : 𝓞 E ⧸ P.asIdeal, u = v →
      (open Classical in if h : IsUnit u then ((ξ h.unit : Kˣ) : K) else 0) =
        (open Classical in if h : IsUnit v then ((ξ h.unit : Kˣ) : K) else 0) := by
    rintro u v rfl
    rfl
  exact key _ _ h

theorem intAt_add_iff {P : HeightOneSpectrum (𝓞 E)} {a b : E} (hb : IntAt P b) : IntAt P (a + b) ↔ IntAt P a :=
  ⟨fun h => by simpa using h.add (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg hb), fun h => h.add hb⟩

theorem phiQ_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  intro E _ _ K _ P ξ k₀ r c' n' c n hk' hk hr' hr
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · unfold LocE.PhiQ at hx
    split_ifs at hx with h
    · rw [intHom_iff]
      intro s l
      obtain ⟨a1, a2⟩ := fIdx_fPos hk l.2
      obtain ⟨b1, b2⟩ := fIdx_fPos hk' s.2
      have := h.1 _ _ a2 b2
      rw [entB_zero, a1, b1] at this
      have e : Loc.eN E (n' + c') s.1 = Pi.single s 1 := by
        funext i
        simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
      rw [e] at this
      simpa [Loc.atN] using this
    · exact absurd rfl hx
  · have hq : (qOf P : E) ≠ 0 := NormalFormAtPrime.qOf_ne_zero P
    have hI := intAt_entB (qOf P) k₀ c' n' c n hy
    have e1 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p') ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p') := fun p p' => by
      rw [entB_add, intAt_add_iff ((TopStep.intAt_nat (qOf P)).mul (hI p p'))]
    have e2 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p' / (qOf P : E)) ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p' / (qOf P : E)) := fun p p' => by
      rw [entB_add, add_div, mul_div_cancel_left₀ _ hq, intAt_add_iff (hI p p')]
    unfold LocE.PhiQ
    split_ifs with h' h h
    rotate_left
    · exact absurd ⟨fun p p' a b => (e1 p p').1 (h'.1 p p' a b), fun p p' a b d => (e2 p p').1 (h'.2 p p' a b d)⟩ h
    · exact absurd ⟨fun p p' a b => (e1 p p').2 (h.1 p p' a b), fun p p' a b d => (e2 p p').2 (h.2 p p' a b d)⟩ h'
    · rfl
    · apply unitV_congr
      have hx : ∀ s t : Fin r, IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1) :=
        fun s t => h.1 _ _ (by have := s.2; omega) (by have := t.2; omega)
      refine (TopStep.det_int ?_).2.trans (Eq.trans ?_ (TopStep.det_int ?_).2.symm)
      · exact fun s t => (e1 _ _).2 (hx s t)
      swap
      · exact hx
      refine congrArg Matrix.det (Matrix.ext fun s t => ?_)
      change redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) s.1 t.1) =
        redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1)
      rw [entB_add, reduction_add (hx s t) ((TopStep.intAt_nat (qOf P)).mul (hI _ _)), reduction_mul (TopStep.intAt_nat (qOf P)) (hI _ _), TopStep.reduction_absNorm_eq_zero, zero_mul, add_zero]

end GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant
end
end

