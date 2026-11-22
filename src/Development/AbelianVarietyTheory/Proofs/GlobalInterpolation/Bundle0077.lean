import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLaRhoBot
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_la_rho_bot : SzRow (fun _ _ L => SizeLa L ∧ SizeRho L ∧ SizeBot L) := by
  intro eps he he' C hC
  have hLa1 : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (eps + eps / 100)
    (2 * C.GK.La * CN ^ 2) 2 (by linarith)
  obtain ⟨x3, h3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    ((2 + 8 * eps + eps / 100) + -(eps / 8) + eps + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 32 0 (by linarith)
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    (eps / 100 + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 2 1 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max (max x1 x2) (max x3 x4)) 1, ?_⟩⟩⟩
  intro D L hε hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hone⟩ := hx
  have hpos : 0 < L.sc.x := by linarith
  obtain ⟨hlo, hhi⟩ := (h1 L.sc hε hx1).2.2 C.GK hLa1
  rw [← hV.La_eq] at hlo hhi
  have hup : L.LaG ≤ L.sc.x ^ (eps + eps / 100) := by
    have := h2 _ hx2
    rw [hε] at hhi
    calc L.LaG ≤ _ := hhi
      _ = 2 * C.GK.La * CN ^ 2 * L.sc.x ^ eps * Real.log L.sc.x ^ 2 := by ring
      _ ≤ _ := this
  refine ⟨⟨hlo, ?_⟩, ?_, ?_⟩
  · simpa only [szTh, hε] using hup
  · have hn := hV.ranks.n_le
    obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hV.ranks
    have h3' := h3 _ hx3
    have h4' := h4 _ hx4
    simp only [Real.rpow_add hpos, pow_zero, pow_one, mul_one] at h3' h4'
    rw [← Real.rpow_add hpos 2, ← Real.rpow_add hpos (2 + 8 * eps) (eps / 100), ← Real.rpow_add hpos (9 / 2),
      ← Real.rpow_add hpos eps (eps / 100)] at h3'
    rw [← Real.rpow_add hpos (9 / 2), ← Real.rpow_add hpos eps (eps / 100)] at h4'
    have hL0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hpos _).le hlo
    unfold SizeRho szNst szTh Scale.delta1
    rw [hε] at hn hk ⊢
    have hkpos : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hpos _) hk
    have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hone
    rw [← add_div, div_le_iff₀ hkpos]
    have hA : 4 * (2 * (D.R.n : ℝ) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps * L.LaG ≤
        4 * (2 * (2 * L.sc.x ^ (2 + 8 * eps + eps / 100)) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps *
          L.sc.x ^ (eps + eps / 100) := by gcongr
    have hB : L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.LaG ≤
        L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.sc.x ^ (eps + eps / 100) := by gcongr
    have hK : L.sc.x ^ (-2 : ℝ) * L.sc.x ^ (9 / 2 + 10 * eps) ≤ L.sc.x ^ (-2 : ℝ) * D.R.k := by gcongr
    linarith
  · intro t
    have := hV.bT_le t
    unfold szNst
    exact this

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowRankSizes
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_rankSizes : SzRow (fun _ _ L => SizeN L ∧ SizeM L ∧ SizeK L ∧ SizeT L ∧ SizeTT L ∧ SizeDe2 L ∧ SizeLw L) := by
  intro eps h0 h1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (100 / eps * (2 * C.P.Cpde) + 4455), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog' : 100 / eps * (2 * C.P.Cpde) + 4455 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hq : 0 < 100 / eps := by positivity
  have hC1 : 1 ≤ C.P.Cpde := hV.host.one_le
  have hlog : 100 / eps + 4455 ≤ Real.log L.sc.x := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * C.P.Cpde by linarith) hq.le
    linarith
  have hth : szTh L = eps / 100 := by rw [szTh, he]
  have hth0 : 0 ≤ szTh L := by rw [hth]; positivity
  have h2C : 2 * C.P.Cpde ≤ L.sc.x ^ szTh L := by
    rw [Real.rpow_def_of_pos hx0, hth]
    have a : 2 * C.P.Cpde ≤ Real.log L.sc.x * (eps / 100) := by
      have b : 100 / eps * (2 * C.P.Cpde) * (eps / 100) = 2 * C.P.Cpde := by field_simp
      have c : 100 / eps * (2 * C.P.Cpde) * (eps / 100) ≤ Real.log L.sc.x * (eps / 100) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have := Real.add_one_le_exp (Real.log L.sc.x * (eps / 100))
    linarith
  have h2 : 2 ≤ L.sc.x ^ szTh L := by linarith
  have hneg : L.sc.x ^ (-szTh L) ≤ 1 / 2 := by
    rw [Real.rpow_neg hx0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hlo : ∀ a : ℝ, L.sc.x ^ (a - szTh L) ≤ L.sc.x ^ a := fun a =>
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hhi : ∀ a : ℝ, 2 * L.sc.x ^ a ≤ L.sc.x ^ (a + szTh L) := fun a => by
    rw [Real.rpow_add hx0, mul_comm]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    exact_mod_cast this
  have n2 : (D.R.n : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) := by
    refine (hV.ranks.n_le_of_o hV.host.o_le).trans ?_
    rw [Real.rpow_add hx0 (2 + 8 * L.sc.eps), mul_comm]
    exact mul_le_mul_of_nonneg_left h2C (by positivity)
  obtain ⟨⟨n1, -⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, -⟩ := hV.ranks
  obtain ⟨-, ⟨t1, t2⟩, d2, -, -, hLw, -⟩ := hV.host
  have hs := Real.sqrt_nonneg (L.sc.x * L.sc.delta1)
  have hd1 : 0 ≤ L.sc.delta1 := by unfold Scale.delta1; positivity
  refine ⟨⟨(hlo _).trans n1, n2⟩, ⟨?_, ?_⟩, ⟨(hlo _).trans k1, k2.trans (hhi _)⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hneg hs
    linarith
  · exact m2.trans (mul_le_mul_of_nonneg_right h2 hs)
  · have h := D.R.rank_add_five_le
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  · exact L.t_win.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
  · have := mul_le_mul_of_nonneg_right hneg (mul_nonneg hn.le hd1)
    calc L.sc.x ^ (-szTh L) * D.R.n * L.sc.delta1 = L.sc.x ^ (-szTh L) * (D.R.n * L.sc.delta1) := by ring
      _ ≤ 1 / 2 * (D.R.n * L.sc.delta1) := this
      _ = L.sc.delta1 * D.R.n / 2 := by ring
      _ ≤ _ := t1
  · exact t2.trans (le_of_eq (by unfold szNst; ring))
  · unfold SizeDe2
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact d2
  · unfold SizeLw
    rw [hLw, Lwv, he]
    have a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1 := Nat.ceil_lt_add_one (by positivity)
    have a3 : 100 / eps = 10 / 3 * (30 / eps) := by ring
    have a4 : 4455 * Real.log L.sc.x ≤ Real.log L.sc.x ^ 2 := by nlinarith
    push_cast
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSigGaps
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rankVal_crude (s : Scale) (R : Ranks) (hx : 2 ≤ s.x) (h : RankVal s R) :
    (0 < (R.n : ℝ) ∧ (R.n : ℝ) ≤ s.x ^ 4) ∧ (R.m : ℝ) ≤ s.x ^ 2 ∧ (R.k : ℝ) ≤ s.x ^ 6 := by
  have hn1 := h.n_lo
  have hn2 := h.n_le'
  obtain ⟨-, ⟨-, hm⟩, ⟨-, hk⟩, -⟩ := h
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have he' := s.eps_lt
  refine ⟨⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hn1, ?_⟩, ?_, ?_⟩
  · have h1 : s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ ((3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; norm_num)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 3 := by positivity
    have h3 : s.x ^ 4 = s.x * s.x ^ 3 := by ring
    nlinarith
  · have h1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have h2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
      apply Real.sqrt_le_iff.2
      refine ⟨hx0.le, ?_⟩
      nlinarith
    nlinarith
  · have h1 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 5 := by positivity
    have h3 : s.x ^ 6 = s.x * s.x ^ 5 := by ring
    nlinarith

theorem gap_crude (x C k m t : ℝ) (hx : 2 ≤ x) (hC : C ≤ x) (hk0 : 0 ≤ k) (hm0 : 0 ≤ m) (ht0 : 0 ≤ t)
    (hm : m ≤ x ^ 2) (hk : k ≤ x ^ 6) (ht : t ≤ x ^ 401) :
    C * k * m ^ 4 + (k + m * (t + 1)) * m ^ 10 < x ^ 430 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have a1 : C * k * m ^ 4 ≤ x * x ^ 6 * (x ^ 2) ^ 4 := by
    have : C * k * m ^ 4 ≤ x * k * m ^ 4 := by gcongr
    refine this.trans ?_
    gcongr
  have a2 : (1 : ℝ) ≤ x ^ 401 := one_le_pow₀ hx1
  have a3 : (k + m * (t + 1)) * m ^ 10 ≤ (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 := by gcongr
  have a4 : x * x ^ 6 * (x ^ 2) ^ 4 = x ^ 15 := by ring
  have a5 : (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 = x ^ 26 + 2 * x ^ 423 := by ring
  have a6 : x ^ 15 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a7 : x ^ 26 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a8 : (2 : ℝ) ^ 7 ≤ x ^ 7 := by gcongr
  have a9 : x ^ 430 = x ^ 7 * x ^ 423 := by ring
  have a10 : 0 < x ^ 423 := by positivity
  have a11 : 2 ^ 7 * x ^ 423 ≤ x ^ 7 * x ^ 423 := by gcongr
  rw [a9]
  rw [a4] at a1
  rw [a5] at a3
  generalize x ^ 423 = y at *
  linarith

theorem base_sizes_ge (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (n : ℕ), s.eps = eps → x0 ≤ s.x →
    0 < (n : ℝ) → (n : ℝ) ≤ s.x ^ 4 → s.x ^ 430 ≤ s.b ∧ s.x ^ 430 ≤ s.b' ∧ s.x ^ 430 ≤ s.w'' n := by
  obtain ⟨x0, h0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps 434 1 1 0 (by positivity)
    (by linarith) one_pos
  refine ⟨x0, fun s n hs hx hn0 hn => ?_⟩
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have h1 := h0 s.x hx
  rw [← hs] at h1
  simp only [pow_zero, one_mul, mul_one] at h1
  have hX0 : 0 < s.X' := Real.exp_pos _
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have h2 : s.x ^ 434 * s.X' ≤ s.b := by
    have e : s.x ^ 434 = Real.exp (434 * Real.log s.x) := by
      rw [show (434 : ℝ) = ((434 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
    rw [e, Scale.X', Scale.b, Scale.L, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h3 : s.x ^ 430 ≤ s.x ^ 434 := pow_le_pow_right₀ hx1 (by norm_num)
  have h4 : s.x ^ 434 ≤ s.b / s.X' := (le_div_iff₀ hX0).2 h2
  have h5 : 0 < s.x ^ 434 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · exact h3.trans ((le_mul_of_one_le_right h5.le hX1).trans h2)
  · have e : s.b' = s.x * (s.b / s.X') := by rw [Scale.b', Scale.a]; ring
    rw [e]
    exact h3.trans (h4.trans (le_mul_of_one_le_left (h5.le.trans h4) hx1))
  · have e : s.w'' n = (s.b / s.X') / n := by
      rw [Scale.w'', Scale.b', Scale.a]; field_simp
    rw [e, le_div_iff₀ hn0]
    refine le_trans ?_ h4
    calc s.x ^ 430 * n ≤ s.x ^ 430 * s.x ^ 4 := by gcongr
      _ = s.x ^ 434 := by ring

theorem szRow_sig_gaps : SzRow (fun C D L => (∀ τ, (∀ (i : ℕ) (h : i + 1 < D.R.k - 1), gapS D C.P.Cgap < (((D.hc τ).v ⟨i, by omega⟩ - (D.hc τ).v ⟨i + 1, h⟩ : ℚ) : ℝ)) ∧ (∀ (hk : 2 ≤ D.R.k) (hm : 0 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ + (D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ)) ∧ (∀ (j : ℕ) (h : j + 1 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)))) := by
  intro eps he _ C hC
  obtain ⟨x0, hx0⟩ := base_sizes_ge eps he
  refine ⟨430, fun cD hcD => ⟨430, fun ch hch => ⟨max x0 (max 2 C.P.Cgap), fun D L hs hx hV => ?_⟩⟩⟩
  have hxa : x0 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C.P.Cgap ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  obtain ⟨⟨hn0, hn⟩, hm, hk⟩ := rankVal_crude L.sc D.R hx2 hV.ranks
  obtain ⟨hb, hb', hw⟩ := hx0 L.sc D.R.n hs hxa hn0 hn
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by
    have h1 := L.t_win.2
    rw [hV.Ct_eq, hC.1.2.2.2.2.2.2.2.2.2, show (401 : ℝ) = ((401 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
    exact h1
  have hg : gapS D C.P.Cgap < L.sc.x ^ 430 := by
    have := gap_crude L.sc.x C.P.Cgap D.R.k D.R.m D.R.t hx2 hxC (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hm hk ht
    unfold gapS Ranks.N
    push_cast
    exact this
  have hp : 0 < L.sc.x ^ 430 := by positivity
  have hpow : ∀ c : ℝ, 430 ≤ c → L.sc.x ^ 430 ≤ (⌈L.sc.x ^ c⌉₊ : ℝ) := by
    intro c hc
    refine le_trans ?_ (Nat.le_ceil _)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; exact hc)
  obtain ⟨hv, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
  have hb1 : ∀ τ, L.sc.x ^ 430 ≤ (b1 τ : ℝ) := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at h1
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
      rw [htop τ ⟨t, htT⟩ hteq.symm]
      have h2 := L.bT_ge ⟨t, htT⟩
      have h3 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by
        exact_mod_cast Int.floor_nonneg.2 (div_nonneg (by linarith) (by linarith))
      push_cast
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have h3 := Int.le_ceil L.sc.b
        have h4 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (hthick τ h2).1
        linarith
      · rw [hthin τ ⟨(D.eTau τ).2, h1, h2⟩]
        exact hw.trans (Int.le_ceil _)
  generalize L.sc.x ^ 430 = y at *
  intro τ
  refine ⟨fun i h => ?_, fun hk2 hm0 => ?_, fun j h => ?_⟩
  · rw [hv, hv]
    have e : D.R.k - 2 - i = (D.R.k - 2 - (i + 1)) + 1 := by omega
    simp only [e]
    have := hpow cD hcD
    unfold Delv
    push_cast
    linarith
  · rw [hv, (hbj τ _).1]
    have := hb1 τ
    simp only [Nat.sub_self]
    push_cast
    linarith
  · rw [(hbj τ _).1, (hbj τ _).1]
    have := hpow ch hch
    unfold h0v
    push_cast
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTOPPLeB
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem f_mul_r_mul_L_le_pow_fourteen (s : Scale) (R : Ranks) (hx : 2 ≤ s.x) (hR : RankVal s R) :
    (R.f : ℝ) * (R.r : ℝ) * s.L ≤ s.x ^ 14 := by
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 ≤ s.x := by linarith
  have he0 := s.eps_pos
  have he1 := s.eps_lt
  obtain ⟨⟨-, hn⟩, ⟨-, hm⟩, ⟨-, hk⟩, -⟩ := hR
  have hpow : ∀ (a : ℝ) (n : ℕ), a ≤ n → s.x ^ a ≤ s.x ^ n := fun a n h => by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 h
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ 3 := by
    have h3 := hpow (2 + 8 * s.eps) 3 (by push_cast; linarith)
    have h2 : (R.f : ℝ) = 2 * (R.n : ℝ) := by simp [Ranks.f]
    rw [h2]
    linarith
  have hk5 : (R.k : ℝ) ≤ 2 * s.x ^ 5 := by
    have h5 := hpow (9 / 2 + 10 * s.eps) 5 (by push_cast; linarith)
    linarith
  have hm1 : (R.m : ℝ) ≤ 2 * s.x := by
    have hd : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hsq : Real.sqrt (s.x * s.delta1) ≤ s.x := by
      calc Real.sqrt (s.x * s.delta1) ≤ Real.sqrt (s.x ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [mul_le_mul_of_nonneg_left hd hx0]
        _ = s.x := Real.sqrt_sq hx0
    linarith
  have hx5 : s.x ≤ s.x ^ 5 := by
    have h4 : 1 ≤ s.x ^ 4 := one_le_pow₀ hx1
    nlinarith
  have hr : (R.r : ℝ) ≤ 4 * s.x ^ 5 := by
    have h1 : R.r ≤ R.k + R.m := Nat.sub_le _ _
    have h2 : (R.r : ℝ) ≤ R.k + R.m := by exact_mod_cast h1
    linarith
  have hL : s.L ≤ s.x := by
    calc s.x ^ s.eps ≤ s.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = s.x := Real.rpow_one _
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg hx0 _
  have h16 : (16 : ℝ) ≤ s.x ^ 5 := by
    have h1 : (2 : ℝ) ^ 5 ≤ s.x ^ 5 := pow_le_pow_left₀ (by norm_num) hx 5
    norm_num at h1
    linarith
  have hx3 := pow_nonneg hx0 3
  have hx5' := pow_nonneg hx0 5
  calc (R.f : ℝ) * R.r * s.L ≤ (4 * s.x ^ 3) * (4 * s.x ^ 5) * s.x :=
        mul_le_mul (mul_le_mul hf hr (by positivity) (by linarith)) hL hL0
          (mul_nonneg (by linarith) (by linarith))
    _ = 16 * s.x ^ 9 := by ring
    _ ≤ s.x ^ 5 * s.x ^ 9 := mul_le_mul_of_nonneg_right h16 (pow_nonneg hx0 9)
    _ = s.x ^ 14 := by ring

theorem szRow_TO_PP_le_b : SzRow (fun C D L => (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ))) := by
  intro eps heps heps' C hC
  obtain ⟨-, -, -, -, -, -, -, -, heP, -, -, -, -, hCP, -, hLast⟩ := hC
  have hCb : 1 ≤ C.T.Cb := hLast C.T.Cb (by simp [FC.cLast])
  obtain ⟨x1, hx1⟩ := GlobalTheory.scale_poly_comparison eps (1259 + C.T.Cb) (1 / 2) heps (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max x1 2) (4 * C.T.CP ^ 3), fun D L hLe hx hV => ?_⟩⟩⟩
  have hxK : 4 * C.T.CP ^ 3 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxx1 : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1' : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have hCP0 : 0 ≤ C.T.CP := by linarith

  have hXb := (hx1 L.sc hLe hxx1).2.2.1
  have hX' : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx0 _)
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0 _)
  have hxc : L.sc.x ^ (1259 + C.T.Cb) ≤ L.sc.b ^ (1 / 2 : ℝ) :=
    le_trans (le_mul_of_one_le_right (Real.rpow_nonneg hx0 _) hX') hXb
  have hbh : L.sc.b ^ (1 / 2 : ℝ) ≤ L.sc.b := by
    calc L.sc.b ^ (1 / 2 : ℝ) ≤ L.sc.b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
      _ = L.sc.b := Real.rpow_one _

  have hz : zBase L ≤ L.sc.x ^ 14 := f_mul_r_mul_L_le_pow_fourteen L.sc D.R hx2 hV.ranks
  obtain ⟨⟨hn1, -⟩, -, -, -⟩ := hV.ranks
  have hn : 1 ≤ (D.R.n : ℝ) := le_trans (Real.one_le_rpow hx1' (by linarith [L.sc.eps_pos])) hn1
  have hf1 : 1 ≤ (D.R.f : ℝ) := by
    have h2 : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by simp [Ranks.f]
    rw [h2]
    linarith
  have hr1 : 1 ≤ (D.R.r : ℝ) := by
    have h2 := D.R.two_le_m
    have h3 : 1 ≤ D.R.r := by
      unfold Ranks.r
      omega
    exact_mod_cast h3
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1' (le_of_lt L.sc.eps_pos)
  have hz1 : 1 ≤ zBase L := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hL1
  have hz0 : 0 ≤ zBase L := by linarith
  have hz12 : zBase L ^ (12 : ℝ) = zBase L ^ (12 : ℕ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hP1 : 1 ≤ C.T.CP * zBase L ^ (12 : ℝ) := by
    rw [hz12]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hz1)
  have hP2 : C.T.CP * zBase L ^ (12 : ℝ) ≤ C.T.CP * L.sc.x ^ 168 := by
    rw [hz12]
    apply mul_le_mul_of_nonneg_left _ hCP0
    calc zBase L ^ 12 ≤ (L.sc.x ^ 14) ^ 12 := pow_le_pow_left₀ hz0 hz 12
      _ = L.sc.x ^ 168 := by ring
  have hT1 : (1 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := by
    have h1 : 0 < TOv L.sc := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxpos _)
    exact_mod_cast h1
  have hT2 : ((TOv L.sc : ℕ) : ℝ) ≤ 2 * L.sc.x ^ 377 := by
    have h1 : ((TOv L.sc : ℕ) : ℝ) < L.sc.x ^ (377 : ℝ) + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0 _)
    have h2 : L.sc.x ^ (377 : ℝ) = L.sc.x ^ (377 : ℕ) := by
      rw [show (377 : ℝ) = ((377 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : 1 ≤ L.sc.x ^ (377 : ℕ) := one_le_pow₀ hx1'
    rw [h2] at h1
    linarith
  have hCb1 : 1 ≤ L.sc.x ^ C.T.Cb := Real.one_le_rpow hx1' (by linarith)
  have hW : (C.T.CP * zBase L ^ (12 : ℝ)) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤
      L.sc.x ^ (1259 + C.T.Cb) := by
    have h1 : (C.T.CP * zBase L ^ (12 : ℝ)) ^ 3 ≤ (C.T.CP * L.sc.x ^ 168) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hP2 3
    have h2 : ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ (2 * L.sc.x ^ 377) ^ 2 := pow_le_pow_left₀ (by linarith) hT2 2
    have h3 := mul_le_mul h1 h2 (by positivity) (pow_nonneg (mul_nonneg hCP0 (pow_nonneg hx0 _)) _)
    have h4 : (C.T.CP * L.sc.x ^ 168) ^ 3 * (2 * L.sc.x ^ 377) ^ 2 = 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 := by ring
    have h5 : 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 ≤ L.sc.x ^ 1259 := by
      calc 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 ≤ L.sc.x * L.sc.x ^ 1258 :=
            mul_le_mul_of_nonneg_right hxK (pow_nonneg hx0 _)
        _ = L.sc.x ^ 1259 := by ring
    have h6 : L.sc.x ^ (1259 : ℕ) * L.sc.x ^ C.T.Cb = L.sc.x ^ (1259 + C.T.Cb) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hxpos]
      norm_num
    rw [← h6]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0 _)
    rw [← h4] at h5
    exact le_trans h3 h5
  beta_reduce
  rw [heP]
  generalize ((TOv L.sc : ℕ) : ℝ) = T at hT1 hW ⊢
  generalize C.T.CP * zBase L ^ (12 : ℝ) = P at hP1 hW ⊢
  have hTP : T * P ≤ P ^ 3 * T ^ 2 := by
    have hP3 : P ≤ P ^ 3 := by nlinarith [one_le_pow₀ (n := 2) hP1]
    have hT' : T ≤ T ^ 2 := by nlinarith
    calc T * P ≤ T ^ 2 * P ^ 3 := mul_le_mul hT' hP3 (by linarith) (by positivity)
      _ = P ^ 3 * T ^ 2 := by ring
  have hW' : P ^ 3 * T ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ) := by
    have h1 : P ^ 3 * T ^ 2 ≤ P ^ 3 * T ^ 2 * L.sc.x ^ C.T.Cb :=
      le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by linarith) 3) (sq_nonneg T)) hCb1
    linarith
  have hTPx : T * P * L.sc.x ^ C.T.Cb ≤ P ^ 3 * T ^ 2 * L.sc.x ^ C.T.Cb :=
    mul_le_mul_of_nonneg_right hTP (Real.rpow_nonneg hx0 _)
  refine ⟨?_, ?_, ?_, hW'⟩
  · linarith
  · linarith
  · linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryQuotientIntegralProdOverPlacesStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuotientIntegral_prod_over_places : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  first | exact @GlobalTheory.RealQuotProd.quot_integral_prod | exact GlobalTheory.RealQuotProd.quot_integral_prod | (intros; apply GlobalTheory.RealQuotProd.quot_integral_prod <;> assumption)
end

