import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0030
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0032
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgTorInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormSqrtNegPowPrimeSqSub
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0026
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0017
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0008
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0024

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.EndIntegral
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem end_not_dvd (d : ℕ) (hd : d % 4 = 3) (l : ℕ) [Fact l.Prime]
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) : ¬ l ∣ (d + 1) / 4 := by
  intro h
  apply hin
  refine ⟨1, ?_⟩
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h0 : ((d + 1 : ℕ) : ZMod l) = 0 := by
    rw [← h4, ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.mul_left h 4
  push_cast at h0
  linear_combination h0

theorem end_unit (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : ¬ l ∣ n) (a : ℂ_[l]) (ha : ‖a‖ ≤ 1)
    (hq : a ^ 2 - a + (n : ℂ_[l]) = 0) : ‖a‖ = 1 := by
  have hnn : ‖(n : ℂ_[l])‖ = 1 := by
    simpa using kq_int_unit l (n : ℤ) (by exact_mod_cast hn)
  have hprod : a * (1 - a) = n := by linear_combination -hq
  have hb : ‖1 - a‖ ≤ 1 := by
    have e : 1 - a = 1 + -a := by ring
    rw [e]
    exact kq_add_le l _ _ 1 (by simp) (by rwa [norm_neg])
  refine le_antisymm ha ?_
  rw [← hnn, ← hprod, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hb

theorem end_card (d : ℕ) (hd : d % 4 = 3) (L : PeriodPair) (hCM : HasCMBy d L) (S : Finset ℂ)
    (h0 : omegaK d ≠ 0) (hS : Formalism.L2.Th1.F.IsKerReps L (omegaK d) S) :
    S.card + 1 = (d + 1) / 4 := by
  have h1 := Formalism.L2.Th1.F.kerRepsCard L (omegaK d) S h0 hCM hS
  have h2 := (Formalism.L2.Th1.F.hasCMByStable d L hCM 0 1).2
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h4' : (4 : ℝ) * (((d + 1) / 4 : ℕ) : ℝ) = (d : ℝ) + 1 := by exact_mod_cast h4
  have e : ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * omegaK d = omegaK d := by simp
  rw [e] at h2
  have h3 : ((S.card + 1 : ℕ) : ℝ) = (((d + 1) / 4 : ℕ) : ℝ) := by
    push_cast
    rw [h1, h2]
    push_cast
    linarith
  exact_mod_cast h3

theorem end_integral (d : ℕ) (L : PeriodPair) (hd : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (hl : 5 ≤ l) (hld : ¬ l ∣ d) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l))
    (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    IntegralPS ((uSer g2 g3).subst (C (ι (omegaK d)) * lgS g2 g3)) := by
  obtain ⟨L', hM, hCM'⟩ := good_lattice l L ι g2 g3 hg
  have hCM1 : HasCMBy d L' := hCM' d hCM
  have hl2 : l ≠ 2 := by omega
  have hquadC := omegaK_quad d hd
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι hquadC
    simpa using this
  have hln := end_not_dvd d hd l hin
  have hn0 : 0 < (d + 1) / 4 := by omega
  obtain ⟨ha1, -, -⟩ := kur_quad l d hd hl2 hld hin _ hquad
  have hau : ‖ι (omegaK d)‖ = 1 := end_unit l _ hln _ ha1 hquad
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := kq_int_unit l 2 (by
      intro h
      have h' : l ∣ 2 := by exact_mod_cast h
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'))
    simpa using this
  have hα : omegaK d ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hau
    exact zero_ne_one hau
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L' (omegaK d) hα hCM1
  have hcard := end_card d hd L' hCM1 S hα hS
  obtain ⟨neg, hE⟩ := endo_curve l L' ι (omegaK d) S hα hCM1 hS
  rw [← hM.eq2, ← hM.eq3] at hE
  have htor : ∀ P : S, ‖ι (L'.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L'.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    obtain ⟨hP1, hP2⟩ := hS.1 P P.2
    refine tor_integral l hl2 L' ι g2 g3 hM _ hn0 hln P ?_ hP2
    have e : (((d + 1) / 4 : ℕ) : ℂ) * (P : ℂ) = omegaK d * (P : ℂ) - omegaK d * (omegaK d * (P : ℂ)) := by
      linear_combination (P : ℂ) * hquadC
    rw [e]
    exact sub_mem hP1 (hCM1 _ hP1)
  have hc : Formalism.L2.Th1.C.CoeffIn (unitBall ℂ_[l]) (Formalism.L2.Th1.A.shortW g2 g3) :=
    shortW_intModel g2 g3 hM.n2 hM.n3 h2
  have h2R : (2 : ℂ_[l])⁻¹ ∈ unitBall ℂ_[l] := Formalism.L2.Th1.C.inv_mem_unitBall h2
  obtain ⟨hlp, hwp, hAx, -, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[l] (unitBall ℂ_[l]) _ hc
  have hDat := Formalism.L2.Th1.C.curveEndoR ℂ_[l] (unitBall ℂ_[l]) _ hc S neg _ _ (ι (omegaK d))
    (1 - ι (omegaK d)) hE (fun P => (htor P).1)
    (fun P => by
      change ‖ι (L'.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
      rw [norm_div, h2, div_one]
      exact (htor P).2)
    (by
      rw [Fintype.card_coe]
      have : ((S.card : ℂ_[l]) + 1) = (((d + 1) / 4 : ℕ) : ℂ_[l]) := by exact_mod_cast hcard
      rw [this]
      linear_combination -hquad)
    hau.le (Formalism.L2.Th1.C.inv_mem_unitBall hau)
    (by
      have : (Formalism.L2.Th1.A.shortW g2 g3).b₂ = 0 := by
        simp [Formalism.L2.Th1.A.shortW, WeierstrassCurve.b₂]
      rw [this]
      simp)
  have hEnd := Formalism.L2.Th1.C.endIntFromDatum ℂ_[l] (unitBall ℂ_[l]) _ _ _ _ _ S neg _ _ _ _ _
    hlp hwp hAx h2R hDat
  rw [lgS_eq_logSer, Formalism.L2.Th1.A.uSerEq]
  exact hEnd

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgLevel
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem half_cubic (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hM : LatModel l L ι g2 g3) :
    4 * ι (L.weierstrassP (L.ω₁ / 2)) ^ 3 - g2 * ι (L.weierstrassP (L.ω₁ / 2)) - g3 = 0 := by
  have hd : L.derivWeierstrassP (L.ω₁ / 2) = 0 :=
    (F.pDerivZero L _ L.ω₁_div_two_notMem_lattice).2
      (by rw [mul_div_cancel₀ _ (two_ne_zero)]; exact L.ω₁_mem_lattice)
  have h := L.derivWeierstrassP_sq _ L.ω₁_div_two_notMem_lattice
  rw [hd] at h
  have h' := congrArg ι h
  simp only [map_pow, map_mul, map_sub, map_zero, map_ofNat] at h'
  rw [hM.eq2, hM.eq3, ← h']
  norm_num

theorem half_prod_norm (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (S : Finset ℂ) (hS : F.IsKerReps L (l : ℂ) S)
    (hκ : ‖3 * ι (L.weierstrassP (L.ω₁ / 2)) ^ 2 - g2 / 4‖ = 1) :
    ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L.weierstrassP (L.ω₁ / 2)) - ι (L.weierstrassP P)‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have h := congrArg ι (an_two L l (hlp.odd_of_ne_two hl) S hS L.ω₁ L.ω₁_mem_lattice
    L.ω₁_div_two_notMem_lattice)
  simp only [map_pow, map_mul, map_prod, map_sub, map_natCast, map_div₀, map_ofNat] at h
  rw [← hM.eq2] at h
  have hn := congrArg norm h
  rw [norm_pow, norm_pow _ (l ^ 2 - 1), hκ, one_pow, norm_mul, norm_prod] at hn
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 hn

theorem level_le (L : PeriodPair) (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer g2 g3).subst (C (l : ℂ_[l]) * lgS g2 g3))‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := by omega
  obtain ⟨L', hM, -⟩ := good_lattice l L ι g2 g3 hg
  obtain ⟨-, -, h2, h3, hΔ, -⟩ := hg
  have h22 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := norm_natCast_Cl_of_not_dvd (l := l) (n := 2)
      (fun h => hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h))
    simpa using this
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hst : F.MulStable L' (l : ℂ) := fun ω hω => by
    have := L'.lattice.smul_mem (l : ℤ) hω
    simpa using this
  obtain ⟨S, hS⟩ := F.kerRepsExist L' (l : ℂ) hl0 hst
  have hcard : S.card + 1 = l ^ 2 := by
    have := F.kerRepsCard L' (l : ℂ) S hl0 hst hS
    rw [Complex.normSq_natCast] at this
    have h' : ((S.card + 1 : ℕ) : ℝ) = ((l ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [this]
      ring
    exact_mod_cast h'
  obtain ⟨U, hU0, hUi, hsq⟩ := sq_formula l hl2 L' ι g2 g3 hM l hlp.pos S hS
  obtain ⟨e', he'0, he'i, he'l⟩ := mulN_integral (curve_law g2 g3 h2 h3 h22) l
  have hee : e' = (uSer g2 g3).subst (C (l : ℂ_[l]) * lgS g2 g3) :=
    mult_unique g2 g3 _ e' he'0 he'l
  rw [← hee] at hsq ⊢
  obtain ⟨hAi, hA0, -⟩ :=
    A.bridgeCurve ℂ_[l] (A.shortW g2 g3) (shortW_intModel g2 g3 h2 h3 h22)
  have hAi' : IntegralPS (A.xS (A.shortW g2 g3)) := (integralPS_iff_mv _).2 hAi
  have hGi := integral_of_sq_eq he'i he'0 hUi hU0 hsq
  have hb := gauss_bound S (fun P => ι (L'.weierstrassP P)) _ hAi' hA0 _ hGi
  obtain ⟨he1, hκ⟩ := kap_unit g2 g3 _ h2 h3 hΔ h22 (half_cubic l L' ι g2 g3 hM)
  have hp := half_prod_norm l hl2 L' ι g2 g3 hM S hS hκ
  have hle : ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L'.weierstrassP (L'.ω₁ / 2)) - ι (L'.weierstrassP P)‖
      ≤ ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, max 1 ‖ι (L'.weierstrassP P)‖ := by
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Finset.prod_le_prod (fun P _ => norm_nonneg _) fun P _ => ?_
    exact (norm_sub_le_max_Cl l _ _).trans (max_le_max he1 le_rfl)
  rw [hp] at hle
  obtain ⟨i, hi, hi1⟩ := unit_coeff_mul hUi hGi (by rw [hU0, norm_one]) _
    (gauss_unit S (fun P => ι (L'.weierstrassP P)) _ hAi' hA0 _ (le_antisymm hb hle))
  refine unit_coeff_of_sq he'i (l ^ 2) ⟨i + 2, by omega, ?_⟩
  rw [hsq, mul_assoc, coeff_X_pow_mul]
  exact hi1

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKur
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

variable (l : ℕ) [Fact l.Prime]

theorem red_norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := norm_l_Cl l

theorem red_norm_natCast {n : ℕ} (h : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 :=
  norm_natCast_Cl_of_not_dvd l h

theorem kur_val {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) : ∃ m : ℤ, ‖x‖ = (l : ℝ) ^ m := by
  obtain ⟨y, hy, hd⟩ := kur_approx l hx ‖x‖ (norm_pos_iff.2 h0)
  have h2 : ‖x‖ = ‖y‖ :=
    norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hd (le_max_left _ _))
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact h0 (norm_eq_zero.1 h2)
  obtain ⟨m, a, -, b, -, ha, hb, e⟩ := kmu_shape l hy hy0
  refine ⟨-m, ?_⟩
  rw [h2, e, norm_mul, norm_div, ha, hb, div_one, mul_one, norm_zpow, norm_l_Cl, inv_zpow, zpow_neg]

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKurOmega
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem redOmegaK_quad (d m : ℕ) (hm : d + 1 = 4 * m) : omegaK d ^ 2 - omegaK d + (m : ℂ) = 0 := by
  have hs : (((Real.sqrt d : ℝ) : ℂ)) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hm' : (d : ℂ) + 1 = 4 * (m : ℂ) := by exact_mod_cast hm
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold omegaK
  have : ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) ^ 2 - (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2
      + (m : ℂ) = (Complex.I ^ 2 * (((Real.sqrt d : ℝ) : ℂ)) ^ 2 - 1 + 4 * (m : ℂ)) / 4 := by ring
  rw [this, hI, hs, ← hm']
  ring

theorem omega_mem_kur (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (l : ℕ) [Fact l.Prime] (hld : ¬ l ∣ d)
    (ι : ℂ ≃+* ℂ_[l]) : ι (omegaK d) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  set w : ℂ_[l] := ι (omegaK d) with hw
  have hq : w ^ 2 - w + (m : ℂ_[l]) = 0 := by
    have := congrArg ι (redOmegaK_quad d m hm)
    simpa using this
  have hm1 : ‖(m : ℂ_[l])‖ ≤ 1 := by
    rw [norm_natCast_Cl]
    exact Padic.norm_int_le_one (m : ℤ)
  have hd1 : ‖(d : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd l hld
  have hw1 : ‖w‖ ≤ 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have h1 : ‖w - 1‖ = ‖w‖ := by
      have hne : ‖w‖ ≠ ‖(-1 : ℂ_[l])‖ := by rw [norm_neg, norm_one]; exact hgt.ne'
      rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_one]
      exact max_eq_left hgt.le
    have h2 : w * (w - 1) = -(m : ℂ_[l]) := by linear_combination hq
    have h3 : ‖w‖ * ‖w‖ ≤ 1 := by
      have := congrArg norm h2
      rw [norm_mul, h1, norm_neg] at this
      rw [this]; exact hm1
    nlinarith
  have hder : ‖2 * w - 1‖ = 1 := by
    have h2 : (2 * w - 1) ^ 2 = -(d : ℂ_[l]) := by
      have hm' : (d : ℂ_[l]) + 1 = 4 * (m : ℂ_[l]) := by exact_mod_cast hm
      linear_combination 4 * hq + hm'
    have h3 : ‖2 * w - 1‖ ^ 2 = 1 := by rw [← norm_pow, h2, norm_neg, hd1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h3
  have hco : ∀ i, (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l]) : Polynomial ℂ_[l]).coeff i =
      (if i = 2 then 1 else 0) - (if 1 = i then 1 else 0) + (if i = 0 then (m : ℂ_[l]) else 0) := fun i => by
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_X]
  refine hensel_mem l (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l])) ?_ ?_ w hw1 ?_ ?_
  · intro i
    rw [hco]
    refine (MaximalUnramifiedExtension l).add_mem ((MaximalUnramifiedExtension l).sub_mem ?_ ?_) ?_
    · split_ifs
      · exact (MaximalUnramifiedExtension l).one_mem
      · exact (MaximalUnramifiedExtension l).zero_mem
    · split_ifs
      · exact (MaximalUnramifiedExtension l).one_mem
      · exact (MaximalUnramifiedExtension l).zero_mem
    · split_ifs
      · exact natCast_mem (MaximalUnramifiedExtension l) m
      · exact (MaximalUnramifiedExtension l).zero_mem
  · intro i
    rw [hco]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((norm_sub_le_max_Cl l _ _).trans (max_le ?_ ?_)) ?_)
    · split_ifs <;> simp
    · split_ifs <;> simp
    · split_ifs
      · exact hm1
      · simp
  · simpa using hq
  · have hd : (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l]) : Polynomial ℂ_[l]).derivative.eval w
        = 2 * w - 1 := by
      simp
      left; norm_num
    rw [hd, hder]

end ReciprocityTheory.ChartRestriction.L1
end
end

