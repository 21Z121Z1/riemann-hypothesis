import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0011
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TchOfIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0005
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormSqrtNegPowPrimeSqSub
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonH
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0014
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0028
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0033
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0022
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledTorsionPointNonsingular

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgClose
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem integral_of_map_kur {l : ℕ} [Fact l.Prime] {f : PowerSeries (MaximalUnramifiedExtension l)}
    (h : IntegralPS (PowerSeries.map (MaximalUnramifiedExtension l).subtype f)) : IntegralPS f := fun n => by
  have := h n
  rw [PowerSeries.coeff_map] at this
  exact this

theorem cm3 : CM3 := by
  intro d L _hsq hd hCM l _ hl hld hin ι g2 g3 hg
  obtain ⟨hg2, hg3, hn2, hn3, -, -⟩ := id hg
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  obtain ⟨σ, hσ⟩ := kurFrob l
  have hR := kur_resClosed l
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι (omegaK_quad d hd)
    simpa using this
  obtain ⟨-, ha1, ha', haσ⟩ := kur_quad l d hd (by omega) hld hin _ hquad
  have haσ' := haσ σ hσ
  have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := by
    have := norm_natCast_of_coprime (K := MaximalUnramifiedExtension l) hσ.prime hσ.norm_l 2
      (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hlaw := curve_law (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ hn2 hn3 h2
  have hD : HD σ (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) _
      ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
        (C (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))
      ⟨ι (omegaK d), ha'⟩ :=
    { toLawD := hlaw
      A0 := mult_const _ _ _
      Aint := integral_of_map_kur (by
        rw [mult_map]
        exact end_integral d L hd hCM l hl hld hin ι g2 g3 hg)
      Alog := mult_log _ _ _
      a_ne := by
        rw [haσ']
        have : ‖((1 - (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 := by
          have e : ((1 - (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])
              = 1 - 2 * ι (omegaK d) := by
            push_cast; ring
          rw [e]; exact ha1
        exact this
      a_sq := by
        rw [haσ', map_sub, map_one, haσ']; ring }
  have he : IntegralPS ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)) := by
    obtain ⟨e', h0, hint, hlog⟩ := mulN_integral hlaw l
    rw [← mult_unique _ _ _ e' h0 hlog]
    exact hint
  have hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))‖ = 1 := by
    obtain ⟨i, hi, hu⟩ := level_le L l hl ι g2 g3 hg
    refine ⟨i, hi, ?_⟩
    have hm := mult_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ ((l : ℕ) : MaximalUnramifiedExtension l)
    have hl' : (MaximalUnramifiedExtension l).subtype ((l : ℕ) : MaximalUnramifiedExtension l) = ((l : ℕ) : ℂ_[l]) := map_natCast _ _
    rw [hl'] at hm
    have hc := congrArg (coeff i) hm
    rw [PowerSeries.coeff_map] at hc
    have : ‖(MaximalUnramifiedExtension l).subtype (coeff i ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)))‖ = 1 := by
      rw [hc]; exact hu
    exact this
  obtain ⟨c, hc, hT⟩ := hon_main hσ hD (mult_const _ _ _) he (mult_log _ _ _) hlev
  obtain ⟨ε, hε, hcε⟩ := lang_semilinear hσ hR c hc
  have hfin := fin_integral hσ (uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)
    (lgS_const _ _) (lgS_coeff_one _ _) (uSer_const _ _) (uSer_subst_lgS _ _) c ε hc hε hcε hT
  refine ⟨ε, ε.2, hε, fun n => ?_⟩
  have hm := lt_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ l (by omega) ε
  have hc' := congrArg (coeff n) hm
  rw [PowerSeries.coeff_map] at hc'
  have hc'' : coeff n ((uSer g2 g3).subst (C (ε : ℂ_[l]) * ltLog ℂ_[l] l))
      = (MaximalUnramifiedExtension l).subtype (coeff n ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
          (C ε * ltLog (MaximalUnramifiedExtension l) l))) := hc'.symm
  rw [hc'']
  exact ⟨SetLike.coe_mem _, hfin n⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedModel
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

section SlopeTestRemainingChoices

variable (l : ℕ) [Fact l.Prime]

theorem norm_twentySeven_padicComplex_eq_one (h5 : 5 ≤ l) : ‖(27 : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  have h : ¬ l ∣ 27 := by
    intro h
    have h3 : l ∣ 3 := hp.dvd_of_dvd_pow (show l ∣ 3 ^ 3 by simpa using h)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  simpa using red_norm_natCast l h

theorem norm_1728_eq_one (h5 : 5 ≤ l) : ‖(1728 : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  have h : ¬ l ∣ 1728 := by
    intro h
    have h' : l ∣ 2 ^ 6 * 3 ^ 3 := by simpa using h
    rcases (hp.dvd_mul).1 h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
      omega
  simpa using red_norm_natCast l h

theorem twentySeven_mem_Kur : (27 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
  exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 27

theorem ofNat_1728_mem_Kur : (1728 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
  exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 1728

theorem model_generic (h5 : 5 ≤ l) (a b J : ℂ_[l]) (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : a ^ 3 - 27 * b ^ 2 ≠ 0) (hJe : J = 1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2))
    (hJ : J ∈ MaximalUnramifiedExtension l) (hJ1 : ‖J‖ ≤ 1) (m n : ℤ) (hm : ‖J‖ = (l : ℝ) ^ (3 * m))
    (hn : ‖J - 1728‖ = (l : ℝ) ^ (2 * n)) :
    ∃ g2 g3 : ℂ_[l], g2 ∈ MaximalUnramifiedExtension l ∧ g3 ∈ MaximalUnramifiedExtension l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1 ∧
      ∃ lam : ℂ_[l], lam ≠ 0 ∧ g2 = lam ^ 4 * a ∧ g3 = lam ^ 6 * b := by
  have hp : l.Prime := Fact.out
  have hx : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hp.pos
  have hl0 : (l : ℂ_[l]) ≠ 0 := by
    intro h
    have := red_norm_l l
    rw [h, norm_zero] at this
    exact (inv_ne_zero hx.ne') this.symm
  have h27 : (27 : ℂ_[l]) ≠ 0 := by
    intro h
    have := norm_twentySeven_padicComplex_eq_one l h5
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have h1728 : (1728 : ℂ_[l]) ≠ 0 := by
    intro h
    have := norm_1728_eq_one l h5
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hJs : J - 1728 = 1728 * 27 * b ^ 2 / (a ^ 3 - 27 * b ^ 2) := by
    rw [hJe]; field_simp; ring
  have hJs0 : J - 1728 ≠ 0 := by
    rw [hJs]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero h1728 h27) (pow_ne_zero _ hb)) hD
  set c : ℂ_[l] := 27 * J / (J - 1728) with hc
  have hcab : c = a ^ 3 / b ^ 2 := by
    rw [hc, hJs, hJe]; field_simp
  have hc27 : c - 27 = 27 * 1728 / (J - 1728) := by
    rw [hc]; field_simp; ring
  set t : ℂ_[l] := (l : ℂ_[l]) ^ (m - n) with ht
  have ht0 : t ≠ 0 := zpow_ne_zero _ hl0
  set X : ℝ := (l : ℝ) ^ m with hX
  set Y : ℝ := (l : ℝ) ^ n with hY
  have hX0 : 0 < X := zpow_pos hx _
  have hY0 : 0 < Y := zpow_pos hx _
  have hm' : ‖J‖ = X ^ 3 := by
    rw [hm, mul_comm, zpow_mul]; norm_cast
  have hn' : ‖J - 1728‖ = Y ^ 2 := by
    rw [hn, mul_comm, zpow_mul]; norm_cast
  have htn : ‖t‖ = Y / X := by
    rw [ht, norm_zpow, red_norm_l, inv_zpow', neg_sub, zpow_sub₀ hx.ne']
  have hcn : ‖c‖ = X ^ 3 / Y ^ 2 := by
    rw [hc, norm_div, norm_mul, norm_twentySeven_padicComplex_eq_one l h5, hm', hn', one_mul]
  have hc27n : ‖c - 27‖ = 1 / Y ^ 2 := by
    rw [hc27, norm_div, norm_mul, norm_twentySeven_padicComplex_eq_one l h5, norm_1728_eq_one l h5, hn', one_mul]
  have hdisc : (t ^ 2 * c) ^ 3 - 27 * (t ^ 3 * c) ^ 2 = t ^ 6 * c ^ 2 * (c - 27) := by ring
  have hdn : ‖(t ^ 2 * c) ^ 3 - 27 * (t ^ 3 * c) ^ 2‖ = 1 := by
    rw [hdisc, norm_mul, norm_mul, norm_pow, norm_pow, htn, hcn, hc27n]
    field_simp
  have hg2 : ‖t ^ 2 * c‖ ≤ 1 := by
    have h : ‖t ^ 2 * c‖ ^ 3 = ‖J‖ := by
      rw [norm_mul, norm_pow, htn, hcn, hm']
      field_simp
    rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) (three_ne_zero)]
    rw [h]; exact hJ1
  have hg3 : ‖t ^ 3 * c‖ ≤ 1 := by
    have h : ‖t ^ 3 * c‖ ^ 2 = ‖J - 1728‖ := by
      rw [norm_mul, norm_pow, htn, hcn, hn']
      field_simp
    rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) (two_ne_zero)]
    rw [h]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hJ1 ?_)
    rw [norm_neg]; exact (norm_1728_eq_one l h5).le
  have htK : t ∈ MaximalUnramifiedExtension l := zpow_mem (natCast_mem (MaximalUnramifiedExtension l) l) _
  have hcK : c ∈ MaximalUnramifiedExtension l :=
    div_mem (mul_mem (twentySeven_mem_Kur l) hJ) (sub_mem hJ (ofNat_1728_mem_Kur l))
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq (t * a / b) (show 0 < 2 by norm_num)
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h] at hlam
    have : t * a / b ≠ 0 := div_ne_zero (mul_ne_zero ht0 ha) hb
    exact this (by rw [← hlam]; simp)
  refine ⟨t ^ 2 * c, t ^ 3 * c, mul_mem (pow_mem htK _) hcK, mul_mem (pow_mem htK _) hcK,
    hg2, hg3, hdn, lam, hlam0, ?_, ?_⟩
  · have : lam ^ 4 = (lam ^ 2) ^ 2 := by ring
    rw [this, hlam, hcab]; field_simp
  · have : lam ^ 6 = (lam ^ 2) ^ 3 := by ring
    rw [this, hlam, hcab]; field_simp

end SlopeTestRemainingChoices

theorem model_of_valDiv (L : PeriodPair) (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) (ι : ℂ ≃+* ℂ_[l])
    (hJ : ι (jInv L) ∈ MaximalUnramifiedExtension l) (hJ1 : ‖ι (jInv L)‖ ≤ 1)
    (h3 : ι (jInv L) ≠ 0 → ∃ m : ℤ, ‖ι (jInv L)‖ = (l : ℝ) ^ (3 * m))
    (h2 : ι (jInv L) ≠ 1728 → ∃ m : ℤ, ‖ι (jInv L) - 1728‖ = (l : ℝ) ^ (2 * m)) :
    ∃ g2 g3, IsGoodModel l L ι g2 g3 := by
  have hD0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := discNeZero L
  have hD : (ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2 ≠ 0 := by
    intro h
    apply hD0
    apply ι.injective
    have e27 : ι 27 = 27 := map_ofNat ι 27
    simpa [e27] using h
  have hJe : ι (jInv L) = 1728 * (ι L.g₂) ^ 3 / ((ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2) := by
    have e27 : ι 27 = 27 := map_ofNat ι 27
    have e1728 : ι 1728 = 1728 := map_ofNat ι 1728
    simp [jInv, e27, e1728]
  have h1728 : (1728 : ℂ_[l]) ≠ 0 := by
    intro h
    have := norm_1728_eq_one l h5
    rw [h, norm_zero] at this
    exact zero_ne_one this
  by_cases ha : ι L.g₂ = 0
  · have hb : ι L.g₃ ≠ 0 := by
      intro hb
      apply hD
      rw [ha, hb]; ring
    obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq (ι L.g₃)⁻¹ (show 0 < 6 by norm_num)
    have hlam0 : lam ≠ 0 := by
      intro h
      rw [h] at hlam
      exact inv_ne_zero hb (by rw [← hlam]; simp)
    refine ⟨0, 1, zero_mem _, one_mem _, by simp, by simp, ?_, lam, hlam0, by rw [ha]; simp, ?_⟩
    · have : (0 : ℂ_[l]) ^ 3 - 27 * 1 ^ 2 = -27 := by ring
      rw [this, norm_neg, norm_twentySeven_padicComplex_eq_one l h5]
    · rw [hlam, inv_mul_cancel₀ hb]
  by_cases hb : ι L.g₃ = 0
  · obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq (ι L.g₂)⁻¹ (show 0 < 4 by norm_num)
    have hlam0 : lam ≠ 0 := by
      intro h
      rw [h] at hlam
      exact inv_ne_zero ha (by rw [← hlam]; simp)
    refine ⟨1, 0, one_mem _, zero_mem _, by simp, by simp, ?_, lam, hlam0, ?_, by rw [hb]; simp⟩
    · have : (1 : ℂ_[l]) ^ 3 - 27 * 0 ^ 2 = 1 := by ring
      rw [this, norm_one]
    · rw [hlam, inv_mul_cancel₀ ha]
  have hJ0 : ι (jInv L) ≠ 0 := by
    rw [hJe]
    exact div_ne_zero (mul_ne_zero h1728 (pow_ne_zero _ ha)) hD
  have hJ1728 : ι (jInv L) ≠ 1728 := by
    rw [hJe]
    intro h
    rw [div_eq_iff hD] at h
    have h' : (1728 : ℂ_[l]) * (27 * (ι L.g₃) ^ 2) = 0 := by linear_combination h
    have h27 : (27 : ℂ_[l]) ≠ 0 := by
      intro h
      have := norm_twentySeven_padicComplex_eq_one l h5
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact mul_ne_zero h1728 (mul_ne_zero h27 (pow_ne_zero _ hb)) h'
  obtain ⟨m, hm⟩ := h3 hJ0
  obtain ⟨n, hn⟩ := h2 hJ1728
  exact model_generic l h5 _ _ _ ha hb hD hJe hJ hJ1 m n hm hn

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedValB
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem unit_point (L : PeriodPair) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (h5 : 5 ≤ l) (μ : ℂ_[l])
    (hμ : μ ^ 12 * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1) (hg2 : ‖μ ^ 4 * ι L.g₂‖ ≤ 1)
    (hg3 : ‖μ ^ 6 * ι L.g₃‖ ≤ 1) (e N : ℕ)
    (he : e = 3 ∧ ‖μ ^ 4 * ι L.g₂‖ < 1 ∨ e = 2 ∧ ‖μ ^ 6 * ι L.g₃‖ < 1) (hlN : ¬ l ∣ N) (heN : ¬ e ∣ N)
    (z : ℂ) (hz : z ∉ L.lattice) (hNz : (N : ℂ) * z ∈ L.lattice) :
    ‖μ ^ 2 * ι (L.weierstrassP z)‖ = 1 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := red_norm_natCast l (n := 2) (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have h3 : ‖(3 : ℂ_[l])‖ = 1 := by
    have := red_norm_natCast l (n := 3) (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hN : ‖(N : ℂ_[l])‖ = 1 := red_norm_natCast l hlN
  have hΔ : ‖(μ ^ 4 * ι L.g₂) ^ 3 - 27 * (μ ^ 6 * ι L.g₃) ^ 2‖ = 1 := by
    have : (μ ^ 4 * ι L.g₂) ^ 3 - 27 * (μ ^ 6 * ι L.g₃) ^ 2 = μ ^ 12 * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    rw [this, hμ, norm_one]
  obtain ⟨h, hP⟩ := Formalism.L2.Th1.E.scaled_torsion_point_of_add Formalism.L2.Th1.E.PtOfAdd_of l L ι μ hμ0 z N hNz hz
  rcases he with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
  · exact torsUnit3 ℂ_[l] _ _ h2 h3 hlt hg3 hΔ N hN heN _ _ h hP
  · exact torsUnit2 ℂ_[l] _ _ h2 h3 hg2 hlt hΔ N hN heN _ _ h hP

theorem unit_prod (L : PeriodPair) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (h5 : 5 ≤ l) (μ : ℂ_[l])
    (hμ : μ ^ 12 * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1) (hg2 : ‖μ ^ 4 * ι L.g₂‖ ≤ 1)
    (hg3 : ‖μ ^ 6 * ι L.g₃‖ ≤ 1) (e N : ℕ)
    (he : e = 3 ∧ ‖μ ^ 4 * ι L.g₂‖ < 1 ∨ e = 2 ∧ ‖μ ^ 6 * ι L.g₃‖ < 1) (hlN : ¬ l ∣ N) (heN : ¬ e ∣ N)
    (T : Finset ℂ) (hT : ∀ z ∈ T, z ∉ L.lattice ∧ (N : ℂ) * z ∈ L.lattice) :
    ‖μ‖ ^ (2 * T.card) * ‖ι (∏ z ∈ T, L.weierstrassP z)‖ = 1 := by
  have key : ∏ z ∈ T, ‖μ ^ 2 * ι (L.weierstrassP z)‖ = 1 :=
    Finset.prod_eq_one fun z hz =>
      unit_point L l ι h5 μ hμ hg2 hg3 e N he hlN heN z (hT z hz).1 (hT z hz).2
  rw [← key, map_prod, norm_prod]
  simp only [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const, pow_mul]

end ReciprocityTheory.ChartRestriction.L1
end
end

