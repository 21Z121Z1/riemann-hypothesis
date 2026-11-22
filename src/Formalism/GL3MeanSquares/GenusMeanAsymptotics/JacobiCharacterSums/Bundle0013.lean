import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0012
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0009
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0004

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistB
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem coprime_of_cls {m₀ s a₀ b : ℕ} (ha : a₀.Coprime m₀) (hb : b ∈ clsB m₀ s a₀) : b.Coprime (m₀ * s) := by
  simp only [clsB, Finset.mem_filter, Finset.mem_range] at hb
  have hm : b.Coprime m₀ := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hb.2.1, ← Nat.gcd_rec, Nat.gcd_comm]
    exact ha
  exact Nat.Coprime.mul_right hm hb.2.2

private theorem sum_clsB_mul_mod_eq_sum {M : Type*} [AddCommMonoid M] (m₀ s a₀ u : ℕ) (hN : 0 < m₀ * s)
    (hu1 : u % m₀ = 1 % m₀) (hus : u.Coprime s) (f : ℕ → M) :
    ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s)) = ∑ b ∈ clsB m₀ s a₀, f b := by
  have hcm : ∀ x k : ℕ, Nat.Coprime x k ↔ Nat.Coprime (x % k) k := fun x k => by
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
  have hum : u.Coprime m₀ := by
    rw [hcm, hu1, ← hcm]
    exact Nat.coprime_one_left _
  have huN : u.Coprime (m₀ * s) := Nat.Coprime.mul_right hum hus
  have hmap : ∀ b ∈ clsB m₀ s a₀, (b * u) % (m₀ * s) ∈ clsB m₀ s a₀ := by
    intro b hb
    simp only [clsB, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨Nat.mod_lt _ hN, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m₀ s), Nat.mul_mod, hb.2.1, hu1, ← Nat.mul_mod, mul_one]
    · rw [hcm, Nat.mod_mod_of_dvd _ (dvd_mul_left s m₀), ← hcm]
      exact Nat.Coprime.mul hb.2.2 hus
  have hinj : Set.InjOn (fun b => (b * u) % (m₀ * s)) (clsB m₀ s a₀) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, clsB, Finset.mem_filter, Finset.mem_range] at hx hy
    have h := Nat.ModEq.cancel_right_of_coprime huN.symm (show x * u ≡ y * u [MOD m₀ * s] from hxy)
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h
  have himg : (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)) = clsB m₀ s a₀ :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hmap)
      (by rw [Finset.card_image_of_injOn hinj])
  calc ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s))
      = ∑ x ∈ (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)), f x := (Finset.sum_image hinj).symm
    _ = ∑ b ∈ clsB m₀ s a₀, f b := by rw [himg]

private theorem jacobiSym_mul_mod_eq_mul (m₀ s b u : ℕ) :
    jacobiSym (((b * u) % (m₀ * s) : ℕ) : ℤ) s = jacobiSym (b : ℤ) s * jacobiSym (u : ℤ) s := by
  rw [← jacobiSym.mul_left]
  apply jacobiSym.mod_left'
  push_cast
  exact Int.emod_emod_of_dvd _ (dvd_mul_left _ _)

private theorem exists_jacobiSym_neg_one_in_residue_class (m₀ s : ℕ) (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s)
    (hcop : m₀.Coprime s) :
    ∃ u : ℕ, u % m₀ = 1 % m₀ ∧ u.Coprime s ∧ jacobiSym (u : ℤ) s = -1 := by
  have hp : s.minFac.Prime := Nat.minFac_prime (by omega)
  haveI := Fact.mk hp
  haveI : NeZero s := ⟨by omega⟩
  obtain ⟨t, ht⟩ := Nat.minFac_dvd s
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    omega
  haveI : NeZero t := ⟨ht0⟩
  haveI : NeZero s.minFac := ⟨hp.ne_zero⟩
  have hp2 : s.minFac ≠ 2 := by
    intro h2
    rw [h2] at ht
    rw [ht] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul t)
  have hpt : s.minFac.Coprime t := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨v, hv⟩
    have hu := hsq s.minFac ⟨v, by rw [mul_assoc, ← hv]; exact ht⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp hu)
  have hmp : (m₀ * t).Coprime s.minFac :=
    Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.minFac_dvd s) hcop) hpt.symm
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod s.minFac)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  let c := Nat.chineseRemainder hmp 1 g.val
  have hc1 : (c : ℕ) ≡ 1 [MOD m₀ * t] := c.2.1
  have hc2 : (c : ℕ) ≡ g.val [MOD s.minFac] := c.2.2
  have hJ : jacobiSym ((c : ℕ) : ℤ) s = -1 := by
    have e1 : jacobiSym ((c : ℕ) : ℤ) s.minFac = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
      have hcg : (((c : ℕ) : ℤ) : ZMod s.minFac) = g := by
        rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc2, ZMod.natCast_zmod_val]
      rwa [hcg]
    have e2 : jacobiSym ((c : ℕ) : ℤ) t = 1 := by
      have hct : (c : ℕ) ≡ 1 [MOD t] := Nat.ModEq.of_mul_left m₀ hc1
      have h' : (((c : ℕ) % t : ℕ) : ℤ) = ((1 % t : ℕ) : ℤ) := congrArg _ hct
      push_cast at h'
      rw [jacobiSym.mod_left' h', jacobiSym.one_left]
    have hsplit : jacobiSym ((c : ℕ) : ℤ) s = jacobiSym ((c : ℕ) : ℤ) (s.minFac * t) := by rw [← ht]
    rw [hsplit, jacobiSym.mul_right, e1, e2]
    norm_num
  refine ⟨c, Nat.ModEq.of_mul_right t hc1, ?_, hJ⟩
  have hg1 : Int.gcd ((c : ℕ) : ℤ) s = 1 := by
    by_contra hne
    have h0 := jacobiSym.eq_zero_iff_not_coprime.mpr hne
    rw [hJ] at h0
    norm_num at h0
  rwa [Int.gcd_natCast_natCast] at hg1

theorem sum_jac_cls_eq_zero (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) :
    ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) = 0 := by
  have hN : 0 < m₀ * s := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨u, hu1, hus, hJu⟩ := exists_jacobiSym_neg_one_in_residue_class m₀ s h1 hodd hsq hcop
  have hre := sum_clsB_mul_mod_eq_sum m₀ s a₀ u hN hu1 hus (fun x => (jacobiSym (x : ℤ) s : ℝ))
  simp only [jacobiSym_mul_mod_eq_mul, hJu, Int.cast_mul, Int.cast_neg, Int.cast_one, mul_neg, mul_one,
    Finset.sum_neg_distrib] at hre
  linarith

theorem main_twist_bound (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (hm : 0 < m₀) (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) (X r : ℝ)
    (e : Option (DirichletCharacter ℂ (m₀ * s) × ℝ)) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (hli : 0 < liX X)
    (hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), e = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X) :
    |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP e b X| ≤
      2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| := by
  have hN : 0 < m₀ * s := Nat.pos_of_ne_zero (NeZero.ne _)
  have hφ : (0 : ℝ) < ((m₀ * s).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hN
  have hsum0 := sum_jac_cls_eq_zero m₀ s a₀ h1 hodd hsq hcop ha
  have hRHS : 0 ≤ 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| := by positivity
  rcases e with _ | ⟨χ, β⟩
  · simp only [mainAP]
    rw [← Finset.sum_mul, hsum0, zero_mul, abs_zero]
    simpa [mainAP] using hRHS
  · have hexp : ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP (some (χ, β)) b X =
        -(liX (X ^ β) / ((m₀ * s).totient : ℝ)) *
          ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re := by
      simp only [mainAP]
      rw [Finset.mul_sum]
      have key : ∀ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
          ((liX X - (χ (b : ZMod (m₀ * s))).re * liX (X ^ β)) / ((m₀ * s).totient : ℝ)) =
          (jacobiSym (b : ℤ) s : ℝ) * (liX X / ((m₀ * s).totient : ℝ)) +
          -(liX (X ^ β) / ((m₀ * s).totient : ℝ)) *
            ((jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re) := fun b _ => by ring
      rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, hsum0, zero_mul, zero_add]
    have hre1 : ∀ b : ℕ, |(χ (b : ZMod (m₀ * s))).re| ≤ 1 := fun b =>
      (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
    by_cases hc : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s →
        χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)
    · have hLb := hG χ β rfl hc
      have hS : |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re| ≤
          ((clsB m₀ s a₀).card : ℝ) := by
        calc _ ≤ ∑ b ∈ clsB m₀ s a₀, |(jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ b ∈ clsB m₀ s a₀, (1 : ℝ) := Finset.sum_le_sum fun b _ => by
              rw [abs_mul]
              have hj : |(jacobiSym (b : ℤ) s : ℝ)| ≤ 1 := by
                rcases jacobiSym.trichotomy (b : ℤ) s with h | h | h <;> simp [h]
              calc _ ≤ 1 * 1 := mul_le_mul hj (hre1 b) (abs_nonneg _) zero_le_one
                _ = 1 := one_mul 1
          _ = ((clsB m₀ s a₀).card : ℝ) := by simp
      have hlow : ∀ b ∈ clsB m₀ s a₀, liX X / (2 * ((m₀ * s).totient : ℝ)) ≤ |mainAP (some (χ, β)) b X| := by
        intro b _
        have h3 : (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) ≤ r * liX X := by
          calc (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) ≤ |(χ (b : ZMod (m₀ * s))).re * liX (X ^ β)| :=
                le_abs_self _
            _ = |(χ (b : ZMod (m₀ * s))).re| * |liX (X ^ β)| := abs_mul _ _
            _ ≤ 1 * |liX (X ^ β)| := mul_le_mul_of_nonneg_right (hre1 b) (abs_nonneg _)
            _ ≤ r * liX X := by linarith
        refine le_trans ?_ (le_abs_self _)
        simp only [mainAP]
        rw [div_le_div_iff₀ (by positivity) hφ]
        have h4 : liX X / 2 ≤ liX X - (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) := by nlinarith
        nlinarith
      rw [hexp, abs_mul, abs_neg, abs_div, abs_of_pos hφ]
      calc |liX (X ^ β)| / ((m₀ * s).totient : ℝ) *
            |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re|
          ≤ r * liX X / ((m₀ * s).totient : ℝ) * ((clsB m₀ s a₀).card : ℝ) :=
            mul_le_mul (div_le_div_of_nonneg_right hLb hφ.le) hS (abs_nonneg _) (by positivity)
        _ = 2 * r * ∑ b ∈ clsB m₀ s a₀, liX X / (2 * ((m₀ * s).totient : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp
        _ ≤ 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP (some (χ, β)) b X| :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlow) (by linarith)
    · push_neg at hc
      obtain ⟨u, hu1, hus, hne⟩ := hc
      have hpt : ∀ b : ℕ, (((jacobiSym (((b * u) % (m₀ * s) : ℕ) : ℤ) s : ℝ)) : ℂ) *
          χ ((((b * u) % (m₀ * s) : ℕ)) : ZMod (m₀ * s)) =
          (((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) *
            ((((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s))) := by
        intro b
        rw [jacobiSym_mul_mod_eq_mul, ZMod.natCast_mod, Nat.cast_mul, map_mul]
        push_cast
        ring
      have hre := sum_clsB_mul_mod_eq_sum m₀ s a₀ u hN hu1 hus
        (fun x => (((jacobiSym (x : ℤ) s : ℝ)) : ℂ) * χ (x : ZMod (m₀ * s)))
      simp only [hpt] at hre
      rw [← Finset.mul_sum] at hre
      have hgcd : Int.gcd (u : ℤ) s = 1 := by rw [Int.gcd_natCast_natCast]; exact hus
      have hc1 : (((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) ≠ 1 := by
        rcases jacobiSym.eq_one_or_neg_one hgcd with h | h
        · rw [h] at hne ⊢
          intro hh
          apply hne
          push_cast at hh ⊢
          simpa using hh
        · rw [h] at hne ⊢
          intro hh
          apply hne
          push_cast at hh ⊢
          linear_combination -hh
      have hT : ∑ b ∈ clsB m₀ s a₀, (((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s)) = 0 := by
        have h0 : ((((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) - 1) *
            ∑ b ∈ clsB m₀ s a₀, (((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s)) = 0 := by
          rw [sub_mul, hre, one_mul, sub_self]
        exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc1)
      have hS0 : ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re = 0 := by
        have h0 := congrArg Complex.re hT
        rw [Complex.re_sum] at h0
        simpa [Complex.re_ofReal_mul] using h0
      rw [hexp, hS0, mul_zero, abs_zero]
      exact hRHS

theorem twist_one (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (hm : 0 < m₀) (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) (X r k : ℝ)
    (e : Option (DirichletCharacter ℂ (m₀ * s) × ℝ)) (hX : 0 ≤ X) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hli : 0 < liX X) (hk : |k| ≤ 1 / 2)
    (hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - mainAP e b X| ≤ k * mainAP e b X)
    (hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), e = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X) :
    |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤
      (4 * r + 2 * |k|) * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) + X ^ (1 / 2 : ℝ) := by
  have hs : 0 < s := by omega
  obtain ⟨hd, hsumabs⟩ := twist_decomp m₀ s a₀ X hm hs hX (fun b => mainAP e b X) k hk hb
  beta_reduce at hd hsumabs
  have hmain := main_twist_bound m₀ s a₀ hm h1 hodd hsq hcop ha X r e hr0 hr hli hG
  have h2 : 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| ≤
      2 * r * (2 * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hsumabs (by linarith)
  have h3 := abs_sub_abs_le_abs_sub (∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ))
    (∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP e b X)
  nlinarith [hd, hmain, h2, h3, abs_nonneg k]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailFinal
section
open Complex Finset ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem box_tail_bound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxTailHyp ε C x₀ := by
  intro ε hε hε1
  obtain ⟨K, hK0, hK⟩ := tail_contour (ε / 1600) (by positivity) (by linarith)
  obtain ⟨CM, hCM0, hCM⟩ := tail_mertens
  obtain ⟨x₀, hx₀3, hnum⟩ := tail_num ε K hε hε1 hK0
  refine ⟨400 * CM + 1, x₀, ?_⟩
  intro x Q N _ χ hx hQlo hQhi hχ hgood
  obtain ⟨_, _, hNQ, hbox⟩ := hgood
  have hx3 : 3 ≤ x := le_trans hx₀3 hx
  have hx0 : 0 < x := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  have hlogQ1 : 1 ≤ Real.log Q := le_trans (Real.one_le_rpow (by linarith) (by positivity)) hQlo
  have hQ2 : 2 ≤ Q := by
    have : Real.exp 1 ≤ Q := by
      rw [← Real.exp_log hQ0]; exact Real.exp_le_exp.mpr hlogQ1
    linarith [Real.exp_one_gt_d9]
  have hnum' := hnum x Q hx hQ0 hQlo hQhi
  set z : ℝ := x ^ 400 with hz
  set η : ℝ := 1 / x ^ 2 with hη
  have hz1 : 1 ≤ z := one_le_pow₀ (by linarith)
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  have hzη : 0 < z * η := by positivity
  have hC := hK N χ Q z η hχ hQ2 hNQ hbox hz1 hη0 hη1
  have hD := tail_diff_schi χ z (z * η) hz1 hzη
  set P : ℂ := ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) with hP
  have htail : Formalism.HermitianLattices.ZeroFreeRegionGL2.tailL χ z = Formalism.ZeroFreeDirichlet.negLD χ 1 - P := by
    simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.tailL, Formalism.HermitianLattices.ZeroFreeRegionGL2.logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, hP]
  have hkey : ((z * η : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.negLD χ 1 - P) =
      -(Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) +
      (Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * P) := by ring
  have hnorm : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤
      (K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + ε / 1600) + z ^ 2 / Q)
        + z * η * (z * η + 1) * Real.log (z + z * η) / z) / (z * η) := by
    rw [le_div_iff₀ hzη]
    have h1 := congrArg norm hkey
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hzη.le] at h1
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ * (z * η) = z * η * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := mul_comm _ _
      _ = _ := h1
      _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        exact add_le_add hC hD
  have hfirst : ‖(x : ℂ) * Formalism.HermitianLattices.ZeroFreeRegionGL2.tailL χ z‖ ≤ x ^ ε := by
    rw [htail, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    refine le_trans ?_ hnum'
    exact mul_le_mul_of_nonneg_left hnorm hx0.le
  refine ⟨hfirst, ?_⟩

  have hz2 : 2 ≤ z := by
    have : (3 : ℝ) ≤ z := by
      rw [hz]; calc (3 : ℝ) ≤ x := hx3
        _ ≤ x ^ 400 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hPle : ‖P‖ ≤ CM * Real.log z := by
    refine le_trans (norm_sum_le _ _) (le_trans ?_ (hCM z hz2))
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχn : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛ : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    gcongr
    calc (Λ n : ℝ) * ‖χ (n : ZMod N)‖ ≤ (Λ n : ℝ) * 1 := by gcongr
      _ = Λ n := mul_one _
  have hlogz : Real.log z = 400 * Real.log x := by
    rw [hz, Real.log_pow]; norm_num
  have htail1 : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤ 1 := by
    have h2 : x * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤ x ^ ε := by
      have := hfirst
      rw [htail, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le] at this
      exact this
    have h3 : x ^ ε ≤ x := by
      calc x ^ ε ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hε1
        _ = x := Real.rpow_one x
    have h4 : x * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤ x * 1 := by linarith
    exact le_of_mul_le_mul_left h4 hx0
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hLD : Formalism.HermitianLattices.ZeroFreeRegionGL2.logDerivLAtOne χ = -(Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, neg_neg]
  rw [hLD, norm_neg]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1‖ = ‖P + (Formalism.ZeroFreeDirichlet.negLD χ 1 - P)‖ := by ring_nf
    _ ≤ ‖P‖ + ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := norm_add_le _ _
    _ ≤ CM * (400 * Real.log x) + 1 := by rw [← hlogz]; linarith
    _ ≤ (400 * CM + 1) * Real.log x := by nlinarith

end Formalism.HermitianLattices.Ext.BoxTail
end
end

