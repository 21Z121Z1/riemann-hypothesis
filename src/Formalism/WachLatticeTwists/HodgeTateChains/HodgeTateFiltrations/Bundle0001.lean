import Formalism.WachLatticeTwists.HodgeTateChains.Bundle0001
import Formalism.WindowSums.AnnihilatorPolynomials.Bundle0002
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Complete
import Formalism.WachLatticeTwists.HodgeTateChains.Statement
import Formalism.WindowSums.AnnihilatorPolynomials.Bundle0001

-- bundled from Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.GeomFact
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem kappa : StatKappa := by
  intro ℓ hℓ s ρ hs h2 hρ hρs j hj1 hjs
  have := Fact.mk hℓ
  have hv : padicValNat ℓ j ≤ s := by
    refine le_trans (padicValNat_le_nat_log j) ?_
    calc Nat.log ℓ j ≤ Nat.log ℓ (ℓ ^ s) := Nat.log_mono_right hjs
      _ = s := Nat.log_pow hℓ.one_lt s
  have hvq : (padicValNat ℓ j : ℚ) ≤ s := by exact_mod_cast hv
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · interval_cases j
    · simp only [padicValNat.one]; push_cast; linarith
    · have hv2 : padicValNat ℓ 2 + 1 ≤ s := by
        by_cases hl : ℓ = 2
        · subst hl
          have : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
          have := h2 rfl
          omega
        · have : padicValNat ℓ 2 = 0 := by
            apply padicValNat.eq_zero_of_not_dvd
            intro hd
            exact hl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd)
          omega
      have hv2q : (padicValNat ℓ 2 : ℚ) + 1 ≤ s := by exact_mod_cast hv2
      push_cast
      linarith
  · have hj : (3 : ℚ) ≤ j := by exact_mod_cast h3
    nlinarith

theorem nilDiv : StatNilDiv := by
  intro La _ a b M q hM hnil
  have hb : b = a + (b - a) := by ring
  have hd : (b - a) ^ M = 0 := by
    have : b - a = -(a - b) := by ring
    rw [this, neg_pow, hnil, mul_zero]
  rw [hb, add_pow]
  apply Finset.dvd_sum
  intro m hm
  rw [Finset.mem_range] at hm
  by_cases hq : q ≤ m
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow a hq) _) _
  · have hle : M ≤ q + M - 1 - m := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, hd]
    simp

lemma geom_fact {R : Type} [CommRing R] (x : R) (a b : ℕ) :
    ∑ k ∈ Finset.range (a * b), x ^ k
      = (∑ k ∈ Finset.range a, x ^ k) * ∑ k ∈ Finset.range b, (x ^ a) ^ k := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, ← pow_mul, mul_comm]

theorem charSum : StatCharSum := by
  intro R _ ℓ ζ h0 hζ h1 s j i n hjs
  have hpow : ∀ t i, ζ (i + t) ^ (ℓ ^ t) = ζ i := by
    intro t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      rw [pow_succ', pow_mul, ← add_assoc, hζ, ih]
  have hsplit : ∀ k, ζ i ^ (n + ℓ ^ j * k) = ζ i ^ n * (ζ i ^ (ℓ ^ j)) ^ k := by
    intro k; rw [pow_add, pow_mul]
  constructor
  · intro hij
    have hone : ζ i ^ (ℓ ^ j) = 1 := by
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hij
      have := hpow i 0
      rw [zero_add, h0] at this
      rw [pow_add, pow_mul, this, one_pow]
    simp only [hsplit, hone, one_pow, mul_one, Finset.sum_const, Finset.card_range]
  · intro hji his
    obtain ⟨t, rfl⟩ : ∃ t, i = j + (t + 1) := ⟨i - j - 1, by omega⟩
    have hy : ζ (j + (t + 1)) ^ (ℓ ^ j) = ζ (t + 1) := by
      rw [add_comm j (t + 1)]; exact hpow j (t + 1)
    simp only [hsplit, hy]
    rw [← Finset.mul_sum]
    obtain ⟨p, hp⟩ : ∃ p, s - j = t + (1 + p) := ⟨s - j - t - 1, by omega⟩
    have hz : ζ (t + 1) ^ (ℓ ^ t) = ζ 1 := by rw [add_comm t 1]; exact hpow t 1
    rw [hp, pow_add, geom_fact, hz, pow_add, pow_one, geom_fact, h1, zero_mul, mul_zero, mul_zero]

theorem rValues : StatRValues := by
  intro ℓ _ u s hs h2 hu e he abelian₂ _ _ L _ _ V β hV ω
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hu (e : ℤ) (by omega)
  rw [zpow_natCast, padicValInt.of_nat] at hval
  rw [zpow_natCast] at hne
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ]ˣ, (((u ^ e : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1)
      = (c : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ e) := by
    have h := PadicInt.unitCoeff_spec hne
    rw [hval] at h
    exact ⟨_, h⟩
  obtain ⟨la, hla1, hla⟩ := hV (fun j =>
    ((ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j) - (if j = 1 then s - 1 else s - j + 1))) •
      (β j).symm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ω j))
  refine ⟨la, fun j hj1 hjs => ?_⟩
  have hVj : V j la = ((ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j))) •
      (β j).symm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ω j) := by
    by_cases h1 : j = 1
    · subst h1
      rw [hla1, if_pos rfl, smul_smul, ← pow_add]
      congr 2
      have : (e + 1) * (s - 1) = e * (s - 1) + (s - 1) := by ring
      omega
    · rw [hla j (by omega) hjs, if_neg h1, smul_smul, ← pow_add]
      congr 2
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hjs
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      have e1 : j' + 2 + p - (j' + 2) = p := by omega
      have e2 : j' + 2 + p - 1 = j' + p + 1 := by omega
      rw [e1, e2]
      have e3 : (e + 1) * (j' + p + 1) = e * p + (p + 1) + (e * j' + e + j') := by ring
      omega
  have hle : e * (s - j) ≤ (e + 1) * (s - 1) := by
    calc e * (s - j) ≤ e * (s - 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (e + 1) * (s - 1) := Nat.mul_le_mul_right _ (by omega)
  rw [hVj, map_smul, LinearEquiv.apply_symm_apply, hc, smul_smul, smul_smul, smul_smul]
  congr 1
  have hexp : (e + 1) * (s - 1) + s + padicValNat ℓ e
      = (s + padicValNat ℓ e) + (e * (s - j) + ((e + 1) * (s - 1) - e * (s - j))) := by omega
  rw [hexp, pow_add, pow_add]
  have hcc : (c : ℤ_[ℓ]) * ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := Units.mul_inv c
  linear_combination ((ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ e) * ((ℓ : ℤ_[ℓ]) ^ (e * (s - j)) *
    (ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j)))) * hcc

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
end
end

-- bundled from Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.InjectivityPassesToCompletion
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem injectivity_passes_to_completion : InjectivityPassesToCompletion := by
  intro R _ Xm _ _ ϖ z hc hz X0 g hdense hsat hstab hinj0 hsur0

  have huniq : ∀ p ∈ X0, ∀ q ∈ X0, g p - p = g q - q → p = q := by
    intro p hp q hq h
    have h1 : g (p - q) = p - q := by
      rw [map_sub, sub_eq_sub_iff_add_eq_add, add_comm (p) (g q)]
      have := sub_eq_sub_iff_add_eq_add.1 h
      rw [this]
    exact sub_eq_zero.1 (hinj0 _ (X0.sub_mem hp hq) h1)

  have key : ∀ (n : ℕ) (v' : Xm) (y : Xm), (ϖ ^ n) • v' ∈ X0 → y ∈ X0 →
      z • ((ϖ ^ n) • v') = g y - y → ∃ t, y = (ϖ ^ n) • t := by
    intro n v' y hv hy hzy
    obtain ⟨t, ht, hvt⟩ := hsat n v' hv
    obtain ⟨yt, hyt, hzt⟩ := hsur0 t ht
    refine ⟨yt, huniq _ hy _ (X0.smul_mem _ hyt) ?_⟩
    rw [← hzy, hvt, map_smul, ← smul_sub, ← hzt, smul_comm]
  constructor
  · intro x hx
    apply hz
    apply haus_of ϖ hc
    intro n
    obtain ⟨x0, hx0, x', hxx⟩ := hdense x n
    have h1 : g x0 - x0 = (ϖ ^ n) • (x' - g x') := by
      have h2 : g x - x = 0 := sub_eq_zero.2 hx
      rw [hxx, map_add, map_smul] at h2
      rw [smul_sub]
      have h3 : g x0 - x0 = (g x0 + ϖ ^ n • g x' - (x0 + ϖ ^ n • x')) + (ϖ ^ n • x' - ϖ ^ n • g x') := by
        abel
      rw [h3, h2, zero_add]
    have hmem : (ϖ ^ n) • (x' - g x') ∈ X0 := by
      rw [← h1]; exact X0.sub_mem (hstab _ hx0) hx0
    obtain ⟨t, ht⟩ := key n (x' - g x') (z • x0) hmem (X0.smul_mem _ hx0)
      (by rw [← h1, map_smul, smul_sub])
    refine ⟨t + z • x', ?_⟩
    rw [hxx, smul_add, ht, smul_add, smul_comm z (ϖ ^ n)]
  · intro x
    choose a ha b hab using hdense x
    choose y hy hzy using fun n => hsur0 (a n) (ha n)
    have hcau : ∀ {m n : ℕ}, m ≤ n →
        y m ≡ y n [SMOD ((Ideal.span {ϖ}) ^ m • (⊤ : Submodule R Xm))] := by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top]
      have h1 : a m - a n = (ϖ ^ m) • ((ϖ ^ (n - m)) • b n - b m) := by
        rw [smul_sub, smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]
        have e1 := hab m
        have e2 := hab n
        have e3 : a m + ϖ ^ m • b m = a n + ϖ ^ n • b n := by rw [← e1, ← e2]
        rw [sub_eq_sub_iff_add_eq_add, e3, add_comm]
      have hmem : (ϖ ^ m) • ((ϖ ^ (n - m)) • b n - b m) ∈ X0 := by
        rw [← h1]; exact X0.sub_mem (ha m) (ha n)
      exact key m _ (y m - y n) hmem (X0.sub_mem (hy m) (hy n))
        (by rw [← h1, smul_sub, hzy m, hzy n, map_sub]; abel)
    obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcau
    refine ⟨L, ?_⟩
    apply sub_eq_zero.1
    apply haus_of ϖ hc
    intro n
    have h1 := hL n
    rw [SModEq.sub_mem, mem_pow_smul_top] at h1
    obtain ⟨t, ht⟩ := h1
    have hLy : L = y n - ϖ ^ n • t := by rw [← ht]; abel
    refine ⟨z • b n + (g t - t), ?_⟩
    rw [hLy, map_sub, map_smul]
    conv_lhs => rw [hab n]
    rw [smul_add, hzy n, smul_add, smul_sub, smul_comm z (ϖ ^ n)]
    abel

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
end
end

-- bundled from Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem minimal_exponent_attained : MinimalExponentAttained := by
  intro ℓ hℓ H0
  have hne : {n : ℕ | H0 ≤ ℓ ^ n * (ℓ - 1)}.Nonempty := by
    refine ⟨H0, ?_⟩
    have h1 : H0 < ℓ ^ H0 := Nat.lt_pow_self hℓ.one_lt
    have h2 : 1 ≤ ℓ - 1 := by have := hℓ.two_le; omega
    show H0 ≤ ℓ ^ H0 * (ℓ - 1)
    nlinarith
  refine ⟨Nat.sInf_mem hne, fun n hn => ?_⟩
  have := Nat.notMem_of_lt_sInf hn
  simpa using this

lemma ceilE_spec (d e : ℕ) : e ≤ ceilE (d + 2) e * (d + 1) ∧ ceilE (d + 2) e * (d + 1) < e + (d + 1) := by
  unfold ceilE
  have e1 : d + 2 - 1 = d + 1 := rfl
  rw [e1]
  have h1 := Nat.div_add_mod (e + (d + 1) - 1) (d + 1)
  have h2 := Nat.mod_lt (e + (d + 1) - 1) (Nat.succ_pos d)
  set q := (e + (d + 1) - 1) / (d + 1)
  set r := (e + (d + 1) - 1) % (d + 1)
  have h3 : (d + 1) * q = q * (d + 1) := Nat.mul_comm _ _
  constructor <;> omega

lemma ceilE_le_floor (d e : ℕ) : ceilE (d + 2) e ≤ e / (d + 2 - 1) + 1 := by
  have e1 : d + 2 - 1 = d + 1 := rfl
  rw [e1]
  have h := (ceilE_spec d e).2
  have h1 := Nat.div_add_mod e (d + 1)
  have h2 : e % (d + 1) < d + 1 := Nat.mod_lt e (Nat.succ_pos d)
  by_contra hc
  push Not at hc
  have : (e / (d + 1) + 2) * (d + 1) ≤ ceilE (d + 2) e * (d + 1) := Nat.mul_le_mul_right _ hc
  generalize e / (d + 1) = Q at *
  generalize e % (d + 1) = R at *
  nlinarith

lemma ceilE_le_self (d e : ℕ) : ceilE (d + 2) e ≤ e := by
  have h := (ceilE_spec d e).2
  by_contra hc
  push Not at hc
  have : (e + 1) * (d + 1) ≤ ceilE (d + 2) e * (d + 1) := Nat.mul_le_mul_right _ hc
  nlinarith

theorem ceil : StatCeil := by
  intro ℓ hℓ e
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩
  have hD : (((d + 2 : ℕ) : ℚ) - 1) = ((d + 1 : ℕ) : ℚ) := by push_cast; ring
  have hpos : (0 : ℚ) < ((d + 1 : ℕ) : ℚ) := by positivity
  obtain ⟨h1, h2⟩ := ceilE_spec d e
  refine ⟨?_, ?_, ceilE_le_floor d e⟩
  · rw [hD, div_le_iff₀ hpos]; exact_mod_cast h1
  · rw [hD, ← sub_lt_iff_lt_add, lt_div_iff₀ hpos]
    have : ((ceilE (d + 2) e * (d + 1) : ℕ) : ℚ) < ((e + (d + 1) : ℕ) : ℚ) := by exact_mod_cast h2
    push_cast at this ⊢
    linarith

theorem rVal : StatRVal := by
  intro ℓ _ w m hm h2 hw U i
  have key := (Formalism.WindowSums.valProd_of Formalism.WindowSums.valuation_zpow_sub_one ℓ w m hm h2 hw).2
    ((U.erase i).map ⟨fun a => a - i, sub_left_injective⟩) (by
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
      intro a ha h0
      exact (Finset.mem_erase.1 ha).1 (by omega))
  have hev : (Rpoly ℓ w U i).eval 1 =
      ∏ a ∈ U.erase i, (1 - ((w ^ (-(a - i)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
    unfold Rpoly
    rw [eval_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [neg_sub]
  rw [Finset.prod_map, Finset.sum_map, Finset.card_map] at key
  simp only [Function.Embedding.coeFn_mk] at key
  rw [hev]
  refine ⟨key.1, ?_⟩
  rw [key.2]
  unfold rI
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]

theorem binom : StatBinom := by
  intro ℓ hℓ b k hb hk hkl
  have hle : k ≤ ℓ ^ b := le_trans hkl.le (Nat.pow_le_pow_right hℓ.pos (by omega))
  have h := hℓ.emultiplicity_choose_prime_pow hle hk.ne'
  have hm : multiplicity ℓ k + 2 ≤ b := by
    by_contra hc
    push Not at hc
    have h1 : ℓ ^ (b - 1) ∣ k :=
      dvd_trans (pow_dvd_pow ℓ (by omega)) (pow_multiplicity_dvd ℓ k)
    exact absurd (Nat.le_of_dvd hk h1) (by omega)
  apply pow_dvd_of_le_emultiplicity
  rw [h]
  exact_mod_cast (by omega : 2 ≤ b - multiplicity ℓ k)

theorem valNN : StatValNN := by
  intro ℓ hℓ s n i j hs hij
  have hl2 : (2 : ℚ) ≤ ℓ := by exact_mod_cast hℓ.two_le
  have hD : (0 : ℚ) < (ℓ : ℚ) - 1 := by linarith
  have hP : (1 : ℚ) ≤ (ℓ : ℚ) ^ (s + n - 1) := one_le_pow₀ (by linarith)
  have hPD : (1 : ℚ) ≤ (ℓ : ℚ) ^ (s + n - 1) * ((ℓ : ℚ) - 1) := by nlinarith
  constructor
  · have hq : (i : ℚ) + j = ℓ * (ℓ : ℚ) ^ (s + n - 1) := by
      have : s + n = (s + n - 1) + 1 := by omega
      rw [this, pow_succ] at hij
      have h' : ((i + j : ℕ) : ℚ) = ((ℓ ^ (s + n - 1) * ℓ : ℕ) : ℚ) := by rw [hij]
      push_cast at h'
      linarith
    have h1 : (ℓ : ℚ) / ((ℓ : ℚ) - 1) =
        ((i : ℚ) + j) / ((ℓ : ℚ) ^ (s + n - 1) * ((ℓ : ℚ) - 1)) := by
      rw [hq]; field_simp
    rw [h1, add_div]
    have : (i : ℚ) / ((ℓ : ℚ) ^ (s + n - 1) * ((ℓ : ℚ) - 1)) ≤ i :=
      div_le_self (by positivity) hPD
    linarith
  · apply lt_min
    · have : 1 / ((ℓ : ℚ) - 1) ≤ 1 := by rw [div_le_one hD]; linarith
      linarith
    · exact div_lt_div_of_pos_right (by linarith) hD

lemma val_factorial_pred (ℓ : ℕ) (hℓ : ℓ.Prime) (e : ℕ) (he : 1 ≤ e) :
    padicValNat ℓ e.factorial = padicValNat ℓ e + padicValNat ℓ (e - 1).factorial := by
  have := Fact.mk hℓ
  rw [← Nat.mul_factorial_pred (by omega : e ≠ 0),
    padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]

theorem betaCount : StatBetaCount := by
  intro ℓ hℓ s e he
  rw [val_factorial_pred ℓ hℓ e he]
  unfold beta
  rw [if_neg (by omega)]
  push_cast
  ring

theorem iBound : StatIBound := by
  intro ℓ hℓ s e
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩
  have h := ceilE_le_self d e
  unfold beta
  split_ifs with h0
  · subst h0
    have : ceilE (d + 2) 0 = 0 := by omega
    rw [this]; push_cast; omega
  · have : (ceilE (d + 2) e : ℤ) ≤ e := by exact_mod_cast h
    have h3 : (0 : ℤ) ≤ padicValNat (d + 2) (e - 1).factorial := by positivity
    linarith

lemma cPrime_eq (ℓ : ℕ) (hℓ : ℓ.Prime) (s e : ℕ) :
    cPrime ℓ s e = e * (s + 1) + padicValNat ℓ e.factorial := by
  have := Fact.mk hℓ
  unfold cPrime
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h1 : ∑ i ∈ Finset.range e, padicValNat ℓ (e - i) = padicValNat ℓ e.factorial := by
    have hr := Finset.sum_range_reflect (fun j => padicValNat ℓ (j + 1)) e
    have h2 : ∑ j ∈ Finset.range e, padicValNat ℓ (j + 1) = padicValNat ℓ e.factorial := by
      clear hr
      induction e with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
          padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
        ring
    rw [← h2, ← hr]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    congr 1
    omega
  rw [h1]; ring

theorem aCount : StatACount := by
  intro ℓ hℓ s e
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩
  refine ⟨cPrime_eq _ hℓ s e, ?_, ?_⟩
  · rw [cPrime_eq _ hℓ s e]
    unfold beta aTB
    split_ifs with h0
    · subst h0
      have : ceilE (d + 2) 0 = 0 := by have := ceilE_le_self d 0; omega
      rw [this]; simp
    · rw [val_factorial_pred _ hℓ e (by omega)]
      push_cast
      ring
  · unfold aTB
    split_ifs with h0
    · subst h0
      generalize 0 / (d + 2 - 1) = c
      omega
    · have := ceilE_le_floor d e
      omega

theorem cTBTable : StatCTBTable := by
  intro ℓ hℓ s m e gK U
  have := Fact.mk hℓ
  have h1 : cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s)) = (m - s) + cM ℓ m U 0 ((e : ℤ) + 1) := by
    unfold cLL; rw [padicValNat.prime_pow]
  refine ⟨h1, ?_⟩
  have h2 := (aCount ℓ hℓ s e).2.2
  unfold cTB cTBof
  omega

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
end
end

