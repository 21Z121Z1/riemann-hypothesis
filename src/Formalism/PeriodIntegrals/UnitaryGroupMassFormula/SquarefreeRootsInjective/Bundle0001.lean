import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.ClaimOf

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.DivCount
section
open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

theorem divCount {g : ℕ} [Fact g.Prime] (r : ℕ) (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) (h : (ZMod g)[X]) (hh : h.Monic) :
    (T.filter (h ∣ ·)).card ≤ g ^ (r - h.natDegree) := by
  classical
  set k := r - h.natDegree
  let φ : (ZMod g)[X] → (Fin k → ZMod g) := fun f i => (f /ₘ h).coeff i
  have key : ∀ f ∈ T.filter (h ∣ ·), (f /ₘ h).Monic ∧ (f /ₘ h).natDegree = k ∧
      h * (f /ₘ h) = f := by
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfT, hdv⟩ := hf
    obtain ⟨hm, hd⟩ := hT f hfT
    have e1 : h * (f /ₘ h) = f := by
      have := modByMonic_add_div f h
      rw [(modByMonic_eq_zero_iff_dvd hh).2 hdv, zero_add] at this
      exact this
    refine ⟨?_, ?_, e1⟩
    · have hm' : (h * (f /ₘ h)).Monic := by rw [e1]; exact hm
      exact hh.of_mul_monic_left hm'
    · rw [natDegree_divByMonic f hh, hd]
  have hinj : Set.InjOn φ (T.filter (h ∣ ·)) := by
    intro f hf f' hf' heq
    obtain ⟨m1, d1, e1⟩ := key f hf
    obtain ⟨m2, d2, e2⟩ := key f' hf'
    have hq : f /ₘ h = f' /ₘ h := by
      ext n
      rcases lt_trichotomy n k with hn | hn | hn
      · exact congrFun heq ⟨n, hn⟩
      · subst hn
        have a1 := m1.coeff_natDegree
        have a2 := m2.coeff_natDegree
        rw [d1] at a1; rw [d2] at a2
        rw [a1, a2]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
    rw [← e1, ← e2, hq]
  calc (T.filter (h ∣ ·)).card ≤ (Finset.univ : Finset (Fin k → ZMod g)).card :=
        Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _) hinj
    _ = g ^ k := by simp [ZMod.card]

end PI.SqfRootsInj.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.TwoPowCardPrimeFactorsLe
section
open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

open PI.SqfLab

theorem lp_pow_four_le {g r e ℓ : ℕ} (hℓ : ℓ.Prime) (hB : ℓ ∉ BB r g) (h1 : 1 ≤ e)
    (h2 : e ≤ r) : (Lp g e ℓ) ^ 4 ≤ g ^ e := by
  by_contra h
  push_neg at h
  apply hB
  right
  refine ⟨e, h1, h2, hℓ, ?_⟩
  unfold Lp at h
  rwa [← pow_mul, mul_comm] at h

theorem two_pow_card_primeFactors_le {n : ℕ} (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

theorem card_nthRoots_toFinset_le {K : Type*} [Field K] (N : ℕ) (a : K) :
    (nthRoots N a).toFinset.card ≤ N :=
  (Multiset.toFinset_card_le _).trans (card_nthRoots N a)

theorem card_roots_X_pow_sub_X_le {K : Type*} [Field K] (M : ℕ) (hM : 2 ≤ M) :
    ((X ^ M - X : K[X]).roots.toFinset).card ≤ M := by
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp <;> omega

end PI.SqfRootsInj.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.WitBase
section
open Polynomial

noncomputable section

namespace PI.SqfRootsInj.W

open PI.SqfLab

theorem pow_eq_part_pow {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M)
    (hx : 0 < orderOf x) :
    x ^ (ℓ ^ (orderOf x).factorization ℓ) =
      (primeToPart ℓ x) ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  have hdvd : ℓ ^ (orderOf x).factorization ℓ ∣ orderOf x := Nat.ordProj_dvd _ ℓ
  have hmpos : 0 < orderOf x / ℓ ^ (orderOf x).factorization ℓ :=
    Nat.div_pos (Nat.le_of_dvd hx hdvd) (pow_pos hℓ.pos _)
  have hcop : Nat.Coprime (ℓ ^ (orderOf x).factorization ℓ)
      (orderOf x / ℓ ^ (orderOf x).factorization ℓ) :=
    (Nat.coprime_ordCompl hℓ hx.ne').pow_left _
  haveI : NeZero (orderOf x / ℓ ^ (orderOf x).factorization ℓ) := ⟨hmpos.ne'⟩
  have hu : ((ℓ ^ (orderOf x).factorization ℓ *
      (((ℓ ^ (orderOf x).factorization ℓ : ℕ) :
        ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ))⁻¹).val : ℕ) :
        ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ)) = ((1 : ℕ) : ZMod _) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  rw [ZMod.natCast_eq_natCast_iff] at hu
  have hmod := Nat.ModEq.mul_left' (ℓ ^ (orderOf x).factorization ℓ) hu
  rw [Nat.mul_div_cancel' hdvd, mul_one] at hmod
  unfold primeToPart
  rw [← pow_mul, ← pow_mod_orderOf, mul_comm _ (ℓ ^ (orderOf x).factorization ℓ), ← hmod,
    pow_mod_orderOf]

theorem pow_eq_part_pow_of_dvd {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M) (N : ℕ)
    (hN : N ≠ 0) (hxN : orderOf x ∣ N) :
    x ^ (ℓ ^ padicValNat ℓ N) = (primeToPart ℓ x) ^ (ℓ ^ padicValNat ℓ N) := by
  have hx : 0 < orderOf x := Nat.pos_of_ne_zero fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hxN))
  have hle : (orderOf x).factorization ℓ ≤ padicValNat ℓ N := by
    rw [← Nat.factorization_def N hℓ]
    exact (Nat.factorization_le_iff_dvd hx.ne' hN).2 hxN ℓ
  have key := pow_eq_part_pow ℓ hℓ x hx
  rw [← Nat.add_sub_cancel' hle, pow_add, pow_mul, pow_mul, key]

theorem pow_card_minpoly {g : ℕ} [Fact g.Prime] (w : Fbar g) :
    w ^ (g ^ (minpoly (ZMod g) w).natDegree) = w := by
  have hw : IsIntegral (ZMod g) w := Algebra.IsIntegral.isIntegral w
  haveI : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {w}) :=
    IntermediateField.adjoin.finiteDimensional hw
  haveI : Finite (IntermediateField.adjoin (ZMod g) {w}) :=
    Module.finite_of_finite (ZMod g)
  letI : Fintype (IntermediateField.adjoin (ZMod g) {w}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod g) {w}) =
      g ^ (minpoly (ZMod g) w).natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hw]
  have h := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen (ZMod g) w)
  rw [hcard] at h
  have h2 := congrArg Subtype.val h
  simpa using h2

end PI.SqfRootsInj.W
end
end

