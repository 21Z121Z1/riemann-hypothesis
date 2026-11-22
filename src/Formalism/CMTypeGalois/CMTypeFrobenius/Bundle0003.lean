import Mathlib
import Formalism.CMTypeGalois.StatementField

-- bundled from Formalism.CMTypeGalois.CMTypeFrobenius.HostInertia
section
open NumberField Ideal

noncomputable section

namespace Formalism.Q3

theorem hostIn_intCast_mem_iff {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] (n : ℤ) :
    (n : 𝓞 E) ∈ P ↔ (p : ℤ) ∣ n := by
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}), Ideal.under_def,
    Ideal.mem_comap, eq_intCast]

theorem hostIn_card (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (P.inertia Gal(E/ℚ)) = P.ramificationIdx ℤ := by
  have : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  rw [card_inertia_eq_ramificationIdxIn (G := Gal(E/ℚ)) (span {(p : ℤ)}) P,
    ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(E/ℚ)]

theorem hostIn_galSign_one {E : Type} [Field E] [Algebra ℚ E] (α : Fin 3 → E) :
    galSign α (1 : Gal(E/ℚ)) = 1 := by
  funext j
  simp [galSign]

theorem hostIn_A (q : Fin 3 → ℕ) {E : Type} [Field E] [NumberField E] (α : Fin 3 → E)
    (hα : IsHost q α) (j : Fin 3) :
    ∃ A : 𝓞 E, (A : E) = α j ∧ A ^ 2 = ((-(q j : ℤ) : ℤ) : 𝓞 E) := by
  have hsq : α j ^ 2 = ((-(q j : ℤ) : ℤ) : E) := hα.1 j
  have hint : IsIntegral ℤ (α j) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hsq, ← eq_intCast (algebraMap ℤ E)]
    exact isIntegral_algebraMap
  refine ⟨⟨α j, hint⟩, rfl, ?_⟩
  apply RingOfIntegers.coe_injective
  simp only [map_intCast]
  exact hsq.trans (by push_cast; rfl)

theorem hostIn_key (hG : MQGalois) (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (p : ℕ) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ))
    (hσ : ∀ x : 𝓞 E, σ • x - x ∈ P) (j : Fin 3) (hj : galSign α σ j = -1) :
    (p : ℤ) ∣ (q j : ℤ) := by
  have hne : ∀ l, (-(q l : ℤ)) ≠ 0 := fun l => by
    have := (hq.1 l).1.pos
    omega
  have hsq : α j ^ 2 = ((-(q j : ℤ) : ℤ) : E) := hα.1 j
  have hσα : σ (α j) = -α j := by
    have := (hG 3 E _ α hα hne).2.1 σ j
    rw [this, hj]
    simp
  obtain ⟨c, hc⟩ : ∃ c : ℤ, -(q j : ℤ) = 4 * c + 1 :=
    ⟨(-(q j : ℤ) - 1) / 4, by have := (hq.1 j).2; omega⟩
  have hcE : ((-(q j : ℤ) : ℤ) : E) = 4 * c + 1 := by exact_mod_cast hc
  obtain ⟨ω, hωdef⟩ : ∃ ω : E, ω = (1 + α j) / 2 := ⟨_, rfl⟩
  have hω2 : ω ^ 2 = ω + (c : E) := by
    rw [hωdef]
    linear_combination (1 / 4 : E) * hsq + (1 / 4 : E) * hcE
  have hωint : IsIntegral ℤ ω := by
    refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
    · apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X_add_C]
      norm_num
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
        Polynomial.eval₂_X_pow, hω2]
      simp
  obtain ⟨W, hWcoe⟩ : ∃ W : 𝓞 E, (W : E) = ω := ⟨⟨ω, hωint⟩, rfl⟩
  obtain ⟨A, hAcoe, hA2⟩ := hostIn_A q α hα j
  have hσW : σ • W - W = -A := by
    apply RingOfIntegers.coe_injective
    show σ (W : E) - (W : E) = -(A : E)
    rw [hWcoe, hAcoe, hωdef, map_div₀, map_add, map_one, hσα]
    have h2 : σ (2 : E) = 2 := map_ofNat σ 2
    rw [h2]
    ring
  have hAP : A ∈ P := by
    have := P.neg_mem_iff.mpr (hσW ▸ hσ W)
    simpa using this
  have hqP : ((-(q j : ℤ) : ℤ) : 𝓞 E) ∈ P := by
    rw [← hA2]
    exact P.pow_mem_of_mem hAP 2 (by norm_num)
  rw [hostIn_intCast_mem_iff p P] at hqP
  exact dvd_neg.mp hqP

theorem hostIn_ram_ne_one (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (i : Fin 3) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(q i : ℤ)})] :
    P.ramificationIdx ℤ ≠ 1 := by
  have hq0 : (q i : ℤ) ≠ 0 := by exact_mod_cast (hq.1 i).1.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(q i : ℤ)}) P (by simpa using (hq.1 i).1.ne_zero)]
  have hmemq : ((q i : ℤ) : 𝓞 E) ∈ P := (hostIn_intCast_mem_iff (q i) P _).mpr dvd_rfl
  have hmap : map (algebraMap ℤ (𝓞 E)) (span {(q i : ℤ)}) = span {((q i : ℤ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, eq_intCast]
  rw [Ideal.ramificationIdx'_ne_one_iff
      (by rw [hmap, Ideal.span_le, Set.singleton_subset_iff]; exact hmemq),
    hmap, Ideal.span_le, Set.singleton_subset_iff]
  obtain ⟨A, -, hA2⟩ := hostIn_A q α hα i
  have hA2P : A ^ 2 ∈ P := by
    rw [hA2, Int.cast_neg]
    exact P.neg_mem_iff.mpr hmemq
  have hAP : A ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem 2 hA2P
  have : ((q i : ℤ) : 𝓞 E) = -(A * A) := by
    rw [← pow_two, hA2, Int.cast_neg, neg_neg]
  show ((q i : ℤ) : 𝓞 E) ∈ P ^ 2
  rw [this, pow_two]
  exact (P * P).neg_mem_iff.mpr (Ideal.mul_mem_mul hAP hAP)

theorem hostInertia_of (hH : HostGalois) (hG : MQGalois) : HostInertia := by
  intro q hq E _ _ α hα i P _ _ σ
  have hGal := hH q hq E α hα
  have : IsGalois ℚ E := hGal.1
  have hinj := hGal.2.2.1.1
  have h1 : galSign α (1 : Gal(E/ℚ)) = 1 := hostIn_galSign_one α
  have hfwd : ∀ τ : Gal(E/ℚ), (∀ x : 𝓞 E, τ • x - x ∈ P) →
      (galSign α τ = 1 ∨ galSign α τ = e3 i) := by
    intro τ hτ
    have hoth : ∀ j, j ≠ i → galSign α τ j = 1 := by
      intro j hji
      rcases Int.units_eq_one_or (galSign α τ j) with h | h
      · exact h
      · exfalso
        have hd := hostIn_key hG q hq E α hα (q i) P τ hτ j h
        have := (Nat.prime_dvd_prime_iff_eq (hq.1 i).1 (hq.1 j).1).mp (by exact_mod_cast hd)
        exact hji (hq.2 this).symm
    rcases Int.units_eq_one_or (galSign α τ i) with h | h
    · left
      funext j
      by_cases hji : j = i
      · subst hji
        simpa using h
      · rw [hoth j hji]
        rfl
    · right
      funext j
      by_cases hji : j = i
      · subst hji
        simp [e3, h]
      · simp [e3, hji, hoth j hji]
  refine ⟨hfwd σ, fun h => ?_⟩
  rcases h with h | h
  · have : σ = 1 := hinj (h.trans h1.symm)
    subst this
    intro x
    simp
  · by_contra hn
    have hbot : P.inertia Gal(E/ℚ) = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      rw [Subgroup.mem_bot]
      rcases hfwd τ hτ with h' | h'
      · exact hinj (h'.trans h1.symm)
      · have := hinj (h'.trans h.symm)
        subst this
        exact absurd hτ hn
    have : Fact (q i).Prime := ⟨(hq.1 i).1⟩
    have hc := hostIn_card E (q i) P
    rw [hbot, Subgroup.card_bot] at hc
    exact hostIn_ram_ne_one q hq E α hα i P hc.symm

end Formalism.Q3
end
end

-- bundled from Formalism.CMTypeGalois.CMTypeFrobenius.HostMu
section
open NumberField Polynomial

noncomputable section

namespace Formalism.Q3

namespace CMRootsOfUnity

variable {q : Fin 3 → ℕ}

lemma not_sq_d (hq : Hyp3 q) (d : ℤ) (S : Finset (Fin 3)) (hS : S.Nonempty ∨ d < 0)
    (hdq : ∀ i, ¬ (q i : ℤ) ∣ d) :
    ¬ IsSquare ((d : ℚ) * ∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by
  classical
  rw [← Int.cast_prod, ← Int.cast_mul, Rat.isSquare_intCast_iff]
  rintro ⟨r, hr⟩
  rcases S.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
  · rcases hS with ⟨x, hx⟩ | hd
    · simp at hx
    · simp only [Finset.prod_empty, mul_one] at hr
      nlinarith [mul_self_nonneg r]
  · have hp : Prime (q i0 : ℤ) := Nat.prime_iff_prime_int.mp (hq.1 i0).1
    have hprod : d * ∏ i ∈ S, -(q i : ℤ) =
        -(q i0 : ℤ) * (d * ∏ i ∈ S.erase i0, -(q i : ℤ)) := by
      rw [← Finset.mul_prod_erase S (fun i => -(q i : ℤ)) hi0]; ring
    have hpr : (q i0 : ℤ) ∣ r := by
      apply hp.dvd_of_dvd_pow (n := 2)
      rw [sq, ← hr, hprod]
      exact Dvd.dvd.mul_right (dvd_neg.mpr dvd_rfl) _
    obtain ⟨t, rfl⟩ := hpr
    have h0 : (q i0 : ℤ) ≠ 0 := by exact_mod_cast (hq.1 i0).1.ne_zero
    have hrest : (q i0 : ℤ) ∣ d * ∏ i ∈ S.erase i0, -(q i : ℤ) := by
      refine ⟨-(t * t), ?_⟩
      rw [hprod] at hr
      apply mul_left_cancel₀ h0
      linear_combination -hr
    rcases hp.dvd_or_dvd hrest with h | h
    · exact hdq i0 h
    · obtain ⟨i, hi, hdiv⟩ := (hp.dvd_finsetProd_iff _).mp h
      rw [dvd_neg, Int.natCast_dvd_natCast,
        Nat.prime_dvd_prime_iff_eq (hq.1 i0).1 (hq.1 i).1] at hdiv
      exact (Finset.ne_of_mem_erase hi) (hq.2 hdiv).symm

lemma not_dvd_one (hq : Hyp3 q) (i : Fin 3) : ¬ (q i : ℤ) ∣ 1 := by
  intro h
  have h1 : q i ∣ 1 := by exact_mod_cast h
  exact (hq.1 i).1.one_lt.ne' (Nat.dvd_one.1 h1)

variable {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}

lemma not_sq_in_E (hK : MQKummer) (hq : Hyp3 q) (hα : IsHost q α) (d : ℤ) (hd : d < 0)
    (hdq : ∀ i, ¬ (q i : ℤ) ∣ d) : ¬ IsSquare (d : E) := by
  intro h
  have hns : ∀ S : Finset (Fin 3), S.Nonempty →
      ¬ IsSquare (∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by
    intro S hS
    have := not_sq_d hq 1 S (Or.inl hS) (fun i => by simpa using not_dvd_one hq i)
    simpa using this
  obtain ⟨_, _, hsq⟩ := hK 3 E (fun i => -(q i : ℤ)) α hα hns
  have h' : IsSquare (algebraMap ℚ E (d : ℚ)) := by simpa using h
  obtain ⟨S, hS⟩ := (hsq d).1 h'
  exact not_sq_d hq d S (Or.inr hd) hdq hS

lemma gal_sq (hH : HostGalois) (hq : Hyp3 q) (hα : IsHost q α) (σ : Gal(E/ℚ)) :
    σ * σ = 1 := by
  obtain ⟨_, _, hbij, hmul⟩ := hH q hq E α hα
  apply hbij.1
  rw [hmul]
  funext i
  have h1 : galSign α (1 : Gal(E/ℚ)) i = 1 := by simp [galSign]
  rw [Pi.mul_apply, h1, Int.units_mul_self]

lemma no_prime_root (hH : HostGalois) (hq : Hyp3 q) (hα : IsHost q α) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (η : E) (hη : IsPrimitiveRoot η p) : False := by
  obtain ⟨hGal, _, _, _⟩ := hH q hq E α hα
  have := hGal
  have hpos := hp.pos
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hη2 : IsPrimitiveRoot (η ^ 2) p := hη.pow_of_coprime 2 hcop
  have hmin : minpoly ℚ (η ^ 2) = minpoly ℚ η := by
    rw [← cyclotomic_eq_minpoly_rat hη hpos, ← cyclotomic_eq_minpoly_rat hη2 hpos]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := E)).1 hmin
  have hσ' : σ η = η ^ 2 := hσ
  have hsq := gal_sq hH hq hα σ
  have h4 : η = η ^ 4 := by
    calc η = (σ * σ) η := by rw [hsq]; rfl
    _ = σ (σ η) := rfl
    _ = η ^ 4 := by rw [hσ', map_pow, hσ', ← pow_mul]
  have h3 : η ^ 3 = 1 := by
    have hne : η ≠ 0 := hη.ne_zero hp.ne_zero
    apply mul_left_cancel₀ hne
    linear_combination -h4
  have h5 := (hη.pow_eq_one_iff_dvd 3).1 h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h5)

lemma no_four (hK : MQKummer) (hq : Hyp3 q) (hα : IsHost q α) (η : E)
    (hη : IsPrimitiveRoot η 4) : False := by
  have h2 : IsPrimitiveRoot (η ^ 2) 2 := hη.pow (by norm_num) (by norm_num)
  have h := h2.eq_neg_one_of_two_right
  refine not_sq_in_E hK hq hα (-1) (by norm_num) (fun i hi => not_dvd_one hq i ?_)
    ⟨η, by push_cast; linear_combination -h⟩
  exact dvd_neg.1 hi

lemma no_three (hK : MQKummer) (hq : Hyp3 q) (hq3 : ∀ i, q i ≠ 3) (hα : IsHost q α) (ω : E)
    (hω : IsPrimitiveRoot ω 3) : False := by
  have h3 : ω ^ 3 = 1 := hω.pow_eq_one
  have h1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hs : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · exact h
  refine not_sq_in_E hK hq hα (-3) (by norm_num) (fun i hi => ?_)
    ⟨2 * ω + 1, by push_cast; linear_combination (-4) * hs⟩
  have h3' : q i ∣ 3 := by
    have := dvd_neg.1 hi
    exact_mod_cast this
  exact hq3 i ((Nat.prime_dvd_prime_iff_eq (hq.1 i).1 Nat.prime_three).1 h3')

end CMRootsOfUnity

open CMRootsOfUnity

theorem hostMu_of (hK : MQKummer) (hH : HostGalois) : HostMu := by
  intro q hq hq3 E _ _ α hα ζ ⟨n, hn, hζn⟩
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hζn⟩
  have hmpos : 0 < orderOf ζ := orderOf_pos_iff.2 hfin
  have hprim : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
  have hodd : ∀ {p : ℕ}, p.Prime → p ∣ orderOf ζ → p = 2 := by
    intro p hp hpm
    obtain ⟨k, hk⟩ := hpm
    have hη : IsPrimitiveRoot (ζ ^ k) p := hprim.pow hmpos (by rw [hk, mul_comm])
    by_contra hp2
    by_cases hp3 : p = 3
    · subst hp3
      exact no_three hK hq hq3 hα (ζ ^ k) hη
    · exact no_prime_root hH hq hα p hp hp2 hp3 (ζ ^ k) hη
  have h4 : ¬ 4 ∣ orderOf ζ := by
    rintro ⟨k, hk⟩
    exact no_four hK hq hα (ζ ^ k) (hprim.pow hmpos (by rw [hk, mul_comm]))
  have hm2 : orderOf ζ ∣ 2 := by
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hmpos.ne' hodd
    rw [hpow] at h4 ⊢
    rcases h : (orderOf ζ).primeFactorsList.length with _ | _ | a
    · simp
    · simp
    · exfalso
      rw [h] at h4
      exact h4 (by
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this]
        exact pow_dvd_pow 2 (by omega))
  have hζ2 : ζ * ζ = 1 := by
    rw [← sq]
    exact (hprim.pow_eq_one_iff_dvd 2).2 hm2
  exact mul_self_eq_one_iff.1 hζ2

end Formalism.Q3
end
end

-- bundled from Formalism.CMTypeGalois.CMTypeFrobenius.MQFrob
section
open NumberField Ideal

noncomputable section

namespace Formalism.Q3

theorem mqFrob_intCast_mem_iff {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] (n : ℤ) :
    (n : 𝓞 E) ∈ P ↔ (p : ℤ) ∣ n := by
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}), Ideal.under_def,
    Ideal.mem_comap, eq_intCast]

theorem mqFrob_card {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [← Ideal.over_def P (span {(p : ℤ)}), Int.card_ideal_quot]

theorem mqFrob_of (hG : MQGalois) : MQFrob := by
  intro k E _ _ a α hMQ ha p _ P hPp _ σ H i
  have hp : p.Prime := Fact.out
  have hmem := mqFrob_intCast_mem_iff p P
  have hF : ∀ x : 𝓞 E, σ • x - x ^ p ∈ P := by
    intro x
    have := H x
    rw [mqFrob_card p P] at this
    exact this
  have hsq : α i ^ 2 = (a i : E) := hMQ.1 i
  have hσ : σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i := (hG k E a α hMQ ha).2.1 σ i
  have hint : IsIntegral ℤ (α i) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hsq, ← eq_intCast (algebraMap ℤ E)]
    exact isIntegral_algebraMap
  obtain ⟨A, hAcoe⟩ : ∃ A : 𝓞 E, (A : E) = α i := ⟨⟨α i, hint⟩, rfl⟩
  have hA2 : A ^ 2 = (a i : 𝓞 E) := by
    apply RingOfIntegers.coe_injective
    simp [hAcoe, hsq]
  have hσA : σ • A = (((galSign α σ i : ℤˣ) : ℤ) : 𝓞 E) * A := by
    apply RingOfIntegers.coe_injective
    show σ (A : E) = _
    rw [hAcoe, hσ]
    simp [hAcoe]
  have hAnot : ¬ (p : ℤ) ∣ a i → A ∉ P := by
    intro hpa hA
    apply hpa
    rw [← hmem, ← hA2]
    exact P.pow_mem_of_mem hA 2 (by norm_num)
  refine ⟨fun hnd => ?_, fun hp2 ha4 => ?_⟩
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hnd (by push_cast; exact dvd_mul_right 2 _)
    have hpa : ¬ (p : ℤ) ∣ a i := fun h => hnd (dvd_mul_of_dvd_right h 2)
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hpow : A ^ p = A * (a i : 𝓞 E) ^ (p / 2) := by
      rw [← hA2, ← pow_mul, ← pow_succ']
      congr 1
      omega
    have hE : (p : ℤ) ∣ (a i) ^ (p / 2) - legendreSym p (a i) := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, legendreSym.eq_pow]
      push_cast
      rfl
    have hE' : (a i : 𝓞 E) ^ (p / 2) - ((legendreSym p (a i) : ℤ) : 𝓞 E) ∈ P := by
      have := (hmem _).mpr hE
      push_cast at this
      exact this
    have hprod : ((((galSign α σ i : ℤˣ) : ℤ) - legendreSym p (a i) : ℤ) : 𝓞 E) * A ∈ P := by
      have heq : ((((galSign α σ i : ℤˣ) : ℤ) - legendreSym p (a i) : ℤ) : 𝓞 E) * A =
          (σ • A - A ^ p) + A * ((a i : 𝓞 E) ^ (p / 2) - ((legendreSym p (a i) : ℤ) : 𝓞 E)) := by
        rw [hσA, hpow]
        push_cast
        ring
      rw [heq]
      exact P.add_mem (hF A) (P.mul_mem_left A hE')
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    have hbad : ∀ n : ℤ, (n = 2 ∨ n = -2) → ¬ (p : ℤ) ∣ n := by
      rintro n (rfl | rfl) h
      · have := Int.le_of_dvd (by norm_num) h
        have := hp.two_le
        omega
      · have := Int.le_of_dvd (by norm_num) (dvd_neg.mpr h)
        have := hp.two_le
        omega
    rcases (inferInstance : P.IsPrime).mem_or_mem hprod with h | h
    · rw [hmem] at h
      have hL := legendreSym.eq_one_or_neg_one p (a := a i)
        (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa)
      rcases Int.units_eq_one_or (galSign α σ i) with h1 | h1 <;>
        simp only [h1, Units.val_one, Units.val_neg] at h ⊢ <;>
        rcases hL with h2 | h2 <;> rw [h2] at h ⊢ <;>
        first | rfl | exact absurd h (hbad _ (by norm_num))
    · exact absurd h (hAnot hpa)
  ·
    subst hp2
    obtain ⟨c, hc⟩ : ∃ c : ℤ, a i = 4 * c + 1 := ⟨(a i - 1) / 4, by omega⟩
    have hcE : (a i : E) = 4 * c + 1 := by exact_mod_cast hc
    obtain ⟨ω, hωdef⟩ : ∃ ω : E, ω = (1 + α i) / 2 := ⟨_, rfl⟩
    have hω2 : ω ^ 2 = ω + (c : E) := by
      rw [hωdef]
      linear_combination (1 / 4 : E) * hsq + (1 / 4 : E) * hcE
    have hωint : IsIntegral ℤ ω := by
      refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
      · apply Polynomial.monic_X_pow_sub
        rw [Polynomial.degree_X_add_C]
        norm_num
      · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
          Polynomial.eval₂_X_pow, hω2]
        simp
    obtain ⟨W, hWcoe⟩ : ∃ W : 𝓞 E, (W : E) = ω := ⟨⟨ω, hωint⟩, rfl⟩
    have hW2 : W ^ 2 = W + (c : 𝓞 E) := by
      apply RingOfIntegers.coe_injective
      simp [hWcoe, hω2]
    have h2P : (2 : 𝓞 E) ∈ P := by
      have := (hmem 2).mpr (by norm_num)
      exact_mod_cast this
    have hs : galSign α σ i = 1 ∨ galSign α σ i = -1 := by
      unfold galSign
      split_ifs <;> simp
    have hFW := hF W
    rcases hs with hs | hs
    · have hσW : σ • W = W := by
        apply RingOfIntegers.coe_injective
        show σ (W : E) = (W : E)
        rw [hWcoe, hωdef, map_div₀, map_add, map_one, hσ, hs, map_ofNat]
        simp
      rw [hσW, hW2, show W - (W + (c : 𝓞 E)) = ((-c : ℤ) : 𝓞 E) by push_cast; ring, hmem] at hFW
      push_cast at hFW
      simp only [hs, true_iff]
      omega
    · have hσW : σ • W = 1 - W := by
        apply RingOfIntegers.coe_injective
        show σ (W : E) = ((1 - W : 𝓞 E) : E)
        have hc1 : ((1 - W : 𝓞 E) : E) = 1 - (W : E) := by simp
        rw [hc1]
        rw [hWcoe, hωdef, map_div₀, map_add, map_one, hσ, hs, map_ofNat]
        push_cast
        ring
      rw [hσW, hW2, show 1 - W - (W + (c : 𝓞 E)) = ((1 - c : ℤ) : 𝓞 E) - 2 * W by push_cast; ring]
        at hFW
      have h1c : ((1 - c : ℤ) : 𝓞 E) ∈ P := by
        have := P.add_mem hFW (P.mul_mem_right W h2P)
        simpa using this
      rw [hmem] at h1c
      push_cast at h1c
      rw [hs]
      constructor
      · intro h
        have := congrArg (fun u : ℤˣ => (u : ℤ)) h
        simp at this
      · intro h
        omega

end Formalism.Q3
end
end

