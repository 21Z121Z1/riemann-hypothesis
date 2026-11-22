import Mathlib

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsAvoidProgression
section
namespace KStar.Choice

theorem exists_avoid (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (bad : (p : ℕ) → Finset (ZMod p)) (hbad : ∀ p ∈ s, (bad p).card < p) (Y : ℤ) :
    ∃ u : ℤ, Y ≤ u ∧ u < Y + ∏ p ∈ s, (p : ℤ) ∧ ∀ p ∈ s, (u : ZMod p) ∉ bad p := by
  classical
  have hc : ∀ p : ℕ, ∃ c : ℕ, p ∈ s → (c : ZMod p) ∉ bad p := by
    intro p
    by_cases hp : p ∈ s
    · have : Fact p.Prime := ⟨hs p hp⟩
      have h1 : (bad p).card < (Finset.univ : Finset (ZMod p)).card := by
        rw [Finset.card_univ, ZMod.card]; exact hbad p hp
      obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
      exact ⟨c.val, fun _ => by rwa [ZMod.natCast_zmod_val]⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose c hc using hc
  have hne : ∀ p ∈ s, id p ≠ 0 := fun p hp => (hs p hp).ne_zero
  have hco : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hs p hp) (hs q hq)).2 hpq
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset c id s hne hco
  have hP : (0 : ℤ) < ∏ p ∈ s, (p : ℤ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (hs p hp).pos
  refine ⟨Y + ((k : ℤ) - Y) % ∏ p ∈ s, (p : ℤ), ?_, ?_, ?_⟩
  · have := Int.emod_nonneg ((k : ℤ) - Y) hP.ne'
    linarith
  · have := Int.emod_lt_of_pos ((k : ℤ) - Y) hP
    linarith
  · intro p hp
    have hd : (p : ℤ) ∣ ∏ p ∈ s, (p : ℤ) := Finset.dvd_prod_of_mem (fun p : ℕ => (p : ℤ)) hp
    have h0 : ((∏ p ∈ s, (p : ℤ) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    have h1 : ((Y + ((k : ℤ) - Y) % ∏ p ∈ s, (p : ℤ) : ℤ) : ZMod p) = (c p : ZMod p) := by
      rw [Int.emod_def, Int.cast_add, Int.cast_sub, Int.cast_mul, h0, Int.cast_sub,
        Int.cast_natCast, zero_mul, sub_zero, add_sub_cancel]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (hk p hp)
    rw [h1]
    exact hc p hp

end KStar.Choice
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExtAlg
section
namespace KStar.Choice

def IsDiv (A : Type*) [CommGroup A] : Prop :=
  ∀ n : ℕ, n ≠ 0 → Function.Surjective fun a : A => a ^ n

theorem isDiv_complex_circle : IsDiv ℂˣ ∧ IsDiv Circle := by
  refine ⟨fun n hn z => ?_, fun n hn z => ?_⟩
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (Nat.pos_of_ne_zero hn)
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hw
      exact z.ne_zero hw.symm
    refine ⟨Units.mk0 w hw0, ?_⟩
    ext
    simp [hw]
  · refine ⟨Circle.exp ((z : ℂ).arg / n), ?_⟩
    simp only
    rw [← Circle.exp_natCast_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn), Circle.exp_arg]

theorem IsDiv.exists_extension {G A : Type*} [CommGroup G] [CommGroup A] (hA : IsDiv A)
    (H : Subgroup G) (f : H →* A) : ∃ F : G →* A, ∀ h : H, F h = f h := by
  have hsurj : ∀ {n : ℤ}, n ≠ 0 → Function.Surjective fun a : Additive A => n • a := by
    intro n hn x
    obtain ⟨y, hy⟩ := hA n.natAbs (Int.natAbs_ne_zero.mpr hn) (Additive.toMul x)
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul y, ?_⟩
      rw [h]
      change Additive.ofMul (y ^ ((n.natAbs : ℕ) : ℤ)) = x
      rw [zpow_natCast]
      simp only at hy
      rw [hy]
      rfl
    · refine ⟨Additive.ofMul y⁻¹, ?_⟩
      rw [h]
      change Additive.ofMul (y⁻¹ ^ (-((n.natAbs : ℕ) : ℤ))) = x
      rw [inv_zpow', neg_neg, zpow_natCast]
      simp only at hy
      rw [hy]
      rfl
  letI : DivisibleBy (Additive A) ℤ := divisibleByOfSMulRightSurj _ _ hsurj
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom
    (MonoidHom.toAdditive H.subtype) Subtype.val_injective (MonoidHom.toAdditive f)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hh (Additive.ofMul x))

end KStar.Choice
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.LevelEqThreeFiveIff
section
namespace KStar.Choice

structure IsLevelPair (N a b : ℕ) : Prop where
  prime_fst : a.Prime
  prime_snd : b.Prime
  ne_two : a ≠ 2
  lt : a < b
  lt_two_mul : b < 2 * a
  not_dvd_fst : ¬ a ∣ N
  not_dvd_snd : ¬ b ∣ N

example : IsLevelPair 1 3 5 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

noncomputable def levelFst (N : ℕ) : ℕ := sInf {a | ∃ b, IsLevelPair N a b}

noncomputable def levelSnd (N : ℕ) : ℕ := sInf {b | ∃ a, IsLevelPair N a b}

noncomputable def levelSnd' (N : ℕ) : ℕ := sInf {b | IsLevelPair N (levelFst N) b}

theorem exists_isLevelPair {N : ℕ} (hN : N ≠ 0) :
    ∃ a b, IsLevelPair N a b ∧ b < 4 * max N 2 := by
  have hM : max N 2 ≠ 0 := by omega
  obtain ⟨a, ha, hMa, haM⟩ := Nat.exists_prime_lt_and_le_two_mul (max N 2) hM
  obtain ⟨b, hb, hab, hba⟩ := Nat.exists_prime_lt_and_le_two_mul a ha.ne_zero
  have h1 : N ≤ max N 2 := le_max_left _ _
  have h2 : 2 ≤ max N 2 := le_max_right _ _
  have hne : b ≠ 2 * a := by
    intro h
    have h2b : 2 ∣ b := ⟨a, h⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hb).1 h2b
    omega
  refine ⟨a, b, ⟨ha, hb, by omega, hab, by omega, ?_, ?_⟩, by omega⟩
  · intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
    omega
  · intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
    omega

theorem isLevelPair_least {N : ℕ} (hN : N ≠ 0) :
    IsLevelPair N (levelFst N) (levelSnd N) ∧ levelSnd' N = levelSnd N ∧
      levelSnd N < 4 * max N 2 ∧
      ∀ a b, IsLevelPair N a b → levelFst N ≤ a ∧ levelSnd N ≤ b := by
  obtain ⟨a₀, b₀, h₀, hb₀⟩ := exists_isLevelPair hN
  have hfst : ∀ a b, IsLevelPair N a b → levelFst N ≤ a := fun a b h =>
    Nat.sInf_le (s := {a | ∃ b, IsLevelPair N a b}) ⟨b, h⟩
  have hsnd : ∀ a b, IsLevelPair N a b → levelSnd N ≤ b := fun a b h =>
    Nat.sInf_le (s := {b | ∃ a, IsLevelPair N a b}) ⟨a, h⟩
  obtain ⟨b₁, h₁⟩ : ∃ b, IsLevelPair N (levelFst N) b :=
    Nat.sInf_mem (s := {a | ∃ b, IsLevelPair N a b}) ⟨a₀, b₀, h₀⟩
  obtain ⟨a₂, h₂⟩ : ∃ a, IsLevelPair N a (levelSnd N) :=
    Nat.sInf_mem (s := {b | ∃ a, IsLevelPair N a b}) ⟨b₀, a₀, h₀⟩
  have hp : IsLevelPair N (levelFst N) (levelSnd N) := by
    have e1 := hfst _ _ h₂
    have e2 := hsnd _ _ h₁
    have e3 := h₂.lt
    have e4 := h₁.lt_two_mul
    exact ⟨h₁.prime_fst, h₂.prime_snd, h₁.ne_two, by omega, by omega, h₁.not_dvd_fst,
      h₂.not_dvd_snd⟩
  refine ⟨hp, le_antisymm ?_ ?_, lt_of_le_of_lt (hsnd _ _ h₀) hb₀,
    fun a b h => ⟨hfst a b h, hsnd a b h⟩⟩
  · exact Nat.sInf_le (s := {b | IsLevelPair N (levelFst N) b}) hp
  · have h' : IsLevelPair N (levelFst N) (levelSnd' N) :=
      Nat.sInf_mem (s := {b | IsLevelPair N (levelFst N) b}) ⟨_, hp⟩
    exact hsnd _ _ h'

end KStar.Choice
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.OddRad
section
namespace KStar.Choice

def oddRad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors.erase 2, p

def modP (q : ℕ) : ℕ := oddRad (q * q.totient)

def hostP (S : Finset ℕ) : ℕ := oddRad (∏ l ∈ S, l * (l - 1))

example : oddRad 90 = 15 := by
  have : (90 : ℕ).primeFactors = {2, 3, 5} := by simp [Nat.primeFactors]
  rw [oddRad, this]; decide

end KStar.Choice
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.SplitDef
section
open NumberField

namespace KStar.Choice

def SplitsCompletely (E : Type*) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1

private theorem span_isPrime {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)

private theorem primesOver_finite (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).Finite := by
  have := span_isPrime hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal this (by simpa using hp.ne_zero)
  exact IsDedekindDomain.primesOver_finite _ _

private theorem sum_ef (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    [Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E))] :
    ∑ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ =
      Module.finrank ℚ E := by
  have := span_isPrime hp
  rw [Ideal.sum_ramification_inertia_eq_finrank, RingOfIntegers.rank]

private theorem one_le_ef (E : Type*) [Field E] [NumberField E] {p : ℕ}
    (q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E)) :
    1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
  have := q.2.1
  exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)

private theorem ncard_eq_sum (E : Type*) [Field E] [NumberField E] {p : ℕ}
    [Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E))] :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard =
      ∑ _q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E), 1 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  simp

private theorem ncard_le (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard ≤ Module.finrank ℚ E := by
  have := (primesOver_finite E hp).fintype
  rw [ncard_eq_sum, ← sum_ef E hp]
  exact Finset.sum_le_sum fun q _ => one_le_ef E q

private theorem card_hom_eq (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    Nat.card (𝓞 E →+* ZMod p) =
      {P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) | P.inertiaDeg ℤ = 1}.ncard := by
  have := Fact.mk hp
  have hinj : Function.Injective (fun φ : 𝓞 E →+* ZMod p => RingHom.ker φ) :=
    fun φ ψ h => ZMod.ringHom_eq_of_ker_eq φ ψ h
  rw [← Set.ncard_range_of_injective hinj]
  congr 1
  ext P
  constructor
  · rintro ⟨φ, rfl⟩
    have h1 : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    have h2 : (RingHom.ker φ).LiesOver (Ideal.span {(p : ℤ)}) := by
      refine ⟨?_⟩
      rw [← ZMod.ker_intCastRingHom, Ideal.under_def, RingHom.comap_ker]
      congr 1
      exact RingHom.ext_int _ _
    refine ⟨⟨h1, h2⟩, ?_⟩
    have h3 := Ideal.pow_inertiaDeg p (RingHom.ker φ)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective φ)).toEquiv,
      Nat.card_zmod] at h3
    exact Nat.pow_right_injective hp.two_le (by simpa using h3)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h4 := Ideal.pow_inertiaDeg p P
    rw [h3, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at h4
    have : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (h4 ▸ hp.ne_zero)
    have := Fintype.ofFinite (𝓞 E ⧸ P)
    have e : ZMod p ≃+* (𝓞 E ⧸ P) :=
      ZMod.ringEquivOfPrime (𝓞 E ⧸ P) hp (by rw [← Nat.card_eq_fintype_card, ← h4])
    refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem splitsCompletely_iff_ncard (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    SplitsCompletely E p ↔
      ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E := by
  have := (primesOver_finite E hp).fintype
  rw [ncard_eq_sum, ← sum_ef E hp, Finset.sum_eq_sum_iff_of_le fun q _ => one_le_ef E q]
  constructor
  · intro h q _
    obtain ⟨h1, h2⟩ := h q.1 q.2.1 q.2.2
    rw [h1, h2]
  · intro h P h1 h2
    have := h ⟨P, h1, h2⟩ (Finset.mem_univ _)
    exact ⟨Nat.eq_one_of_mul_eq_one_right this.symm, Nat.eq_one_of_mul_eq_one_left this.symm⟩

theorem splitsCompletely_iff_card_hom (E : Type*) [Field E] [NumberField E] {p : ℕ}
    (hp : p.Prime) :
    SplitsCompletely E p ↔ Nat.card (𝓞 E →+* ZMod p) = Module.finrank ℚ E := by
  rw [card_hom_eq E hp]
  constructor
  · intro h
    rw [← (splitsCompletely_iff_ncard E hp).1 h]
    congr 1
    ext P
    exact ⟨fun h' => h'.1, fun h' => ⟨h', (h P h'.1 h'.2).2⟩⟩
  · intro h
    refine (splitsCompletely_iff_ncard E hp).2 (le_antisymm (ncard_le E hp) ?_)
    rw [← h]
    exact Set.ncard_le_ncard (fun P hP => hP.1) (primesOver_finite E hp)

theorem SplitsCompletely.of_tower {E L : Type*} [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] {p : ℕ} (hp : p.Prime) (h : SplitsCompletely L p) :
    SplitsCompletely E p := by
  intro P h1 h2
  have _ := hp
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) P
  have hQ3 : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  obtain ⟨h3, h4⟩ := h Q hQ1 hQ3
  exact ⟨Nat.dvd_one.1 (h3 ▸ Ideal.ramificationIdx_below_dvd (R := ℤ) P Q),
    Nat.dvd_one.1 (h4 ▸ Ideal.inertiaDeg_below_dvd (R := ℤ) P Q)⟩

end KStar.Choice
end

