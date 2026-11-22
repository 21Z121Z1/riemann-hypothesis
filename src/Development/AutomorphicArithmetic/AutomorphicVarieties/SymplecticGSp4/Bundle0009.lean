import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LocUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DirGPowOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {M : ℕ} (N : ℕ) [NeZero N] (hN : N ∣ M)
    (s : G ℚ Ω) (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) : Chr.cls ℚ Ω N s = 1 := by
  refine (Chr.clsFacts ℚ Ω N).2.2.1 s 1 (fun ζ hζ => ?_)
  obtain ⟨k, rfl⟩ := hN
  rw [h ζ (by rw [pow_mul, hζ, one_pow]), Units.val_one, ZMod.val_one_eq_one_mod]
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hN1 : N = 1 := by
      have := NeZero.pos N
      omega
    subst hN1
    simpa using hζ

private theorem dirG_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {M N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) (hN : N ∣ M) (s : G ℚ Ω) (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) : Chr.dirG ℚ Ω χ s = 1 := by
  rw [Chr.dirG, MonoidHom.comp_apply, cls_one N hN s h, map_one]

private theorem dirG_pow_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {a m : ℕ} (h : χ ^ a = 1) (ha : a ∣ m) : Chr.dirG ℚ Ω χ ^ m = 1 := by
  obtain ⟨k, rfl⟩ := ha
  refine MonoidHom.ext fun g => Units.ext ?_
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one,
    Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rw [pow_mul, ← MulChar.pow_apply_coe, h, MulChar.one_apply_coe, one_pow]

private theorem tot_two (k : ℕ) : Nat.totient (2 ^ k) ∣ 2 ^ k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.totient_prime_pow_succ Nat.prime_two, pow_succ]
    exact Nat.mul_dvd_mul_left _ (by norm_num)

private theorem pow_tot {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    χ ^ Nat.totient N = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
    ZMod.pow_totient, Units.val_one, map_one]

private theorem pow_tot_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    χ ^ Nat.totient χ.conductor = 1 := by
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  rw [show χ ^ Nat.totient χ.conductor = DirichletCharacter.changeLevel χ.conductor_dvd_level
      (χ.primitiveCharacter ^ Nat.totient χ.conductor) by
    rw [map_pow, χ.changeLevel_primitiveCharacter]]
  rw [pow_tot, map_one]

theorem UpperTheory.V.GradeZeroInterpolatingElement.levOf :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → ∀ n' p₁ m₀ : ℕ, Aut.OfChar D e ψ n' p₁ m₀ → c2 ψ ≤ n' → m₀ ∣ h.o → (Af.KillsMu (l * 2 ^ n' * h.N * p₁) D.ψ ∧ Af.KillsMu (l * 2 ^ n' * h.N * p₁) D.ξ ∧ Af.KillsMu (l * 2 ^ n' * h.N * p₁) D.om) ∧ D.ψ ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 ∧ D.ξ ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 ∧ D.om ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 := by
  intro Ω _ _ _ h t _ l _ c e _ _ _ ψ hψ D hD n' p₁ m₀ hc hc2 hm₀
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hp₁, ξ', ξ₀, -, -, hord, hξ⟩ := hc.xi
  have hpsi := hc.psi
  have hMN : h.N ∣ l * 2 ^ n' * h.N * p₁ := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hMp : p₁ ∣ l * 2 ^ n' * h.N * p₁ := dvd_mul_left _ _
  have hM2 : 2 ^ n' ∣ l * 2 ^ n' * h.N * p₁ :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  have hMl : l ∣ l * 2 ^ n' * h.N * p₁ :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hEo : h.o ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hE2o : 2 * h.o ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_left _ _
  have hE2 : 2 ^ n' ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hEl : l - 1 ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hIs : IsOmT c D.om := ⟨hD.om_pow, fun σ => Ideal.Quotient.eq.mp (hD.om_bar σ)⟩
  have hker := ((omT Ω l c).2 D.om hIs).2.1
  have htot2 : Nat.totient (2 ^ n') ∣ (l - 1) * 2 ^ n' * (2 * h.o) := (tot_two n').trans hE2
  have hpsiE : ψ ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 := by
    have hchar := ((Host.mem_X h).1 hψ).1
    have hcomp := hostComp h c.O ψ hchar
    refine (compAlg c.O h.N 2 Nat.prime_two).2.2.2.2.2.2.2 ψ _ (fun p hp => ?_)
    have pp := Nat.prime_of_mem_primeFactors hp
    by_cases hp2 : p = 2
    · subst hp2
      have hcond := (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1
      have h1 := pow_tot_cond (psi2 ψ)
      rw [← hcond] at h1
      have hdv : Nat.totient (2 ^ c2 ψ) ∣ (l - 1) * 2 ^ n' * (2 * h.o) :=
        ((tot_two _).trans (Nat.pow_dvd_pow 2 hc2)).trans hE2
      obtain ⟨k, hk⟩ := hdv
      rw [hk, pow_mul]
      unfold psi2 at h1
      rw [h1, one_pow]
    · exact orderOf_dvd_iff_pow_eq_one.mp (((hcomp.2.2 p pp hp2).1).trans hE2o)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro s hs
    rw [hpsi]
    exact dirG_one ψ hMN s hs
  · intro s hs
    rw [hξ, MonoidHom.mul_apply, dirG_one ξ₀ hMp s hs, dirG_one ξ' hM2 s hs, mul_one]
  · intro s hs
    have h1 : Chr.cls ℚ Ω l s = 1 := cls_one l hMl s hs
    have h2 : s ∈ D.om.ker := by
      rw [hker]
      exact h1
    exact h2
  · rw [hpsi]
    exact dirG_pow_one ψ hpsiE dvd_rfl
  · rw [hξ, mul_pow, dirG_pow_one ξ₀ (pow_orderOf_eq_one ξ₀) (by rw [hord]; exact hm₀.trans hEo),
      dirG_pow_one ξ' (pow_tot ξ') htot2, mul_one]
  · obtain ⟨k, hk⟩ := hEl
    rw [hk, pow_mul, hD.om_pow, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowClogLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem two_pow_clog_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.clog 2 m ≤ 2 * m := by
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · have hk : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) h1
    have hlt := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h1
    obtain ⟨k, hk'⟩ : ∃ k, Nat.clog 2 m = k + 1 := ⟨Nat.clog 2 m - 1, by omega⟩
    rw [hk'] at hlt ⊢
    simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel] at hlt
    rw [pow_succ]
    linarith
  · have : m = 1 := by omega
    subst this
    simp

private theorem nII_le (X l N o q c n f : ℕ) (hX : 16 ≤ X) (hl : l ≤ X) (hN : N ≤ X) (ho : o ≤ X) (hq : q ≤ X)
    (hc : 2 ^ c ≤ X) (hn : 2 ^ n ≤ l ^ f) (hl0 : 0 < l) (hN0 : 0 < N) :
    2 ^ Nat.clog 2 (max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2)) ≤ X ^ (2 * f + 10) := by
  have hX1 : 1 ≤ X := by omega
  have hX2 : 2 ≤ X := by omega
  have hmono : ∀ {i j : ℕ}, i ≤ j → X ^ i ≤ X ^ j := fun h => Nat.pow_le_pow_right hX1 h
  have mlp : ∀ {a b i j : ℕ}, a ≤ X ^ i → b ≤ X ^ j → a * b ≤ X ^ (i + j) := by
    intro a b i j ha hb
    rw [pow_add]
    exact Nat.mul_le_mul ha hb
  have h4 : 4 ^ n ≤ X ^ (f * 2) := by
    have e4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e4, pow_mul]
    exact Nat.pow_le_pow_left (hn.trans (Nat.pow_le_pow_left hl f)) 2
  have hA1 : l * N * 4 ^ n ≤ X ^ (1 + 1 + f * 2) :=
    mlp (mlp (hl.trans (pow_one X).ge) (hN.trans (pow_one X).ge)) h4
  have hB : 2 ^ c * o * l ^ 3 * q ^ 2 ≤ X ^ (1 + 1 + 3 + 2) :=
    mlp (mlp (mlp (hc.trans (pow_one X).ge) (ho.trans (pow_one X).ge))
      (Nat.pow_le_pow_left hl 3)) (Nat.pow_le_pow_left hq 2)
  have hA2 : 2 ^ (c + 6) * o * l ^ 3 * q ^ 2 ≤ 64 * X ^ (1 + 1 + 3 + 2) := by
    calc 2 ^ (c + 6) * o * l ^ 3 * q ^ 2 = 64 * (2 ^ c * o * l ^ 3 * q ^ 2) := by ring
      _ ≤ 64 * X ^ (1 + 1 + 3 + 2) := Nat.mul_le_mul_left 64 hB
  have hpos : 1 ≤ l * N * 4 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmax1 : 1 ≤ max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) := hpos.trans (le_max_left _ _)
  have k1 : 2 * (l * N * 4 ^ n) ≤ X ^ (2 * f + 10) :=
    calc 2 * (l * N * 4 ^ n) ≤ X * X ^ (1 + 1 + f * 2) := Nat.mul_le_mul hX2 hA1
      _ = X ^ (1 + (1 + 1 + f * 2)) := by ring
      _ ≤ X ^ (2 * f + 10) := hmono (by omega)
  have h128 : 128 ≤ X ^ 2 := by nlinarith
  have k2 : 2 * (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) ≤ X ^ (2 * f + 10) :=
    calc 2 * (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) ≤ 2 * (64 * X ^ (1 + 1 + 3 + 2)) := Nat.mul_le_mul_left 2 hA2
      _ = 128 * X ^ (1 + 1 + 3 + 2) := by ring
      _ ≤ X ^ 2 * X ^ (1 + 1 + 3 + 2) := Nat.mul_le_mul_right _ h128
      _ = X ^ (2 + (1 + 1 + 3 + 2)) := by ring
      _ ≤ X ^ (2 * f + 10) := hmono (by omega)
  calc 2 ^ Nat.clog 2 (max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2))
      ≤ 2 * max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) := two_pow_clog_le _ hmax1
    _ ≤ X ^ (2 * f + 10) := by
      rcases max_choice (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) with h | h <;> rw [h] <;> assumption

private theorem le_pow_self' {X : ℕ} (hX : 2 ≤ X) (k : ℕ) : k ≤ X ^ k := by
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ X ^ k := Nat.pow_le_pow_left hX k

private theorem mul_le_pow' {X a b i j : ℕ} (ha : a ≤ X ^ i) (hb : b ≤ X ^ j) : a * b ≤ X ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

private theorem two_pow_nIII_le {X l q P n f : ℕ} (hX : 2 ≤ X) (hl : l ≤ X) (hl0 : 0 < l) (hn : 2 ^ n < l ^ f) :
    2 ^ Nat.clog 2 (max (l * q * P * 4 ^ n) (8 * l ^ 2)) ≤ X ^ (1 + (10 + q + P + 2 * f)) := by
  have hX1 : 1 ≤ X := by omega
  have hmono : ∀ {i j : ℕ}, i ≤ j → X ^ i ≤ X ^ j := fun h => Nat.pow_le_pow_right hX1 h
  have h4 : 4 ^ n ≤ X ^ (f * 2) := by
    have e4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e4, pow_mul]
    exact Nat.pow_le_pow_left (hn.le.trans (Nat.pow_le_pow_left hl f)) 2
  have hA1 : l * q * P * 4 ^ n ≤ X ^ (1 + q + P + f * 2) :=
    mul_le_pow' (mul_le_pow' (mul_le_pow' (hl.trans (pow_one X).ge) (le_pow_self' hX q))
      (le_pow_self' hX P)) h4
  have h8 : 8 ≤ X ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ X ^ 3 := Nat.pow_le_pow_left hX 3
  have hA2 : 8 * l ^ 2 ≤ X ^ (3 + 2) := mul_le_pow' h8 (Nat.pow_le_pow_left hl 2)
  have hmax1 : 1 ≤ max (l * q * P * 4 ^ n) (8 * l ^ 2) :=
    (Nat.one_le_iff_ne_zero.mpr (by positivity)).trans (le_max_right _ _)
  have k1 : 2 * (l * q * P * 4 ^ n) ≤ X ^ (1 + (10 + q + P + 2 * f)) :=
    calc 2 * (l * q * P * 4 ^ n) ≤ X * X ^ (1 + q + P + f * 2) := Nat.mul_le_mul hX hA1
      _ = X ^ (1 + (1 + q + P + f * 2)) := by ring
      _ ≤ X ^ (1 + (10 + q + P + 2 * f)) := hmono (by omega)
  have k2 : 2 * (8 * l ^ 2) ≤ X ^ (1 + (10 + q + P + 2 * f)) :=
    calc 2 * (8 * l ^ 2) ≤ X * X ^ (3 + 2) := Nat.mul_le_mul hX hA2
      _ = X ^ (1 + (3 + 2)) := by ring
      _ ≤ X ^ (1 + (10 + q + P + 2 * f)) := hmono (by omega)
  calc 2 ^ Nat.clog 2 (max (l * q * P * 4 ^ n) (8 * l ^ 2))
      ≤ 2 * max (l * q * P * 4 ^ n) (8 * l ^ 2) := two_pow_clog_le _ hmax1
    _ ≤ X ^ (1 + (10 + q + P + 2 * f)) := by
      rcases max_choice (l * q * P * 4 ^ n) (8 * l ^ 2) with h | h <;> rw [h] <;> assumption

private theorem pZero_le' (m : ℕ) : pZero m ≤ 2 * m + 10 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [pZero]
  · exact (pZeroLe m hm).2.2.2

private theorem final_le (C A a B o l n N P e : ℕ) (hl : 2 ≤ l) (hN : 0 < N) (he : 0 < e) (hP : P ≤ B)
    (hn : 2 ^ n ≤ (l * N * e) ^ a) :
    (2 * C * ((l - 1) * 2 ^ n * (2 * o) : ℕ) * (((l * 2 ^ n * N * P : ℕ) : ℝ) * (e + 1)) ^ A *
      Real.log (pZero (l * N * P)) : ℝ) ≤
      ((l : ℝ) * N * e) ^ (2 * C + (1 + a + 2 * o) + (1 + a + 1 + B + 2) * A + (2 + (1 + 1 + B) + 10 + 1)) := by
  obtain ⟨X, hXdef⟩ : ∃ X, X = l * N * e := ⟨_, rfl⟩
  rw [← hXdef] at hn
  have hNe : 1 ≤ N * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hle : 1 ≤ l * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlN : 1 ≤ l * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlX : l ≤ X := by
    calc l = l * 1 := (mul_one _).symm
      _ ≤ l * (N * e) := Nat.mul_le_mul_left _ hNe
      _ = X := by rw [hXdef]; ring
  have hNX : N ≤ X := by
    calc N = N * 1 := (mul_one _).symm
      _ ≤ N * (l * e) := Nat.mul_le_mul_left _ hle
      _ = X := by rw [hXdef]; ring
  have heX : e ≤ X := by
    calc e = 1 * e := (one_mul _).symm
      _ ≤ (l * N) * e := Nat.mul_le_mul_right _ hlN
      _ = X := by rw [hXdef]
  have hX2 : 2 ≤ X := hl.trans hlX
  have hX1 : 1 ≤ X := by omega
  have hmono : ∀ {i j : ℕ}, i ≤ j → X ^ i ≤ X ^ j := fun h => Nat.pow_le_pow_right hX1 h
  have hPB : P ≤ X ^ B := hP.trans (le_pow_self' hX2 B)
  have b1 : 2 * C ≤ X ^ (2 * C) := le_pow_self' hX2 _
  have b2 : (l - 1) * 2 ^ n * (2 * o) ≤ X ^ (1 + a + 2 * o) :=
    mul_le_pow' (mul_le_pow' (((Nat.sub_le l 1).trans hlX).trans (pow_one X).ge) hn) (le_pow_self' hX2 _)
  have he1 : e + 1 ≤ X ^ 2 := by nlinarith
  have b3 : l * 2 ^ n * N * P * (e + 1) ≤ X ^ (1 + a + 1 + B + 2) :=
    mul_le_pow' (mul_le_pow' (mul_le_pow' (mul_le_pow' (hlX.trans (pow_one X).ge) hn)
      (hNX.trans (pow_one X).ge)) hPB) he1
  have hy : l * N * P ≤ X ^ (1 + 1 + B) :=
    mul_le_pow' (mul_le_pow' (hlX.trans (pow_one X).ge) (hNX.trans (pow_one X).ge)) hPB
  have hy1 : 1 ≤ X ^ (1 + 1 + B) := Nat.one_le_pow _ _ (by omega)
  have h16 : 16 ≤ X ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ X ^ 4 := Nat.pow_le_pow_left hX2 4
  have b4 : pZero (l * N * P) ≤ X ^ (2 + (1 + 1 + B) + 10 + 1) := by
    calc pZero (l * N * P) ≤ 2 * (l * N * P) + 10 := pZero_le' _
      _ ≤ 2 * X ^ (1 + 1 + B) + 10 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hy) 10
      _ ≤ X ^ 4 * X ^ (1 + 1 + B) := by nlinarith
      _ = X ^ (4 + (1 + 1 + B)) := by ring
      _ ≤ X ^ (2 + (1 + 1 + B) + 10 + 1) := hmono (by omega)
  have hXr : ((l : ℝ) * N * e) = (X : ℝ) := by rw [hXdef]; push_cast; ring
  rw [hXr]
  have c1 : 2 * (C : ℝ) ≤ (X : ℝ) ^ (2 * C) := by exact_mod_cast b1
  have c2 : (((l - 1) * 2 ^ n * (2 * o) : ℕ) : ℝ) ≤ (X : ℝ) ^ (1 + a + 2 * o) := by exact_mod_cast b2
  have c3 : (((l * 2 ^ n * N * P : ℕ) : ℝ) * (e + 1)) ≤ (X : ℝ) ^ (1 + a + 1 + B + 2) := by
    have : (((l * 2 ^ n * N * P * (e + 1) : ℕ) : ℝ)) ≤ (X : ℝ) ^ (1 + a + 1 + B + 2) := by exact_mod_cast b3
    simpa using this
  have hlog0 : 0 ≤ Real.log (pZero (l * N * P)) := Real.log_natCast_nonneg _
  have c4 : Real.log (pZero (l * N * P)) ≤ (X : ℝ) ^ (2 + (1 + 1 + B) + 10 + 1) := by
    have hb4 : ((pZero (l * N * P) : ℕ) : ℝ) ≤ (X : ℝ) ^ (2 + (1 + 1 + B) + 10 + 1) := by exact_mod_cast b4
    exact (Real.log_le_self (Nat.cast_nonneg _)).trans hb4
  have hY0 : 0 ≤ (((l * 2 ^ n * N * P : ℕ) : ℝ) * (e + 1)) := by positivity
  have s1 := mul_le_mul c1 c2 (by positivity) (by positivity)
  have s2 := mul_le_mul s1 (pow_le_pow_left₀ hY0 c3 A) (by positivity) (by positivity)
  have s3 := mul_le_mul s2 c4 hlog0 (by positivity)
  refine s3.trans (le_of_eq ?_)
  rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]

theorem UpperTheory.V.GradeZeroInterpolatingElement.arith :
    ∀ (χ : Formalism.HC.PChar) (C A : ℕ), ∃ C' : ℕ, ∀ h : Host, h.chi = χ → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 2 ≤ e → ∀ ψ ∈ h.X c e, ∀ n' p₁ : ℕ, (n' = h.nII l ψ ∧ p₁ = 1) ∨ (n' = h.nIII l ψ ∧ p₁ = UpperTheory.V.pOne χ) → (2 * C * ((l - 1) * 2 ^ n' * (2 * h.o) : ℕ) * (((l * 2 ^ n' * h.N * p₁ : ℕ) : ℝ) * (e + 1)) ^ A * Real.log (pZero (l * h.N * p₁)) : ℝ) ≤ ((l : ℝ) * h.N * e) ^ C' := by
  intro χ C A
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = (2 * (4 * ordC χ).totient + 10) +
      (1 + (10 + χ.N + pOne χ + 2 * (4 * ordC χ).totient)) := ⟨_, rfl⟩
  refine ⟨2 * C + (1 + a + 2 * ordC χ) + (1 + a + 1 + (1 + pOne χ) + 2) * A +
    (2 + (1 + 1 + (1 + pOne χ)) + 10 + 1), ?_⟩
  intro h hχ
  subst hχ
  intro l _ c e hl2 he ψ hψ n' p₁ hcase
  have pl : l.Prime := Fact.out
  have hl : 2 ≤ l := pl.two_le
  have hN0 := h.N_pos
  have hchar := ((Host.mem_X h).1 hψ).1
  obtain ⟨-, -, hn0, -, -⟩ := cmDatum_char_two_adic_order_bounds h c.O ψ hchar l pl hl2
  have hidx := hostIndex h
  have hNe : 1 ≤ h.N * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hle : 1 ≤ l * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlX : l ≤ l * h.N * e := by
    calc l = l * 1 := (mul_one _).symm
      _ ≤ l * (h.N * e) := Nat.mul_le_mul_left _ hNe
      _ = l * h.N * e := by ring
  have hNX : h.N ≤ l * h.N * e := by
    calc h.N = h.N * 1 := (mul_one _).symm
      _ ≤ h.N * (l * e) := Nat.mul_le_mul_left _ hle
      _ = l * h.N * e := by ring
  have h16 : 16 ≤ h.N := Nat.le_of_dvd hN0 hidx.2.2.1
  have hX16 : 16 ≤ l * h.N * e := h16.trans hNX
  have hX1 : 1 ≤ l * h.N * e := by omega
  have hX2 : 2 ≤ l * h.N * e := by omega
  have hqN : h.q ≤ h.N := Nat.le_of_dvd hN0 h.q_dvd
  have hoq : h.o ≤ h.q := hidx.2.2.2.2.1
  have hcN : 2 ^ c2 ψ ≤ h.N := Nat.le_of_dvd hN0 (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.2.1
  have hP : p₁ ≤ 1 + pOne h.chi := by
    rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  have hn : 2 ^ n' ≤ (l * h.N * e) ^ a := by
    rw [ha]
    rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · have key := nII_le (l * h.N * e) l h.N h.o h.q (c2 ψ) (n0 l ψ) (4 * h.o).totient hX16 hlX hNX
        ((hoq.trans hqN).trans hNX) (hqN.trans hNX) (hcN.trans hNX) hn0.le (by omega) hN0
      unfold Host.nII
      exact key.trans (Nat.pow_le_pow_right hX1 (Nat.le_add_right _ _))
    · have key := two_pow_nIII_le (X := l * h.N * e) (q := h.q) (P := pOne h.chi)
        (f := (4 * h.o).totient) hX2 hlX (by omega) hn0
      unfold Host.nIII
      exact key.trans (Nat.pow_le_pow_right hX1 (Nat.le_add_left _ _))
  exact final_le C A a (1 + pOne h.chi) h.o l n' h.N p₁ e hl hN0 (by omega) hP hn
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ValProd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem val_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m n : ℕ} (h : m ∣ n)
    (hA : A.valuation (m : Ω) < 1) : A.valuation (n : Ω) < 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  have hk : A.valuation (k : Ω) ≤ 1 := by
    simpa using A.valuation_le_one (k : A)
  calc A.valuation (m : Ω) * A.valuation (k : Ω) ≤ A.valuation (m : Ω) * 1 := mul_le_mul' le_rfl hk
    _ < 1 := by rwa [mul_one]

private theorem val_prod {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (S : Finset ℕ)
    (hA : A.valuation ((∏ p ∈ S, p : ℕ) : Ω) < 1) : ∃ p ∈ S, A.valuation (p : Ω) < 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hA
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Nat.cast_mul, map_mul] at hA
    by_cases hp : A.valuation (a : Ω) < 1
    · exact ⟨a, Finset.mem_insert_self a S, hp⟩
    · have h1 : A.valuation (a : Ω) = 1 :=
        le_antisymm (by simpa using A.valuation_le_one (a : A)) (not_lt.mp hp)
      rw [h1, one_mul] at hA
      obtain ⟨p, hpS, hp'⟩ := ih hA
      exact ⟨p, Finset.mem_insert_of_mem hpS, hp'⟩

private theorem vlen_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (he : e ≠ 0) (ψ : DirichletCharacter c.O N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Vlen Ω c e ψ ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ) := by
  classical
  haveI := c.dvr
  haveI := c.fin
  have hcls := Chr.clsFacts ℚ Ω N
  have hker : (Chr.cls ℚ Ω N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [Chr.dirG, hg]
  have hopen : IsOpen ((Chr.dirG ℚ Ω ψ).ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hker hcls.1
  have hpow : Chr.dirG ℚ Ω ψ ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Chr.dirG, MonoidHom.comp_apply, ← map_pow,
      pow_card_eq_one, map_one]
  have hint : ∀ (A : ValuationSubring Ω) (x : Ω) (z : ℤ), A.valuation x < 1 →
      A.valuation (x * (z : Ω)) < 1 := by
    intro A x z hx
    rw [map_mul]
    have hz : A.valuation (z : Ω) ≤ 1 := by simpa using A.valuation_le_one (z : A)
    calc A.valuation x * A.valuation (z : Ω) ≤ A.valuation x * 1 := mul_le_mul' le_rfl hz
      _ < 1 := by rwa [mul_one]
  show Chr.VS l (l * N) e (Chr.dirG ℚ Ω ψ) ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ)
  unfold Chr.VS
  refine Module.length_le_of_injective (Submodule.inclusion ?_) (Submodule.inclusion_injective _)
  intro x hx
  simp only [Base.ShaU, Base.mem_locSel] at hx ⊢
  intro D hD
  rcases hD with ⟨A, hAS, rfl⟩ | ⟨A, rfl⟩
  · obtain ⟨p, hpS, hp⟩ := val_prod A S hAS
    by_cases hdvd : p ∣ l * N
    · exact hx (Dec A) (Or.inl ⟨A, val_dvd A hdvd hp, rfl⟩)
    · have pp := hS p hpS
      have hpl : p ≠ l := by
        rintro rfl
        exact hdvd (dvd_mul_right p N)
      have hpN : ¬ p ∣ N := fun h' => hdvd (dvd_mul_of_dvd_right h' l)
      have hN : ¬ A.valuation (N : Ω) < 1 := by
        intro hN
        have hcop : Nat.gcd p N = 1 := ((Nat.Prime.coprime_iff_not_dvd pp).2 hpN)
        have hb := Nat.gcd_eq_gcd_ab p N
        rw [hcop] at hb
        have h1 : (1 : Ω) = (p : Ω) * (Nat.gcdA p N : Ω) + (N : Ω) * (Nat.gcdB p N : Ω) := by
          have := congrArg (fun z : ℤ => (z : Ω)) hb
          push_cast at this
          exact this
        have hsum := Valuation.map_add_lt A.valuation (hint A _ (Nat.gcdA p N) hp)
          (hint A _ (Nat.gcdB p N) hN)
        rw [← h1, map_one] at hsum
        exact lt_irrefl _ hsum
      have hIne : Ine A ≤ (Chr.dirG ℚ Ω ψ).ker := le_trans (hcls.2.2.2.2 A hN) hker
      have hU : (⊤ : Subgroup (G ℚ Ω)) ⊓ Ine A ≤ ⊤ ⊓ Dec A := inf_le_inf_left _ (Ine_le_Dec A)
      have hinj := (Chr.locUnr Ω l c.O e (Fintype.card (ZMod N)ˣ) (Chr.dirG ℚ Ω ψ) he
        Fintype.card_ne_zero hopen hpow p A pp hpl hp (⊤ ⊓ Ine A) (⊤ ⊓ Dec A) hU
        (top_inf_eq _) (top_inf_eq _)).2 (inf_le_right.trans hIne)
      have h0 := hx (Ine A) (Or.inr ⟨A, rfl⟩)
      have h2 : Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) hU
          (Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) (inf_le_left : ⊤ ⊓ Dec A ≤ ⊤) x) = 0 := by
        rw [Base.resU_resU]
        exact h0
      exact hinj (h2.trans (map_zero _).symm)
  · exact hx (Ine A) (Or.inr ⟨A, rfl⟩)

theorem UpperTheory.V.GradeZeroInterpolatingElement.shaEq :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → Aut.OfCase D h e ψ → Vlen Ω c e ψ ≤ D.sha := by
  intro Ω _ _ _ h t _ l _ c e _ he _ ψ _ D hD hA
  have key : ∀ {n' p₁ m₀ : ℕ}, Aut.OfChar D e ψ n' p₁ m₀ → Vlen Ω c e ψ ≤ D.sha := by
    intro n' p₁ m₀ hc
    unfold Raw.sha
    rw [hc.e_eq, hc.psi]
    exact vlen_le Ω l c h.N e he.ne' ψ D.S hD.S_prime
  rcases hA with ⟨_, hc⟩ | ⟨_, hc⟩
  · exact key hc
  · exact key hc
end

