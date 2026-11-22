import Mathlib
import Formalism.DirichletDensity.Statement

-- bundled from Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
section
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries

noncomputable section

namespace Formalism.HF.P

variable {q : ℕ} [NeZero q] {a : ZMod q}

private lemma apld_term_lemma (a : ZMod q) (x : ℝ) (n : ℕ) :
    LSeries.term (fun n ↦ (residueClass a n : ℂ)) (x : ℂ) n =
      ((residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, residueClass_apply_zero, zero_div, Complex.ofReal_zero]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]

lemma apld_tsum_residueClass_eq (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    ∑' n, residueClass a n / (n : ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
  have hx' : (x : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hx
  have hLS : LSeries (fun n ↦ (residueClass a n : ℂ)) x =
      ((∑' n, residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    unfold LSeries
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun n => apld_term_lemma a x n
  have hE := eqOn_LFunctionResidueClassAux ha hx'
  have hA : LFunctionResidueClassAux a x =
      (((∑' n, residueClass a n / (n : ℝ) ^ x) - (q.totient : ℝ)⁻¹ / (x - 1) : ℝ) : ℂ) := by
    rw [hE]
    simp only [hLS]
    push_cast
    rfl
  rw [hA, Complex.ofReal_re]
  ring

lemma apld_summable (a : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ ↦ residueClass a n / (n : ℝ) ^ x := by
  have hL : LSeriesSummable (fun n ↦ (residueClass a n : ℂ)) x :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re ((abscissaOfAbsConv_residueClass_le_one a).trans_lt
      (by simp only [Complex.ofReal_re]; exact_mod_cast hx))
  have h2 : Summable (LSeries.term (fun n ↦ (residueClass a n : ℂ)) x) := hL
  have h3 : Summable fun n : ℕ ↦ ((residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    convert h2 using 1
    funext n
    exact (apld_term_lemma a x n).symm
  exact Complex.summable_ofReal.1 h3

lemma residue_class_l_function_tendsto (a : ZMod q) :
    Tendsto (fun x : ℝ ↦ (x - 1) * (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 0) := by
  have hc : ContinuousWithinAt (fun x : ℝ ↦ LFunctionResidueClassAux a x) (Set.Ioi 1) 1 := by
    have h1 : ContinuousWithinAt (LFunctionResidueClassAux a) {s : ℂ | 1 ≤ s.re} ((1 : ℝ) : ℂ) :=
      continuousOn_LFunctionResidueClassAux a _ (by simp)
    exact h1.comp Complex.continuous_ofReal.continuousWithinAt
      (fun x hx => by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; exact le_of_lt hx)
  have hre : Tendsto (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (𝓝[>] 1)
      (𝓝 (LFunctionResidueClassAux a ((1 : ℝ) : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp hc.tendsto
  have hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  simpa using hlin.mul hre

lemma apld_nonprime_nonneg (a : ZMod q) (x : ℝ) (n : ℕ) :
    0 ≤ (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x := by
  split_ifs
  · simp
  · exact div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)

lemma apld_nonprime_le (a : ZMod q) {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x ≤
      (if n.Prime then 0 else residueClass a n) / n := by
  split_ifs
  · simp
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [residueClass_apply_zero, zero_div, zero_div]
    · apply div_le_div_of_nonneg_left (residueClass_nonneg a n) (by exact_mod_cast hn)
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx

lemma apld_prime_part_eq (a : ZMod q) (x : ℝ) (n : ℕ) :
    (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x =
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n := by
  by_cases hp : n.Prime
  · by_cases hn : (n : ZMod q) = a
    · have hmem : n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := ⟨hp, hn⟩
      rw [if_pos hp, Set.indicator_of_mem hmem]
      simp [residueClass, Set.indicator, hn, vonMangoldt_apply_prime hp]
    · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := fun h => hn h.2
      rw [if_pos hp, Set.indicator_of_notMem hmem]
      simp [residueClass, Set.indicator, hn]
  · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := fun h => hp h.1
    rw [if_neg hp, Set.indicator_of_notMem hmem, zero_div]

end Formalism.HF.P

open Formalism.HF.P in

theorem Formalism.HF.apLogDensity : Formalism.HF.APLogDensity := by
  intro N _ a ha
  unfold Formalism.HF.LogDensity
  set P : ℝ → ℕ → ℝ := fun x n => (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x with hP
  set Q : ℝ → ℕ → ℝ := fun x n => (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x with hQ
  have hPQ : ∀ x n, residueClass a n / (n : ℝ) ^ x = P x n + Q x n := by
    intro x n
    simp only [hP, hQ, ← add_div]
    congr 1
    split_ifs <;> simp
  have hPnn : ∀ x n, 0 ≤ P x n := by
    intro x n
    simp only [hP]
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) x)
    split_ifs
    · exact residueClass_nonneg a n
    · exact le_rfl
  have hQnn : ∀ x n, 0 ≤ Q x n := fun x n => apld_nonprime_nonneg a x n
  have hPs : ∀ x : ℝ, 1 < x → Summable (P x) := fun x hx =>
    (apld_summable a hx).of_nonneg_of_le (hPnn x) (fun n => by rw [hPQ]; linarith [hQnn x n])
  have hQs : ∀ x : ℝ, 1 < x → Summable (Q x) := fun x hx =>
    (apld_summable a hx).of_nonneg_of_le (hQnn x) (fun n => by rw [hPQ]; linarith [hPnn x n])
  have hB : Summable fun n : ℕ => (if n.Prime then 0 else residueClass a n) / n :=
    summable_residueClass_non_primes_div a
  set B := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n with hBdef
  have hQle : ∀ x : ℝ, 1 < x → ∑' n, Q x n ≤ B := fun x hx =>
    (hQs x hx).tsum_le_tsum (fun n => apld_nonprime_le a hx.le n) hB
  have hsplit : ∀ x : ℝ, 1 < x →
      (x - 1) * (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ - (x - 1) * ∑' n, Q x n =
      (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) := by
    intro x hx
    have hsum : ∑' n, residueClass a n / (n : ℝ) ^ x = ∑' n, P x n + ∑' n, Q x n := by
      rw [← (hPs x hx).tsum_add (hQs x hx)]
      exact tsum_congr (hPQ x)
    have hPind : ∑' n, P x n = ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n :=
      tsum_congr (fun n => apld_prime_part_eq a x n)
    have hT := apld_tsum_residueClass_eq ha hx
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.2 hx.ne'
    rw [← hPind]
    have : ∑' n, P x n = (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ / (x - 1) - ∑' n, Q x n := by
      linarith
    rw [this]
    field_simp
  have h1 : Tendsto (fun x : ℝ => (x - 1) * (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 0) :=
    residue_class_l_function_tendsto a
  have hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun x : ℝ => (x - 1) * ∑' n, Q x n) (𝓝[>] 1) (𝓝 0) := by
    have hup : Tendsto (fun x : ℝ => (x - 1) * B) (𝓝[>] 1) (𝓝 0) := by
      simpa using hlin.mul_const B
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_nonneg (sub_nonneg.2 (le_of_lt hx)) (tsum_nonneg (hQnn x))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_le_mul_of_nonneg_left (hQle x hx) (sub_nonneg.2 (le_of_lt hx))
  have hlim := (h1.add (tendsto_const_nhds (x := (N.totient : ℝ)⁻¹))).sub h3
  have e : (0 : ℝ) + (N.totient : ℝ)⁻¹ - 0 = 1 / (N.totient : ℝ) := by simp
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hsplit x hx
end
end

-- bundled from Formalism.DirichletDensity.DirichletDensityProofs.HostDensityArith
section
open Filter Topology Finset Formalism.Q3

noncomputable section

namespace Formalism.HF.P

theorem hda_jac_zero_iff (p : ℕ) [Fact p.Prime] (m : ℕ) :
    jacobiSym (m : ℤ) p = 0 ↔ p ∣ m := by
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, Int.cast_natCast,
    ZMod.natCast_eq_zero_iff]

theorem hda_jac_qc (p : ℕ) [Fact p.Prime] (m : ℕ) :
    jacobiSym (m : ℤ) p = quadraticChar (ZMod p) (m : ZMod p) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  unfold legendreSym
  rw [Int.cast_natCast]

theorem hda_card_qc (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (e : ℤ) (he : e = 1 ∨ e = -1) :
    2 * (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = e)).card = p - 1 := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have key : ∀ y : ZMod p, quadraticChar (ZMod p) y = 0 ∨ quadraticChar (ZMod p) y = 1 ∨
      quadraticChar (ZMod p) y = -1 := by
    intro y
    by_cases hy : y = 0
    · left; rw [hy]; exact MulChar.map_zero _
    · right; exact quadraticChar_dichotomy hy
  have hsum : ((univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = 1)).card : ℤ) -
      (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = -1)).card = 0 := by
    have h0 := quadraticChar_sum_zero hF
    have : ∀ y : ZMod p, quadraticChar (ZMod p) y =
        (if quadraticChar (ZMod p) y = 1 then 1 else 0) -
          (if quadraticChar (ZMod p) y = -1 then 1 else 0) := by
      intro y; rcases key y with h | h | h <;> simp [h]
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_sub_distrib] at h0
    rw [Finset.card_filter, Finset.card_filter]; push_cast; exact h0
  have htot : (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = 1)).card +
      (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = -1)).card = p - 1 := by
    have : ∀ y : ZMod p, ((if quadraticChar (ZMod p) y = 1 then 1 else 0) +
        (if quadraticChar (ZMod p) y = -1 then 1 else 0) : ℕ) = (if y ≠ 0 then 1 else 0 : ℕ) := by
      intro y
      by_cases hy : y = 0
      · simp [hy]
      · rcases quadraticChar_dichotomy hy with h | h <;> simp [h, hy]
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun y _ => this y), ← Finset.card_filter, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rcases he with rfl | rfl <;> omega

theorem hda_log (hAP : APLogDensity) (q : Fin 3 → ℕ) (hq : Hyp3 q) (g : Gal3) :
    LogDensity {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = ((g i : ℤˣ) : ℤ)} (1 / 8) := by
  classical
  obtain ⟨hp, hinj⟩ := hq
  have hF : ∀ i, Fact (q i).Prime := fun i => ⟨(hp i).1⟩
  have hne2 : ∀ i, q i ≠ 2 := fun i h => by have := (hp i).2; omega
  have hcop : ∀ i j, i ≠ j → Nat.Coprime (q i) (q j) := fun i j h =>
    (Nat.coprime_primes (hp i).1 (hp j).1).mpr (hinj.ne h)
  set N := q 0 * q 1 * q 2 with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.mul_pos (hp 0).1.pos (hp 1).1.pos) (hp 2).1.pos
  have : NeZero N := ⟨hNpos.ne'⟩
  set e : Fin 3 → ℤ := fun i => ((g i : ℤˣ) : ℤ) with he_def
  have he : ∀ i, e i = 1 ∨ e i = -1 := fun i => by
    rcases Int.units_eq_one_or (g i) with h | h <;> simp [he_def, h]
  have hd0 : q 0 ∣ N := Dvd.intro (q 1 * q 2) (by rw [hN]; ring)
  have hd1 : q 1 ∣ N := Dvd.intro (q 0 * q 2) (by rw [hN]; ring)
  have hd2 : q 2 ∣ N := Dvd.intro (q 0 * q 1) (by rw [hN]; ring)
  have hdvd : ∀ i, q i ∣ N := by
    intro i; fin_cases i
    exacts [hd0, hd1, hd2]

  let A : Finset (ZMod N) := univ.filter (fun a => ∀ i, jacobiSym (a.val : ℤ) (q i) = e i)
  have hval : ∀ (n : ℕ) i, jacobiSym (((n : ZMod N)).val : ℤ) (q i) = jacobiSym (n : ℤ) (q i) := by
    intro n i
    apply jacobiSym.mod_left'
    rw [ZMod.val_natCast, Int.natCast_mod, Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.mpr (hdvd i))]
  have hmem : ∀ n : ℕ, ((∀ i, n ≠ q i) ∧ ∀ i, chiQ (q i) n = e i) ↔ (n : ZMod N) ∈ A := by
    intro n
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, hval, chiQ]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun i hni => ?_, h⟩
      have h0 : jacobiSym (n : ℤ) (q i) = 0 := (hda_jac_zero_iff (q i) n).mpr (by rw [hni])
      rw [h i] at h0
      rcases he i with h1 | h1 <;> omega
  have hunit : ∀ a ∈ A, IsUnit a := by
    intro a ha
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]
    have hc : ∀ i, Nat.Coprime a.val (q i) := by
      intro i
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hp i).1]
      intro hd
      have h0 := (hda_jac_zero_iff (q i) a.val).mpr hd
      rw [ha i] at h0
      rcases he i with h1 | h1 <;> omega
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hc 0) (hc 1)) (hc 2)

  let F : ZMod N → ZMod (q 0) × ZMod (q 1) × ZMod (q 2) := fun a =>
    ((a.val : ZMod (q 0)), (a.val : ZMod (q 1)), (a.val : ZMod (q 2)))
  have hFinj : Function.Injective F := by
    intro a b hab
    simp only [F, Prod.mk.injEq, ZMod.natCast_eq_natCast_iff] at hab
    obtain ⟨h0, h1, h2⟩ := hab
    have h01 : a.val ≡ b.val [MOD q 0 * q 1] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (hcop 0 1 (by decide))).mp ⟨h0, h1⟩
    have h012 : a.val ≡ b.val [MOD N] :=
      (Nat.modEq_and_modEq_iff_modEq_mul
        (Nat.Coprime.mul_left (hcop 0 2 (by decide)) (hcop 1 2 (by decide)))).mp ⟨h01, h2⟩
    apply ZMod.val_injective N
    unfold Nat.ModEq at h012
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h012
  have hFbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hFinj, ?_⟩
    simp only [ZMod.card, Fintype.card_prod, hN, mul_assoc]
  let B : ∀ i, Finset (ZMod (q i)) := fun i => univ.filter (fun y => quadraticChar (ZMod (q i)) y = e i)
  have hcardA : A.card = (B 0).card * (B 1).card * (B 2).card := by
    have hmap : A.map ⟨F, hFinj⟩ = B 0 ×ˢ (B 1 ×ˢ B 2) := by
      ext ⟨y0, y1, y2⟩
      simp only [Finset.mem_map, Finset.mem_product, A, B, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨a, ha, hFa⟩
        simp only [F, Prod.mk.injEq] at hFa
        obtain ⟨r0, r1, r2⟩ := hFa
        refine ⟨?_, ?_, ?_⟩
        · rw [← r0, ← hda_jac_qc]; exact ha 0
        · rw [← r1, ← hda_jac_qc]; exact ha 1
        · rw [← r2, ← hda_jac_qc]; exact ha 2
      · rintro ⟨h0, h1, h2⟩
        obtain ⟨a, ha⟩ := hFbij.2 (y0, y1, y2)
        refine ⟨a, ?_, ha⟩
        simp only [F, Prod.mk.injEq] at ha
        obtain ⟨r0, r1, r2⟩ := ha
        intro i; fin_cases i
        · show jacobiSym (a.val : ℤ) (q 0) = e 0
          rw [hda_jac_qc, r0]; exact h0
        · show jacobiSym (a.val : ℤ) (q 1) = e 1
          rw [hda_jac_qc, r1]; exact h1
        · show jacobiSym (a.val : ℤ) (q 2) = e 2
          rw [hda_jac_qc, r2]; exact h2
    rw [← Finset.card_map ⟨F, hFinj⟩, hmap, Finset.card_product, Finset.card_product, mul_assoc]
  have hB : ∀ i, 2 * (B i).card = q i - 1 := fun i => hda_card_qc (q i) (hne2 i) (e i) (he i)
  have htot : N.totient = (q 0 - 1) * (q 1 - 1) * (q 2 - 1) := by
    rw [hN, Nat.totient_mul (Nat.Coprime.mul_left (hcop 0 2 (by decide)) (hcop 1 2 (by decide))),
      Nat.totient_mul (hcop 0 1 (by decide)), Nat.totient_prime (hp 0).1,
      Nat.totient_prime (hp 1).1, Nat.totient_prime (hp 2).1]
  have h8 : 8 * A.card = N.totient := by
    rw [hcardA, htot, ← hB 0, ← hB 1, ← hB 2]; ring
  have hphi : (0 : ℝ) < N.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hNpos)
  have hsumconst : ∑ a ∈ A, (1 / (N.totient : ℝ)) = 1 / 8 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have h8r : (8 : ℝ) * A.card = N.totient := by exact_mod_cast h8
    have hA0 : (A.card : ℝ) ≠ 0 := by intro h0; rw [h0] at h8r; linarith
    rw [← h8r]; field_simp

  have hS : ∀ a ∈ A, LogDensity {p : ℕ | (p : ZMod N) = a} (1 / (N.totient : ℝ)) :=
    fun a ha => hAP N a (hunit a ha)
  have hind : ∀ (f : ℕ → ℝ) (n : ℕ),
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = e i}}.indicator f n =
        ∑ a ∈ A, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator f n := by
    intro f n
    by_cases hn : n.Prime
    · by_cases hT : (∀ i, n ≠ q i) ∧ ∀ i, chiQ (q i) n = e i
      · have ha : (n : ZMod N) ∈ A := (hmem n).1 hT
        rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧
          ∀ i, chiQ (q i) p = e i}} from ⟨hn, hT⟩), Finset.sum_eq_single_of_mem (n : ZMod N) ha]
        · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = (n : ZMod N)}}
            from ⟨hn, rfl⟩)]
        · intro b _ hb
          exact Set.indicator_of_notMem (fun h => hb h.2.symm) _
      · rw [Set.indicator_of_notMem (fun h => hT h.2), Finset.sum_eq_zero]
        intro b hb
        apply Set.indicator_of_notMem
        rintro ⟨_, h⟩
        have h' : (n : ZMod N) = b := h
        exact hT ((hmem n).2 (h' ▸ hb))
    · rw [Set.indicator_of_notMem (fun h => hn h.1), Finset.sum_eq_zero]
      intro b _
      exact Set.indicator_of_notMem (fun h => hn h.1) _
  have hsumm : ∀ᶠ x in 𝓝[>] (1 : ℝ), ∀ a ∈ A,
      Summable ({p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x)) := by
    rw [Filter.eventually_all_finset]
    intro a ha
    have hpos : (0 : ℝ) < 1 / (N.totient : ℝ) := by positivity
    filter_upwards [(hS a ha).eventually (lt_mem_nhds hpos)] with x hx
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns, mul_zero] at hx
    exact lt_irrefl _ hx
  have heq : (fun x : ℝ => ∑ a ∈ A, (x - 1) * (∑' n : ℕ,
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x : ℝ => (x - 1) * (∑' n : ℕ,
        {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = e i}}.indicator
          (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)) := by
    filter_upwards [hsumm] with x hx
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hx]
    congr 1
    exact tsum_congr (fun n => (hind _ n).symm)
  have hlim := tendsto_finsetSum A (fun a ha => hS a ha)
  rw [hsumconst] at hlim
  exact hlim.congr' heq

end Formalism.HF.P

namespace Formalism.HF

theorem hostDensityArith_of (hAP : Formalism.HF.APLogDensity) (hLD : Formalism.HF.LogToDir) :
    Formalism.HF.HostDensityArith := by
  intro q hq g
  have h := Formalism.HF.P.hda_log hAP q hq g
  exact ⟨h, hLD _ _ h⟩

end Formalism.HF
end
end

-- bundled from Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
section
open NumberField Polynomial Matrix

noncomputable section

namespace Formalism.HF.P

lemma quad_not_sq_rat (a : ℤ) (ha : Squarefree a) (h1 : a ≠ 1) : ∀ b : ℚ, b ^ 2 ≠ (a : ℚ) := by
  intro b hb
  have hsq : IsSquare (a : ℚ) := ⟨b, by rw [← hb]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_intCast_iff.1 hsq
  have hu : IsUnit n := ha n ⟨1, by rw [hn, mul_one]⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (subst h; simp at hn; exact h1 hn)

theorem quadDiscr_ne_one (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a)
    (h4 : a % 4 = 1) (h1 : a ≠ 1) : discr K = a := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have hint : IsIntegral ℚ x := .of_finite ℚ x
  have hrank : Module.finrank ℚ K = 2 := by
    have := IntermediateField.adjoin.finrank hint
    rw [hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top'] at this
    exact this
  have htrq : ∀ q : ℚ, Algebra.trace ℚ K (algebraMap ℚ K q) = 2 * q := by
    intro q
    rw [Algebra.trace_algebraMap, hrank]; simp
  have htrlin : ∀ (q : ℚ) (z : K), Algebra.trace ℚ K (algebraMap ℚ K q * z) =
      q * Algebra.trace ℚ K z := by
    intro q z
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have htrx : Algebra.trace ℚ K x = 0 := by
    have hnc : (X ^ 2 - C (a : ℚ)).nextCoeff = 0 := by
      rw [nextCoeff, natDegree_X_pow_sub_C, coeff_sub, coeff_X_pow, coeff_C]; norm_num
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, hnc]; simp
  set ω : K := (1 + x) / 2 with hω
  have hω1 : ω = algebraMap ℚ K (1 / 2) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; ring
  have hω2 : ω * ω = algebraMap ℚ K ((1 + a) / 4) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; linear_combination (1 / 4 : K) * hx
  have htr1 : Algebra.trace ℚ K 1 = 2 := by
    rw [show (1 : K) = algebraMap ℚ K 1 by simp, htrq]; norm_num
  have htrω : Algebra.trace ℚ K ω = 1 := by
    rw [hω1, map_add, htrq, htrlin, htrx]; norm_num
  have htrωω : Algebra.trace ℚ K (ω * ω) = (1 + a) / 2 := by
    rw [hω2, map_add, htrq, htrlin, htrx]; ring
  have hdisc : Algebra.discr ℚ ![(1 : K), ω] = a := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, mul_one]
    rw [htr1, htrω, htrωω]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℤ, a = 4 * c + 1 := ⟨a / 4, by omega⟩
  have hcK : (a : K) = 4 * c + 1 := by rw [hc]; push_cast; ring
  have hωint : IsIntegral ℤ ω := by
    refine ⟨X ^ 2 - X - C c, ?_, ?_⟩
    · monicity!
    · rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast, hω]
      linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hcK
  let B := RingOfIntegers.basis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← hrank, Module.finrank_eq_card_basis (integralBasis K)]
  let e := Fintype.equivFinOfCardEq hcard
  let B' : Module.Basis (Fin 2) ℤ (𝓞 K) := B.reindex e
  let Cb : Module.Basis (Fin 2) ℚ K := (integralBasis K).reindex e
  have hC : ∀ i, Cb i = ((B' i : 𝓞 K) : K) := by
    intro i; simp [Cb, B', B, integralBasis_apply]
  let ω' : 𝓞 K := ⟨ω, hωint⟩
  let v : Fin 2 → 𝓞 K := ![1, ω']
  let P : Matrix (Fin 2) (Fin 2) ℤ := B'.toMatrix v
  have hv : ![(1 : K), ω] = Cb ᵥ* (P.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ K) := by
    have h0 := B'.toMatrix_map_vecMul v
    funext j
    have hj := congrArg (fun w : Fin 2 → 𝓞 K => ((w j : 𝓞 K) : K)) h0
    have hvj : ((v j : 𝓞 K) : K) = ![(1 : K), ω] j := by
      fin_cases j <;> rfl
    rw [← hvj, ← hj]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hC, P]
  have key : (a : ℚ) = ((P.det : ℤ) : ℚ) ^ 2 * (discr K : ℚ) := by
    rw [← hdisc, hv, Algebra.discr_of_matrix_vecMul, coe_discr, Module.Basis.coe_reindex,
      Algebra.discr_reindex]
    congr 2
    exact (RingHom.map_det (Int.castRingHom ℚ) P).symm
  have key' : a = P.det ^ 2 * discr K := by exact_mod_cast key
  have hu : IsUnit P.det := hsf P.det ⟨discr K, by rw [key']; ring⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (rw [key', h]; ring)

end Formalism.HF.P

theorem Formalism.HF.quadDiscr : Formalism.HF.QuadDiscr := by
  intro K _ _ a x hx hadj hsf h4
  by_cases h1 : a = 1
  · subst h1
    have hx1 : x * x = 1 := by rw [← sq, hx]; simp
    have hbot : x ∈ (⊥ : IntermediateField ℚ K) := by
      rcases mul_self_eq_one_iff.1 hx1 with h | h
      · rw [h]; exact IntermediateField.one_mem _
      · rw [h]; exact IntermediateField.neg_mem _ (IntermediateField.one_mem _)
    have htop : (⊥ : IntermediateField ℚ K) = ⊤ := by
      rw [← hadj, eq_comm]; exact IntermediateField.adjoin_simple_eq_bot_iff.2 hbot
    let e : ℚ ≃ₐ[ℚ] K := (IntermediateField.botEquiv ℚ K).symm.trans
      ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
    rw [← NumberField.discr_eq_discr_of_algEquiv ℚ e, NumberField.discr_rat]
  · exact Formalism.HF.P.quadDiscr_ne_one K a x hx hadj hsf h4 h1
end
end

