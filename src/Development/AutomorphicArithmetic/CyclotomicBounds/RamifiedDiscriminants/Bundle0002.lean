import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
section
open NumberField IsDedekindDomain

namespace UpperTheory.Ram

private theorem mem_sq_of_sqrt {E : Type} [Field E] [NumberField E] {p : ℕ} {a : E} (ha : a ^ 2 = -(p : E))
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hv : (p : 𝓞 E) ∈ P) : (p : 𝓞 E) ∈ P ^ 2 := by
  have hint : IsIntegral ℤ a := by
    refine IsIntegral.of_pow two_pos ?_
    rw [ha]
    have e : -(p : E) = algebraMap ℤ E (-(p : ℤ)) := by simp
    rw [e]
    exact isIntegral_algebraMap
  set b : 𝓞 E := ⟨a, hint⟩ with hb
  have hb2 : b ^ 2 = -(p : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact ha
  have hbP : b ∈ P := by
    apply hP.mem_of_pow_mem 2
    rw [hb2]
    exact P.neg_mem hv
  have hsq : b ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hbP 2
  rw [hb2] at hsq
  simpa using (P ^ 2).neg_mem hsq

variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

theorem mem_sq_of_dvd_condN {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q * H.d) (P : Ideal (𝓞 H.E)) (hP : P.IsPrime)
    (hv : (p : 𝓞 H.E) ∈ P) : (p : 𝓞 H.E) ∈ P ^ 2 := by
  haveI := hP
  have hc : p ∣ H.condN := h
  rcases (H.dvd_condN_iff hp).1 hc with hq | rfl | rfl
  · exact H.toHostAx.mem_sq_of_dvd_QS H.QS_exact hp hq P hv
  · exact mem_sq_of_sqrt H.sqq_sq P hP hv
  · exact mem_sq_of_sqrt H.sqd_sq P hP hv

theorem exists_place_over (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal := by
  haveI : Fact p.Prime := ⟨hp⟩
  set pZ : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)}
  haveI : pZ.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨⟨P, hP, hl⟩⟩ := (inferInstance : Nonempty (pZ.primesOver (𝓞 E)))
  have hz : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
    rw [← (Ideal.liesOver_iff P pZ).1 hl]
    exact Ideal.subset_span rfl
  have hmem : ((p : ℕ) : 𝓞 E) ∈ P := by simpa [Ideal.under] using hz
  have hnb : P ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  exact ⟨⟨P, hP, hnb⟩, hmem⟩

theorem not_dvd_condN_of_unram {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ w.asIdeal → (p : 𝓞 H.E) ∉ w.asIdeal ^ 2) :
    ¬ p ∣ H.QS * H.q * H.d := fun hd => by
  obtain ⟨w, hw⟩ := exists_place_over H.E hp
  exact h w hw (mem_sq_of_dvd_condN H hp hd w.asIdeal w.isPrime hw)

end UpperTheory.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunDen
section
open NumberField IsDedekindDomain Finset
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp n_vp c_vp a0 delta_vp)

noncomputable section

namespace UpperTheory.Ram.Fun

theorem sum_ceil_off_le {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (GlobalTheory.CMVal.OF E)) (z : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime)
    (ha : ∀ l ∈ S, a0 𝔣 l = 0) {N : ℕ} (hN : N ≠ 0) (hd : ∀ l : ℕ, l.Prime → (l : ℤ) ∣ discr E → l ∣ N) {A : ℝ}
    (h1 : Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ≤ A) (h2 : Real.log N ≤ A) :
    ∑ l ∈ S, ((⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) : ℝ) * Real.log l ≤ ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l +
      (((2 * s * Fintype.card I : ℕ) : ℝ) + 5 * (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) + 1) * A := by
  classical
  have hK0 : (0 : ℝ) ≤ ((2 * s * Fintype.card I : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ A := le_trans (Real.log_natCast_nonneg N) h2
  have hlog : ∀ l ∈ S, 0 ≤ Real.log (l : ℝ) := fun l hl =>
    Real.log_nonneg (by exact_mod_cast (hS l hl).one_lt.le)
  have hdl : ∀ l, 0 ≤ delta_vp E l := by
    intro l
    unfold delta_vp
    positivity
  have hc0 : ∀ l, 0 ≤ c_vp 𝔣 l := by
    intro l
    unfold c_vp
    split_ifs
    · positivity
    · exact hdl l
  have hcle : ∀ l ∈ S, c_vp 𝔣 l ≤ delta_vp E l := by
    intro l hl
    unfold c_vp
    split_ifs
    · rw [ha l hl]
      simpa using hdl l
    · exact le_rfl
  have ht : ∀ l : ℕ, ((if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0) ≤ 3 / 2 := by
    intro l
    split_ifs <;> norm_num
  have hn_eq : ∀ l, n_vp d s κ 𝔣 l = 0 ∨ n_vp d s κ 𝔣 l =
      ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l + (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) *
        (2 * c_vp 𝔣 l + 1 + ((if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0)) := by
    intro l
    by_cases h : c_vp 𝔣 l = 0
    · left
      unfold n_vp
      rw [if_pos h]
    · right
      unfold n_vp
      rw [if_neg h]
      rfl
  have hn0 : ∀ l, 0 ≤ n_vp d s κ 𝔣 l := by
    intro l
    rcases hn_eq l with h | h
    · rw [h]
    · rw [h]
      have h1 := mul_nonneg hK0 (hc0 l)
      have h3 : (0 : ℝ) ≤ (if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0 := by
        split_ifs <;> norm_num
      have h2 := mul_nonneg hk0 (by linarith [hc0 l] : (0 : ℝ) ≤ 2 * c_vp 𝔣 l + 1 +
        ((if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0))
      linarith
  have hceil : ∀ l ∈ S, ((⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) : ℝ) =
      (cE_vp l z : ℝ) + (⌈n_vp d s κ 𝔣 l⌉₊ : ℝ) := by
    intro l hl
    have e : betaBound_vp d s κ 𝔣 z l / 12 = n_vp d s κ 𝔣 l + ((cE_vp l z : ℕ) : ℝ) := by
      unfold betaBound_vp
      rw [ha l hl]
      push_cast
      ring
    rw [e, Nat.ceil_add_natCast (hn0 l)]
    push_cast
    ring
  have hsplit : ∑ l ∈ S, ((⌈n_vp d s κ 𝔣 l⌉₊ : ℕ) : ℝ) * Real.log l =
      ∑ l ∈ S.filter (fun l => c_vp 𝔣 l ≠ 0), ((⌈n_vp d s κ 𝔣 l⌉₊ : ℕ) : ℝ) * Real.log l := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro l _
    split_ifs with h
    · rfl
    · have h0 : n_vp d s κ 𝔣 l = 0 := by
        unfold n_vp
        rw [if_pos (not_not.mp h)]
      simp [h0]
  have hsubS : S.filter (fun l => c_vp 𝔣 l ≠ 0) ⊆ S := Finset.filter_subset _ _
  have hcA : ∑ l ∈ S.filter (fun l => c_vp 𝔣 l ≠ 0), c_vp 𝔣 l * Real.log l ≤ A := by
    calc ∑ l ∈ S.filter (fun l => c_vp 𝔣 l ≠ 0), c_vp 𝔣 l * Real.log l
        ≤ ∑ l ∈ S, c_vp 𝔣 l * Real.log l := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubS
          intro l hl _
          exact mul_nonneg (hc0 l) (hlog l hl)
      _ ≤ ∑ l ∈ S, delta_vp E l * Real.log l := by
          apply Finset.sum_le_sum
          intro l hl
          exact mul_le_mul_of_nonneg_right (hcle l hl) (hlog l hl)
      _ ≤ Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) := by
          have := sum_delta_log_le E S hS
          simpa [delta_vp] using this
      _ ≤ A := h1
  have hlA : ∑ l ∈ S.filter (fun l => c_vp 𝔣 l ≠ 0), Real.log (l : ℝ) ≤ A := by
    refine le_trans (sum_log_le_of_dvd hN _ ?_) h2
    intro l hl
    rw [Finset.mem_filter] at hl
    obtain ⟨hlS, hne⟩ := hl
    refine ⟨hS l hlS, ?_⟩
    apply hd l (hS l hlS)
    by_contra hnd
    apply hne
    unfold c_vp
    split_ifs
    · rw [ha l hlS]
      simp
    · unfold delta_vp
      haveI : Fact l.Prime := ⟨hS l hlS⟩
      rw [padicValInt.eq_zero_of_not_dvd hnd]
      simp
  have hmain := sum_ceil_nl_le (S.filter (fun l => c_vp 𝔣 l ≠ 0)) (n_vp d s κ 𝔣) (c_vp 𝔣)
    (fun l => (if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0)
    hK0 hk0 (fun l _ => hc0 l) (fun l _ => ht l)
    (fun l _ => hn0 l) (fun l _ => hn_eq l) hcA hlA
  calc ∑ l ∈ S, ((⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) : ℝ) * Real.log l
      = ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l +
          ∑ l ∈ S, ((⌈n_vp d s κ 𝔣 l⌉₊ : ℕ) : ℝ) * Real.log l := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro l hl
        rw [hceil l hl]
        ring
    _ ≤ ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l +
          (((2 * s * Fintype.card I : ℕ) : ℝ) + 5 * (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) + 1) * A := by
        rw [hsplit]
        have hkA := mul_nonneg hk0 hA
        nlinarith [hmain]

end UpperTheory.Ram.Fun

end
end

