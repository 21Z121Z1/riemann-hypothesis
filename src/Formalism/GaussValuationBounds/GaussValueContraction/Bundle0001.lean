import Formalism.GaussValuationBounds.Statement
import Formalism.WachModuleLifts.WachModuleProofs.Bundle0001

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.ExponentSumIdentity
section
namespace Formalism.NOK

theorem expNonzero_proof : ExpNonzero := by
  intro g b hg hgb x hx
  simp only [Finset.mem_union, Finset.mem_Icc] at hx
  omega

theorem eTotal_proof : ETotal := by
  intro r s k g e hr hs hg he
  rw [max_eq_right (by nlinarith [mul_nonneg hg he])]; ring

theorem exponentSumIdentity : ExponentSumIdentity := by
  intro l b b' S E lam hl
  have h1 : l - 1 ≠ 0 := by linarith
  have h2 : l ≠ 0 := by linarith
  field_simp; ring

theorem slopeNum_proof : SlopeNum := by
  refine ⟨fun l hl => ?_, by norm_num⟩
  have h1 : 0 < l - 1 := by linarith
  rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by linarith)]
  nlinarith [sq_nonneg (l-13), mul_pos h1 h1, mul_pos (mul_pos h1 h1) h1, sq_nonneg l,
    mul_pos (mul_pos (mul_pos h1 h1) h1) h1]

end Formalism.NOK
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.SigBound
section
namespace Formalism.NOK

theorem sigBound_pow (L a : ℝ) (k : ℕ) (hL : 3 ≤ L) (ha : a = L - 1) :
    L * a ^ (k + 2) ≤ 3 / 2 * L ^ k * a ^ 3 := by
  have ha2 : 2 ≤ a := by linarith
  rcases k with _ | k
  · simp only [pow_zero, zero_add, mul_one]
    have : 0 ≤ a ^ 2 := by positivity
    nlinarith
  · have h1 : a ^ k ≤ L ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have h3 : 0 < a ^ 3 := by positivity
    have hLp : 0 < L := by linarith
    have e1 : L * a ^ (k + 1 + 2) = L * a ^ k * a ^ 3 := by ring
    have e2 : 3 / 2 * L ^ (k + 1) * a ^ 3 = 3 / 2 * L * L ^ k * a ^ 3 := by ring
    rw [e1, e2]
    have h4 : L * a ^ k * a ^ 3 ≤ L * L ^ k * a ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ h3.le
      exact mul_le_mul_of_nonneg_left h1 hLp.le
    have h5 : 0 ≤ L * L ^ k * a ^ 3 := by positivity
    nlinarith

theorem sigBound_proof : SigBound := by
  intro ℓ hℓ g h j hj
  unfold sigNOK
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hL3 : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  set L : ℝ := (ℓ : ℝ) with hL
  set a : ℝ := L - 1 with ha
  have ha2 : 2 ≤ a := by linarith
  have hapos : 0 < a := by linarith
  have hLpos : 0 < L := by linarith
  have hmle : (((h + 2 * g) / (ℓ - 1) : ℕ) : ℝ) ≤ ((h : ℝ) + 2 * g) / a := by
    have := Nat.cast_div_le (α := ℝ) (m := h + 2 * g) (n := ℓ - 1)
    have e : ((ℓ - 1 : ℕ) : ℝ) = a := by
      rw [Nat.cast_sub (by omega)]; simp [ha, hL]
    rw [e] at this; push_cast at this; exact this
  set m : ℕ := (h + 2 * g) / (ℓ - 1) with hm
  set H : ℝ := (h : ℝ) + 2 * g with hH
  have hH0 : 0 ≤ H := by positivity
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hm0 : (0 : ℝ) ≤ m := by positivity
  set P : ℝ := L ^ k with hP
  have hP1 : 1 ≤ P := one_le_pow₀ (by linarith)
  have hPpos : 0 < P := by linarith
  have hpow := sigBound_pow L a k hL3 ha

  have hq : L / a ^ 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have t1 : 3 * (g : ℝ) * L / a ^ 2 ≤ 9 / 4 * g := by
    have := mul_le_mul_of_nonneg_left hq hg0
    calc 3 * (g : ℝ) * L / a ^ 2 = 3 * ((g : ℝ) * (L / a ^ 2)) := by ring
      _ ≤ 9 / 4 * (g : ℝ) := by linarith
  have t2 : L / (P * a ^ 2) ≤ 3 / 4 := by
    calc L / (P * a ^ 2) ≤ L / (1 * a ^ 2) := by
          apply div_le_div_of_nonneg_left hLpos.le (by positivity)
          exact mul_le_mul_of_nonneg_right hP1 (by positivity)
      _ = L / a ^ 2 := by ring
      _ ≤ 3 / 4 := hq
  have t3 : H * L / (P * a ^ 3) ≤ 3 / 2 * H / a ^ (k + 1 + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : L * a ^ (k + 2) ≤ 3 / 2 * P * a ^ 3 := hpow
    calc H * L * a ^ (k + 1 + 1) = H * (L * a ^ (k + 2)) := by ring
      _ ≤ H * (3 / 2 * P * a ^ 3) := mul_le_mul_of_nonneg_left this hH0
      _ = 3 / 2 * H * (P * a ^ 3) := by ring
  have t4 : (m : ℝ) * L / (P * a ^ 2) ≤ H * L / (P * a ^ 3) := by
    have e : H * L / (P * a ^ 3) = (H / a) * L / (P * a ^ 2) := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hmle hLpos.le
  have hsplit : (3 * (g : ℝ) + ((m : ℝ) + 1) / P) * L / a ^ 2 =
      3 * (g : ℝ) * L / a ^ 2 + (m : ℝ) * L / (P * a ^ 2) + L / (P * a ^ 2) := by
    field_simp; ring
  have hX0 : 0 ≤ (3 * (g : ℝ) + ((m : ℝ) + 1) / P) * L / a ^ 2 := by positivity
  have hfl := Nat.floor_le hX0
  push_cast
  rw [hsplit] at hfl ⊢
  linarith

end Formalism.NOK
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.TruncationExponentBounds
section
namespace Formalism.NOK

theorem powMemSpanPow : PowContent := by
  intro A _ a X p N M z c hN hp hz
  obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hp
  obtain ⟨q, hqd⟩ : ∃ q, q = (M + N - 1) / N := ⟨_, rfl⟩
  rw [← hqd] at hz
  have hq : M ≤ N * q := by
    have h1 := Nat.div_add_mod (M + N - 1) N
    have h2 := Nat.mod_lt (M + N - 1) (by omega : 0 < N)
    rw [← hqd] at h1
    generalize N * q = w at h1 ⊢
    omega
  rw [add_pow]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_cases hci : c ≤ i
  · have hmem : (α * a) ^ i ∈ Ideal.span {a ^ c, X ^ M} := by
      rw [show (α * a) ^ i = (α ^ i * a ^ (i - c)) * a ^ c by
        rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hci]]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hmem)
  · have hle : M ≤ N * (z - i) := le_trans hq (Nat.mul_le_mul_left _ (by omega))
    have hmem : (β * X ^ N) ^ (z - i) ∈ Ideal.span {a ^ c, X ^ M} := by
      rw [show (β * X ^ N) ^ (z - i) = (β ^ (z - i) * X ^ (N * (z - i) - M)) * X ^ M by
        rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hle]]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)

theorem powMemSpanOfLe : RelVanish := by
  intro A _ ℓ X u p E M j r hM hE
  rw [Ideal.mem_span_singleton, mul_pow, mul_pow, ← Finset.prod_pow, mul_assoc]
  have h1 : X ^ M ∣ X ^ r := pow_dvd_pow X hM
  have h2 : ∏ s ∈ Finset.range j, p s ^ E ∣ ∏ s ∈ Finset.range j, (p s ^ (ℓ - 1)) ^ r :=
    Finset.prod_dvd_prod_of_dvd _ _ fun s _ => by
      rw [← pow_mul]
      exact pow_dvd_pow _ hE
  exact Dvd.dvd.mul_left (mul_dvd_mul h1 h2) _

private theorem prime_sub_one_mul_padicValNat_factorial_le (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) :
    ((ℓ : ℝ) - 1) * (padicValNat ℓ r.factorial : ℝ) ≤ r := by
  have h2 : (ℓ - 1) * padicValNat ℓ r.factorial ≤ r := by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have h1 : 1 ≤ ℓ := (Fact.out : ℓ.Prime).one_lt.le
  have h3 : (((ℓ - 1) * padicValNat ℓ r.factorial : ℕ) : ℝ) ≤ r := by exact_mod_cast h2
  push_cast [Nat.cast_sub h1] at h3
  exact h3

theorem truncationExponentBounds : SigNum := by
  intro ℓ _ hℓ E M j r hj
  have hℓ' : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hM0 : (0 : ℝ) ≤ (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by positivity
  have hsig : ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 < sigNOK ℓ E M j := by
    unfold sigNOK
    push_cast
    exact Nat.lt_floor_add_one _
  have hleg := prime_sub_one_mul_padicValNat_factorial_le ℓ r
  have hsub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  constructor
  · intro hr
    have hr' : ((ℓ : ℝ) - 1) * r < E := by
      have h := (Nat.cast_lt (α := ℝ)).2 hr
      push_cast [hsub] at h
      exact h
    have key : ((r + padicValNat ℓ r.factorial : ℕ) : ℝ) < sigNOK ℓ E M j := by
      refine lt_of_le_of_lt ?_ hsig
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hleg hL0.le, mul_le_mul_of_nonneg_right hr'.le (by linarith : (0 : ℝ) ≤ ℓ)]
    exact_mod_cast key
  · refine le_trans ?_ hsig.le
    rcases le_or_gt (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) 0 with h | h
    · rw [max_eq_left h, sub_zero, div_le_div_iff₀ hL0 (by positivity)]
      have h' : ((ℓ : ℝ) - 1) * r ≤ E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ ℓ * ((ℓ : ℝ) - 1))]
    · rw [max_eq_right h.le]
      have hneg : (ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2 < 0 := by nlinarith
      have e : (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) - (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) -
          ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
          (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) /
            ((ℓ : ℝ) - 1) ^ 2 := by
        field_simp
        ring
      have hn : (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) /
          ((ℓ : ℝ) - 1) ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg.le) (sq_nonneg _)
      linarith

theorem scaledPowMemSpan : RelCoeff := by
  intro A _ ℓ _ hℓ X u p E M j hj hp r
  set σ := sigNOK ℓ E M j with hσ
  set v := padicValNat ℓ r.factorial with hv
  set J := Ideal.span {(ℓ : A) ^ (r + v), X ^ M * ∏ s ∈ Finset.range j, p s ^ E} with hJ
  have hmem1 : (ℓ : A) ^ (r + v) ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have hmem2 : X ^ M * ∏ s ∈ Finset.range j, p s ^ E ∈ J :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  by_cases hA : r + v ≤ σ
  · rw [← Nat.sub_add_cancel hA, pow_add]
    exact J.mul_mem_right _ (J.mul_mem_left _ hmem1)
  rw [not_le] at hA
  have hℓ' : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hN0 : (0 : ℝ) < (ℓ : ℝ) ^ (j - 1) := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by positivity
  have hleg := prime_sub_one_mul_padicValNat_factorial_le ℓ r
  have hB := (truncationExponentBounds ℓ hℓ E M j r hj).2
  have h1 : (r : ℝ) + v ≤ r * ℓ / ((ℓ : ℝ) - 1) := by
    rw [le_div_iff₀ hL0]
    nlinarith [hleg]
  have hσr : (σ : ℝ) < r + v := by exact_mod_cast hA
  have hmx : max 0 (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) =
      ((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by
    apply max_eq_right
    by_contra hneg
    rw [not_le] at hneg
    rw [max_eq_left hneg.le] at hB
    linarith
  rw [hmx] at hB
  have hc : ((r + v - σ : ℕ) : ℝ) ≤ ((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by
    rw [Nat.cast_sub hA.le]
    push_cast
    linarith
  have hsub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  have hE : E ≤ (ℓ - 1) * r := by
    have h0 : (0 : ℝ) ≤ ((r + v - σ : ℕ) : ℝ) := Nat.cast_nonneg _
    have : (E : ℝ) ≤ ((ℓ - 1) * r : ℕ) := by
      push_cast [hsub]
      linarith
    exact_mod_cast this
  by_cases hMr : M ≤ r
  · have hv' := powMemSpanOfLe A ℓ X u p E M j r hMr hE
    have hle : Ideal.span {X ^ M * ∏ s ∈ Finset.range j, p s ^ E} ≤ J :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem2)
    exact J.mul_mem_left _ (hle hv')
  rw [not_le] at hMr
  obtain ⟨c, hcd⟩ : ∃ c, c = r + v - σ := ⟨_, rfl⟩
  obtain ⟨z, hzd⟩ : ∃ z, z = (ℓ - 1) * r - E := ⟨_, rfl⟩
  rw [← hcd] at hc
  have hzr : (z : ℝ) = ((ℓ : ℝ) - 1) * r - E := by
    rw [hzd, Nat.cast_sub hE]
    push_cast [hsub]
    ring
  have hN1 : 1 ≤ ℓ ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have hcz : c ≤ z := by
    have : (c : ℝ) ≤ z := by rw [hzr]; linarith
    exact_mod_cast this
  have hMN : M - r ≤ (z - c) * ℓ ^ (j - 1) := by
    have hreal : ((M - r : ℕ) : ℝ) ≤ ((z - c : ℕ) : ℝ) * ((ℓ ^ (j - 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hMr.le, Nat.cast_sub hcz]
      push_cast
      have hdiv : (M : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ z - c := by rw [hzr]; linarith
      rw [div_le_iff₀ hN0] at hdiv
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      linarith
    exact_mod_cast hreal
  have hz : c + (M - r + ℓ ^ (j - 1) - 1) / ℓ ^ (j - 1) ≤ z + 1 := by
    have hlt : (M - r + ℓ ^ (j - 1) - 1) / ℓ ^ (j - 1) < z - c + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega), add_mul, one_mul]
      generalize (z - c) * ℓ ^ (j - 1) = w at hMN ⊢
      omega
    omega
  have hpz := powMemSpanPow A (ℓ : A) X (p (j - 1)) (ℓ ^ (j - 1)) (M - r) z c hN1 hp hz
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hpz
  have hprod : ∏ s ∈ Finset.range j, (p s ^ (ℓ - 1)) ^ r = (∏ s ∈ Finset.range j, p s ^ E) *
      (p (j - 1) ^ z * ∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) := by
    rw [Finset.mul_prod_erase (Finset.range j) (fun s => p s ^ z) (Finset.mem_range.mpr (by omega)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← pow_mul, ← pow_add, hzd, Nat.add_sub_cancel' hE]
  have hX : X ^ M = X ^ r * X ^ (M - r) := by rw [← pow_add, Nat.add_sub_cancel' hMr.le]
  have hl : (ℓ : A) ^ (r + v) = (ℓ : A) ^ σ * (ℓ : A) ^ c := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, ← Finset.prod_pow, hprod, ← hαβ]
  convert J.add_mem (J.mul_mem_left (α * u ^ r * (∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) * X ^ r *
      ∏ s ∈ Finset.range j, p s ^ E) hmem1)
    (J.mul_mem_left (β * u ^ r * (∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) * (ℓ : A) ^ σ) hmem2) using 1
  rw [hX, hl]
  ring

end Formalism.NOK
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.WStepContract
section
namespace Formalism.NOK

theorem wStep_mono {ℓ H H' lam a a' : ℝ} (hℓ : 3 ≤ ℓ) (hH : H ≤ H') (ha : a ≤ a') :
    WStep ℓ H lam a ≤ WStep ℓ H' lam a' := by
  have hd : 0 < ℓ - 1 := by linarith
  have hD : 0 < ℓ ^ 2 - ℓ + 1 := by nlinarith
  unfold WStep
  have h1 : H / (ℓ - 1) ≤ H' / (ℓ - 1) := div_le_div_of_nonneg_right hH hd.le
  have h2 : (ℓ * a + (ℓ - 1) * (H + lam)) / (ℓ ^ 2 - ℓ + 1) ≤
      (ℓ * a' + (ℓ - 1) * (H' + lam)) / (ℓ ^ 2 - ℓ + 1) := by
    apply div_le_div_of_nonneg_right _ hD.le
    have : ℓ * a ≤ ℓ * a' := mul_le_mul_of_nonneg_left ha (by linarith)
    have : (ℓ - 1) * (H + lam) ≤ (ℓ - 1) * (H' + lam) :=
      mul_le_mul_of_nonneg_left (by linarith) hd.le
    linarith
  have := max_le_max h1 h2
  linarith

theorem wStep_contract {ℓ H lam z t : ℝ} (hℓ : 3 ≤ ℓ) (hlam : 0 ≤ lam) (hz : 0 ≤ z)
    (hH : H + lam = (ℓ - 1) * t) :
    WStep ℓ H lam ((ℓ - 1) * z + t + 2) ≤ z + t + 2 := by
  have hd : 0 < ℓ - 1 := by linarith
  have hD : 0 < ℓ ^ 2 - ℓ + 1 := by nlinarith
  have e1 : H / (ℓ - 1) ≤ z + t + 1 := by
    rw [div_le_iff₀ hd]; nlinarith
  have e2 : (ℓ * ((ℓ - 1) * z + t + 2) + (ℓ - 1) * (H + lam)) / (ℓ ^ 2 - ℓ + 1) ≤ z + t + 1 := by
    rw [div_le_iff₀ hD, hH]; nlinarith
  unfold WStep
  have := max_le e1 e2
  linarith

theorem wCycle_proof : WCycle := by
  intro n _ ℓ lam Hm a H hℓ hlam hH hstep i
  have hd : 0 < ℓ - 1 := by linarith
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  have hm : ∀ i, a i ≤ a i₀ := fun i => hi₀ i (Finset.mem_univ i)
  have h1 := hstep (i₀ + 1)
  rw [add_sub_cancel_right] at h1
  have h2 : a i₀ ≤ WStep ℓ Hm lam (a i₀) := le_trans h1 (wStep_mono hℓ (hH _) (hm _))
  have key : a i₀ ≤ (Hm + lam) / (ℓ - 1) + 2 := by
    unfold WStep at h2
    have h3 : a i₀ - 1 ≤ max (Hm / (ℓ - 1)) ((ℓ * a i₀ + (ℓ - 1) * (Hm + lam)) / (ℓ ^ 2 - ℓ + 1)) := by
      linarith
    rcases le_max_iff.mp h3 with h4 | h4
    · have : Hm / (ℓ - 1) ≤ (Hm + lam) / (ℓ - 1) := div_le_div_of_nonneg_right (by linarith) hd.le
      linarith
    · have hD : 0 < ℓ ^ 2 - ℓ + 1 := by nlinarith
      rw [le_div_iff₀ hD] at h4
      have h5 : a i₀ * (ℓ - 1) ≤ Hm + lam + 2 * (ℓ - 1) := by
        by_contra hc
        rw [not_le] at hc
        have := mul_lt_mul_of_pos_left hc hd
        nlinarith
      have : a i₀ ≤ (Hm + lam + 2 * (ℓ - 1)) / (ℓ - 1) := by rw [le_div_iff₀ hd]; exact h5
      have e : (Hm + lam + 2 * (ℓ - 1)) / (ℓ - 1) = (Hm + lam) / (ℓ - 1) + 2 := by
        field_simp
      linarith
  exact le_trans (hm i) key

theorem wThin_proof : WThin := by
  intro ℓ lam G X₀ j x H hℓ hlam hG hX₀ hx0 hH hstep
  have hd : 0 < ℓ - 1 := by linarith
  set t := (2 * G + lam) / (ℓ - 1) with ht
  have htH : 2 * G + lam = (ℓ - 1) * t := by rw [ht]; field_simp
  have claim : ∀ k, k ≤ j → x k ≤ X₀ / (ℓ - 1) ^ k + t + 2 := by
    intro k
    induction k with
    | zero =>
      intro _
      have : 0 ≤ t := div_nonneg (by linarith) hd.le
      simp only [pow_zero, div_one]
      linarith
    | succ k ih =>
      intro hk
      have hk' : k < j := by omega
      have hprev := ih hk'.le
      set z := X₀ / (ℓ - 1) ^ (k + 1) with hzdef
      have hz : 0 ≤ z := div_nonneg hX₀ (pow_nonneg hd.le _)
      have hzk : X₀ / (ℓ - 1) ^ k = (ℓ - 1) * z := by
        rw [hzdef, pow_succ]; field_simp
      rw [hzk] at hprev
      calc x (k + 1) ≤ WStep ℓ (H k) lam (x k) := hstep k hk'
        _ ≤ WStep ℓ (2 * G) lam ((ℓ - 1) * z + t + 2) := wStep_mono hℓ (hH k hk') hprev
        _ ≤ z + t + 2 := wStep_contract hℓ hlam hz htH
  have := claim j le_rfl
  linarith

theorem wCut_proof : WCut := by
  intro n _ ℓ lam h G a H c j hℓ hlam hh hG hH hthin hstep
  have hd : 0 < ℓ - 1 := by linarith
  set X₀ := (2 * h + lam) / (ℓ - 1) + 2 with hX₀def
  have hX₀ : 0 ≤ X₀ := by
    have : 0 ≤ (2 * h + lam) / (ℓ - 1) := div_nonneg (by linarith) hd.le
    linarith
  have hA : ∀ i, a i ≤ X₀ := wCycle_proof n ℓ lam (2 * h) a H hℓ hlam hH hstep
  have := wThin_proof ℓ lam G X₀ j (fun k => a (c + ((j - k : ℕ) : ZMod n)))
    (fun k => H (c + ((j - k : ℕ) : ZMod n))) hℓ hlam hG hX₀ (hA _)
    (fun k hk => hthin (j - k) (by omega) (by omega))
    (by
      intro k hk
      have e1 : ((j - k : ℕ) : ZMod n) = ((j - (k + 1) : ℕ) : ZMod n) + 1 := by
        rw [show j - k = (j - (k + 1)) + 1 by omega]
        push_cast
        ring
      have e2 : c + ((j - k : ℕ) : ZMod n) - 1 = c + ((j - (k + 1) : ℕ) : ZMod n) := by
        rw [e1]; ring
      have h1 := hstep (c + ((j - k : ℕ) : ZMod n))
      rw [e2] at h1
      exact h1)
  simpa using this

end Formalism.NOK
end

