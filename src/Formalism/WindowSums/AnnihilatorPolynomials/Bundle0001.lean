import Formalism.WindowSums.Statement

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.DistinctTerms
section
noncomputable section

namespace Formalism.WindowSums

open PowerSeries

theorem mem_span_iff_of_distinct_exponents : DistinctTerms := by
  intro O _ _ ϖ hϖ hnu ι I w e m B s hw he
  classical
  constructor
  · intro hmem
    by_contra hbad
    push_neg at hbad
    obtain ⟨i₁, hi₁, hb₁, hs₁⟩ := hbad
    have hJne : (I.filter fun i => e i < B ∧ m i < s).Nonempty :=
      ⟨i₁, Finset.mem_filter.mpr ⟨hi₁, hb₁, hs₁⟩⟩
    obtain ⟨i₀, hi₀J, hmin⟩ := (I.filter fun i => e i < B ∧ m i < s).exists_min_image e hJne
    obtain ⟨hi₀, hB, hs⟩ := Finset.mem_filter.mp hi₀J
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    have hcoef := congrArg (PowerSeries.coeff (e i₀)) hab
    rw [map_add, mul_comm a, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add,
      PowerSeries.coeff_mul_C, map_sum] at hcoef
    have hterm : ∀ i ∈ I, PowerSeries.coeff (e i₀) (w i * X ^ e i * C (ϖ ^ m i)) =
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      intro i _
      rw [PowerSeries.coeff_mul_C, mul_comm (w i), PowerSeries.coeff_X_pow_mul']
    rw [Finset.sum_congr rfl hterm, ← Finset.add_sum_erase _ _ hi₀, if_pos le_rfl,
      Nat.sub_self] at hcoef
    have hrest : ϖ ^ s ∣ ∑ i ∈ I.erase i₀,
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      refine Finset.dvd_sum fun i hi => ?_
      obtain ⟨hne, hiI⟩ := Finset.mem_erase.mp hi
      by_cases hle : e i ≤ e i₀
      · rw [if_pos hle]
        have hlt : e i < e i₀ := lt_of_le_of_ne hle fun h => hne (he hiI hi₀ h)
        have hms : s ≤ m i := by
          by_contra hms
          push_neg at hms
          have := hmin i (Finset.mem_filter.mpr ⟨hiI, by omega, hms⟩)
          omega
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hms) _
      · rw [if_neg hle, zero_mul]
        exact dvd_zero _
    have hdvd : ϖ ^ s ∣ PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ := by
      have h2 : PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ =
          PowerSeries.coeff (e i₀) b * ϖ ^ s - ∑ i ∈ I.erase i₀,
            (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
        rw [hcoef]; ring
      rw [h2]
      exact dvd_sub (dvd_mul_left _ _) hrest
    have hu : IsUnit (PowerSeries.coeff 0 (w i₀)) := by
      have := (hw i₀ hi₀).map (PowerSeries.constantCoeff (R := O))
      simpa using this
    have hsplit : ϖ ^ s = ϖ ^ m i₀ * ϖ ^ (s - m i₀) := by
      rw [← pow_add, Nat.add_sub_cancel' hs.le]
    rw [hsplit, mul_comm (PowerSeries.coeff 0 (w i₀))] at hdvd
    have hd2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ)).mp hdvd
    have hd3 : ϖ ∣ PowerSeries.coeff 0 (w i₀) :=
      (dvd_pow_self ϖ (by omega)).trans hd2
    exact hnu (isUnit_of_dvd_unit hd3 hu)
  · intro h
    refine Ideal.sum_mem _ fun i hi => ?_
    rcases h i hi with hb | hs
    · have hx : (X : PowerSeries O) ^ B ∈
          Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert _ _)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = X ^ B * (w i * X ^ (e i - B) * C (ϖ ^ m i)) := by
        rw [show e i = B + (e i - B) by omega, pow_add]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hx
    · have hc : C (ϖ ^ s) ∈ Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = C (ϖ ^ s) * (w i * X ^ e i * C (ϖ ^ (m i - s))) := by
        rw [show m i = s + (m i - s) by omega, pow_add, map_mul]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hc

end Formalism.WindowSums
end
end

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.EvalOneSmulDecomposition
section
namespace Formalism.WindowSums

open Polynomial

theorem annihilatorPoly_kills : KillerKills := by
  intro ℓ _ c ell JJ V _ _ T
  refine ⟨?_, ?_⟩
  · rintro x ⟨i, hi, hx⟩
    have hsplit : PP ℓ c ell JJ = ((∏ k ∈ (JJ.erase 0).erase i, (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (k * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
        ∑ k ∈ Finset.range (ℓ ^ ell), Polynomial.X ^ k) * (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
      unfold PP
      rw [← Finset.mul_prod_erase _ _ hi]
      ring
    have hk : Polynomial.aeval T (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) x = 0 := by
      simp [hx]
    rw [hsplit, map_mul, Module.End.mul_apply, hk, map_zero]
  · intro v hv
    have hS : Polynomial.aeval T (∑ k ∈ Finset.range (ℓ ^ ell), (Polynomial.X : Polynomial ℤ_[ℓ]) ^ k)
        (T v - v) = 0 := by
      have h1 : T v - v = Polynomial.aeval T (Polynomial.X - 1 : Polynomial ℤ_[ℓ]) v := by simp
      rw [h1, ← Module.End.mul_apply, ← map_mul, geom_sum_mul]
      simp [hv]
    unfold PP
    rw [map_mul, Module.End.mul_apply, hS, map_zero]

end Formalism.WindowSums
end

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.FirstCoefficientBoundHolds
section
noncomputable section

namespace Formalism.WindowSums

open PowerSeries

namespace AnnihilatorQuotientResidues

variable {O : Type} [CommRing O]

lemma map_mk_eq_zero_iff (ϖ : O) (f : PowerSeries O) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 ↔ PowerSeries.C ϖ ∣ f := by
  constructor
  · intro h
    have hc : ∀ n, ∃ z, z * ϖ = PowerSeries.coeff n f := by
      intro n
      have h1 := congrArg (PowerSeries.coeff n) h
      rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact Ideal.mem_span_singleton'.mp h1
    refine ⟨PowerSeries.mk fun n => Classical.choose (hc n), ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_comm]
    exact (Classical.choose_spec (hc n)).symm
  · rintro ⟨g, rfl⟩
    rw [map_mul, PowerSeries.map_C,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self ϖ), map_zero, zero_mul]

lemma mk_self (ϖ : O) : Ideal.Quotient.mk (Ideal.span {ϖ}) ϖ = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self ϖ)

lemma residue_map_p1_eq (ℓ : ℕ) (ε u : PowerSeries O) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) (p1 ℓ ε u) =
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) u * PowerSeries.X ^ ℓ := by
  rw [p1, map_add, map_mul, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, mk_self,
    map_zero, zero_mul, zero_add]

variable [IsDomain O] [IsDiscreteValuationRing O]

lemma C_ne_zero {ℓ : ℕ} (hℓ : Irreducible (ℓ : O)) : (PowerSeries.C (ℓ : O)) ≠ 0 := by
  intro h
  apply hℓ.ne_zero
  simpa using congrArg PowerSeries.constantCoeff h

lemma nzd {ℓ : ℕ} (hℓ : Irreducible (ℓ : O)) (ε u : PowerSeries O) (hu : IsUnit u) (y : ℕ) :
    ∀ (t : ℕ) (g : PowerSeries O), PowerSeries.C (ℓ : O) ^ t ∣ p1 ℓ ε u ^ y * g →
      PowerSeries.C (ℓ : O) ^ t ∣ g := by
  have : (Ideal.span {(ℓ : O)}).IsPrime := (PrincipalIdealRing.isMaximal_of_irreducible hℓ).isPrime
  intro t
  induction t with
  | zero => intro g _; simp
  | succ t ih =>
    intro g h
    obtain ⟨g1, rfl⟩ := ih g (dvd_trans (pow_dvd_pow _ (Nat.le_succ t)) h)
    have hL := C_ne_zero hℓ
    rw [pow_succ] at h ⊢
    have h2 : PowerSeries.C (ℓ : O) ∣ p1 ℓ ε u ^ y * g1 := by
      rw [show p1 ℓ ε u ^ y * (PowerSeries.C (ℓ : O) ^ t * g1) =
        PowerSeries.C (ℓ : O) ^ t * (p1 ℓ ε u ^ y * g1) by ring] at h
      exact (mul_dvd_mul_iff_left (pow_ne_zero t hL)).mp h
    have h3 := (map_mk_eq_zero_iff _ _).mpr h2
    rw [map_mul, map_pow, residue_map_p1_eq] at h3
    have h4 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) g1 = 0 := by
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exfalso
        exact pow_ne_zero _ (mul_ne_zero (hu.map _).ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)) h4
      · exact h4
    exact mul_dvd_mul_left _ ((map_mk_eq_zero_iff _ _).mp h4)

lemma core {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : Irreducible (ℓ : O)) (ε u : PowerSeries O) (hu : IsUnit u)
    (y r N μ : ℕ) (hr : r < ℓ) (hN : N ≤ y) (m : ℕ → ℕ) (w : ℕ → PowerSeries O)
    (j0 : ℕ) (hj0 : j0 < N) (hw0 : IsUnit (w j0)) (hm0 : m j0 = μ)
    (hmge : ∀ j < N, μ ≤ m j) (hlt : ∀ j < j0, μ < m j) :
    (∑ j ∈ Finset.range N, PowerSeries.C (ℓ : O) ^ m j * w j * PowerSeries.X ^ r * p1 ℓ ε u ^ j) ∉
      Ideal.span {p1 ℓ ε u ^ y, PowerSeries.C (ℓ : O) ^ (μ + 1)} := by
  have : (Ideal.span {(ℓ : O)}).IsPrime := (PrincipalIdealRing.isMaximal_of_irreducible hℓ).isPrime
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  intro hmem
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
  set L := PowerSeries.C (ℓ : O) with hLdef
  set P := p1 ℓ ε u with hPdef
  set φ := PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) with hφ
  set E := ∑ j ∈ Finset.range N, L ^ (m j - μ) * w j * PowerSeries.X ^ r * P ^ j with hE
  have hFE : (∑ j ∈ Finset.range N, L ^ m j * w j * PowerSeries.X ^ r * P ^ j) = L ^ μ * E := by
    rw [hE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := hmge j (Finset.mem_range.mp hj)
    conv_lhs => rw [show m j = μ + (m j - μ) by omega, pow_add]
    ring
  rw [hFE] at hab
  have hdvd : L ^ μ ∣ P ^ y * a := ⟨E - b * L, by linear_combination hab⟩
  obtain ⟨a', rfl⟩ := nzd hℓ ε u hu y μ a hdvd
  have hL : L ≠ 0 := C_ne_zero hℓ
  have hE2 : E = a' * P ^ y + b * L := by
    have : L ^ μ * E = L ^ μ * (a' * P ^ y + b * L) := by rw [← hab]; ring
    exact mul_left_cancel₀ (pow_ne_zero μ hL) this
  have hφL : φ L = 0 := by rw [hφ, hLdef, PowerSeries.map_C, mk_self, map_zero]
  have key := congrArg (fun f => PowerSeries.coeff (r + ℓ * j0) (φ f)) hE2
  have hR : PowerSeries.coeff (r + ℓ * j0) (φ (a' * P ^ y + b * L)) = 0 := by
    have h1 : ℓ * (j0 + 1) ≤ ℓ * y := Nat.mul_le_mul_left ℓ (by omega)
    rw [map_add, map_mul, map_mul, map_pow, hPdef, residue_map_p1_eq, hφL, mul_zero, add_zero, mul_pow,
      ← pow_mul, ← mul_assoc, PowerSeries.coeff_mul_X_pow', if_neg]
    intro h2
    rw [Nat.mul_succ] at h1
    linarith
  have hterm : ∀ j, φ (L ^ (m j - μ) * w j * PowerSeries.X ^ r * P ^ j) =
      (φ L ^ (m j - μ) * φ (w j) * φ u ^ j) * PowerSeries.X ^ (r + ℓ * j) := by
    intro j
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, hPdef, residue_map_p1_eq, PowerSeries.map_X]
    ring
  have hLft : PowerSeries.coeff (r + ℓ * j0) (φ E) ≠ 0 := by
    rw [hE, map_sum, map_sum, Finset.sum_eq_single j0]
    · rw [hterm, PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hm0, Nat.sub_self, pow_zero, one_mul]
      exact ((hw0.map φ).mul ((hu.map φ).pow j0)).map PowerSeries.constantCoeff |>.ne_zero
    · intro j hj hne
      rw [hterm]
      rcases Nat.lt_or_gt_of_ne hne with hlt' | hgt
      · have := hlt j hlt'
        rw [hφL, zero_pow (by omega), zero_mul, zero_mul, zero_mul, map_zero]
      · rw [PowerSeries.coeff_mul_X_pow', if_neg]
        intro h2
        have : ℓ * j0 < ℓ * j := Nat.mul_lt_mul_of_pos_left hgt hℓpos
        linarith
    · intro h; exact absurd (Finset.mem_range.mpr hj0) h
  exact hLft (key.trans hR)

end AnnihilatorQuotientResidues

end Formalism.WindowSums
end
end

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.Lagrange
section
noncomputable section

namespace Formalism.WindowSums

open Polynomial

private lemma aeval_prod_X_sub_C_eq_zero_of_subset {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
    (T : Module.End R V) {ι : Type} [DecidableEq ι] (A B : Finset ι) (γ : ι → R) (x : V)
    (hAB : A ⊆ B) (hA : aeval T (∏ k ∈ A, (X - C (γ k))) x = 0) :
    aeval T (∏ k ∈ B, (X - C (γ k))) x = 0 := by
  rw [← Finset.prod_sdiff hAB, map_mul, Module.End.mul_apply, hA, map_zero]

theorem lagrange_annihilation : Lagrange := by
  intro R _ _ V _ _ T ι _ I S γ d x hSI hinj hS hIS hdiv
  classical
  rcases I.eq_empty_or_nonempty with hI | hI
  · subst hI
    have hS0 : S = ∅ := Finset.subset_empty.mp hSI
    subst hS0
    simp at hS
    simp [hS]
  choose! c hc using hdiv

  have key : ∑ k ∈ I, C (c k) * ∏ m ∈ I.erase k, (X - C (γ m)) = C d := by
    rw [← sub_eq_zero]
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (I.image γ)
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      rw [eval_sub, eval_finsetSum, eval_C, sub_eq_zero]
      rw [Finset.sum_eq_single j]
      · rw [eval_mul, eval_C, eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        rw [hc j hj, mul_comm]
      · intro k hk hkj
        rw [eval_mul, eval_prod]
        apply mul_eq_zero_of_right
        apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨fun h => hkj h.symm, hj⟩)
        simp
      · intro hj'; exact absurd hj hj'
    · rw [Finset.card_image_of_injOn hinj]
      have hpos : 0 < I.card := Finset.card_pos.mpr hI
      have hdeg : ∀ k ∈ I, (C (c k) * ∏ m ∈ I.erase k, (X - C (γ m))).natDegree ≤ I.card - 1 := by
        intro k hk
        refine (natDegree_C_mul_le _ _).trans ?_
        refine (natDegree_prod_le _ _).trans ?_
        simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
        rw [Finset.card_erase_of_mem hk]
      refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
      rw [natDegree_C, max_lt_iff]
      refine ⟨lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ hdeg) (by omega), hpos⟩
  have h := congrArg (fun p => aeval T p x) key
  simp only [map_sum, aeval_C] at h
  rw [LinearMap.sum_apply] at h
  rw [Module.algebraMap_end_apply] at h
  rw [← h]
  apply Finset.sum_eq_zero
  intro k hk
  rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply]
  by_cases hkS : k ∈ S
  · have : I \ S ⊆ I.erase k := by
      intro m hm
      rw [Finset.mem_sdiff] at hm
      exact Finset.mem_erase.mpr ⟨fun h => hm.2 (h ▸ hkS), hm.1⟩
    rw [aeval_prod_X_sub_C_eq_zero_of_subset T _ _ γ x this hIS, smul_zero]
  · have : S ⊆ I.erase k := by
      intro m hm
      exact Finset.mem_erase.mpr ⟨fun h => hkS (h ▸ hm), hSI hm⟩
    rw [aeval_prod_X_sub_C_eq_zero_of_subset T _ _ γ x this hS, smul_zero]

end Formalism.WindowSums
end
end

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.ValProd
section
namespace Formalism.WindowSums

open Finset

section ValProdAux

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma vp_val_neg (x : ℤ_[ℓ]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · simp [hx]
  have h1 : (-1 : ℤ_[ℓ]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hm1 : (-1 : ℤ_[ℓ]).valuation = 0 := by
    have h := PadicInt.valuation_mul h1 h1
    rw [neg_one_mul, neg_neg, PadicInt.valuation_one] at h
    omega
  rw [← neg_one_mul x, PadicInt.valuation_mul h1 hx, hm1, zero_add]

lemma vp_val_prod {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ_[ℓ])
    (h : ∀ i ∈ S, f i ≠ 0) :
    (∏ i ∈ S, f i) ≠ 0 ∧ (∏ i ∈ S, f i).valuation = ∑ i ∈ S, (f i).valuation := by
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp [PadicInt.valuation_one]
  · intro a S ha ih h
    have hS : ∀ i ∈ S, f i ≠ 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha0 : f a ≠ 0 := h a (Finset.mem_insert_self a S)
    obtain ⟨h1, h2⟩ := ih hS
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨mul_ne_zero ha0 h1, by rw [PadicInt.valuation_mul ha0 h1, h2]⟩

private theorem prime_pow_ne_zero_and_valuation_eq (n : ℕ) :
    (ℓ : ℤ_[ℓ]) ^ n ≠ 0 ∧ ((ℓ : ℤ_[ℓ]) ^ n).valuation = n := by
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by
    intro h
    have h' := PadicInt.valuation_p (p := ℓ)
    rw [h, PadicInt.valuation_zero] at h'
    exact absurd h' (by norm_num)
  induction n with
  | zero => simp [PadicInt.valuation_one]
  | succ n ih =>
    refine ⟨pow_ne_zero _ hℓ0, ?_⟩
    rw [pow_succ, PadicInt.valuation_mul ih.1 hℓ0, ih.2, PadicInt.valuation_p]

lemma vp_sum_padicValNat (M : ℕ) :
    ∑ i ∈ Finset.Icc 1 M, padicValNat ℓ i = padicValNat ℓ M.factorial := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      padicValNat.mul (by omega : n + 1 ≠ 0) (Nat.factorial_ne_zero n)]
    omega

end ValProdAux

theorem valProd_of (hZ : ZpowVal) : ValProd := by
  unfold ValProd
  unfold ZpowVal at hZ
  intro ℓ hp u s hs h2 hv
  have key : ∀ j : ℤ, j ≠ 0 →
      (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
      (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j := by
    intro j hj
    obtain ⟨h1, h2'⟩ := hZ ℓ u s hs h2 hv j hj
    rw [← neg_sub, vp_val_neg, h2']
    exact ⟨neg_ne_zero.mpr h1, rfl⟩
  refine ⟨fun M => ?_, fun J hJ => ?_⟩
  · have hf : ∀ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i) ≠ 0 ∧
        (1 - (u : ℤ_[ℓ]) ^ i).valuation = s + padicValNat ℓ i := by
      intro i hi
      have hi0 : (i : ℤ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      have hk := key i hi0
      have e : ((u ^ (i : ℤ) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ i := by
        rw [zpow_natCast, Units.val_pow_eq_pow_val]
      have hv' : padicValInt ℓ (i : ℤ) = padicValNat ℓ i := by
        simp [padicValInt]
      rw [e, hv'] at hk
      exact hk
    obtain ⟨h1, h2'⟩ := vp_val_prod (Finset.Icc 1 M)
      (fun i => 1 - (u : ℤ_[ℓ]) ^ i) (fun i hi => (hf i hi).1)
    refine ⟨h1, h2'.trans ?_⟩
    rw [Finset.sum_congr rfl (fun i hi => (hf i hi).2), Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Icc, smul_eq_mul,
      vp_sum_padicValNat, Nat.add_sub_cancel]
  · have hf : ∀ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
        (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j := by
      intro j hj
      have hj0 : -j ≠ 0 := neg_ne_zero.mpr (fun h => hJ (by rw [← h]; exact hj))
      obtain ⟨h1, h2'⟩ := key (-j) hj0
      refine ⟨h1, h2'.trans ?_⟩
      simp [padicValInt]
    obtain ⟨h1, h2'⟩ := vp_val_prod J
      (fun j => 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun j hj => (hf j hj).1)
    refine ⟨h1, h2'.trans ?_⟩
    rw [Finset.sum_congr rfl (fun j hj => (hf j hj).2), Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul]

theorem killerVal_of (hZ : ZpowVal) : KillerVal := by
  unfold KillerVal
  unfold ZpowVal at hZ
  intro ℓ hp h2 c hc e JJ
  have h22 : ℓ = 2 → 2 ≤ 1 := fun h => absurd h h2
  have hf : ∀ i ∈ JJ.erase 0,
      (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
      (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = 1 + e + padicValInt ℓ i := by
    intro i hi
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have hp0 : ((ℓ : ℤ) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    have hj : i * (ℓ : ℤ) ^ e ≠ 0 := mul_ne_zero hi0 hp0
    obtain ⟨h1, h2'⟩ := hZ ℓ c 1 le_rfl h22 hc _ hj
    rw [← neg_sub, vp_val_neg, h2', padicValInt.mul hi0 hp0]
    refine ⟨neg_ne_zero.mpr h1, ?_⟩
    have hpe : padicValInt ℓ ((ℓ : ℤ) ^ e) = e := by
      simp [padicValInt, Int.natAbs_pow]
    omega
  obtain ⟨h1, h2'⟩ := vp_val_prod (JJ.erase 0)
    (fun i => 1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun i hi => (hf i hi).1)
  obtain ⟨hP1, hP2⟩ := prime_pow_ne_zero_and_valuation_eq (ℓ := ℓ) e
  have hev : (PP ℓ c e JJ).eval 1 =
      (∏ i ∈ JJ.erase 0, (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) * (ℓ : ℤ_[ℓ]) ^ e := by
    simp [PP, Polynomial.eval_prod, Polynomial.eval_finsetSum]
  rw [hev]
  refine ⟨mul_ne_zero h1 hP1, ?_⟩
  rw [PadicInt.valuation_mul h1 hP1, hP2, h2', Finset.sum_congr rfl (fun i hi => (hf i hi).2)]

end Formalism.WindowSums
end

