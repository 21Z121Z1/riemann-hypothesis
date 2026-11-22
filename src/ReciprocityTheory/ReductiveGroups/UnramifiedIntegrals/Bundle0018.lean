import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0017
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.G2EqZeroOfHasCMByThree
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_three_sq : omegaK 3 ^ 2 = omegaK 3 - 1 := by
  have h : (((Real.sqrt (3 : ℕ) : ℝ) : ℂ)) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  unfold omegaK
  linear_combination (Complex.I ^ 2 / 4) * h + (3 / 4 : ℂ) * Complex.I_sq

def mulOmegaEquiv (L : PeriodPair) (hCM : HasCMBy 3 L) : L.lattice ≃ L.lattice where
  toFun l := ⟨omegaK 3 * l, hCM l l.2⟩
  invFun l := ⟨(l : ℂ) - omegaK 3 * l, L.lattice.sub_mem l.2 (hCM l l.2)⟩
  left_inv l := by
    apply Subtype.ext
    show omegaK 3 * (l : ℂ) - omegaK 3 * (omegaK 3 * l) = l
    linear_combination (-(l : ℂ)) * omegaK_three_sq
  right_inv l := by
    apply Subtype.ext
    show omegaK 3 * ((l : ℂ) - omegaK 3 * l) = l
    linear_combination (-(l : ℂ)) * omegaK_three_sq

theorem g2_eq_zero_of_hasCMBy_three (L : PeriodPair) (hCM : HasCMBy 3 L) : L.g₂ = 0 := by
  have hsq := omegaK_three_sq
  have h4 : omegaK 3 ^ 4 = -omegaK 3 := by
    linear_combination (omegaK 3 ^ 2 + omegaK 3) * hsq
  have h0 : omegaK 3 ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have h1 : omegaK 3 ≠ -1 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have key : L.G 4 = (omegaK 3 ^ 4)⁻¹ * L.G 4 := by
    conv_lhs => rw [PeriodPair.G, ← (mulOmegaEquiv L hCM).tsum_eq]
    rw [PeriodPair.G, ← tsum_mul_left]
    refine tsum_congr fun l => ?_
    show ((omegaK 3 * (l : ℂ)) ^ 4)⁻¹ = _
    rw [mul_pow, mul_inv]
  have hG : L.G 4 = 0 := by
    have h40 : omegaK 3 ^ 4 ≠ 0 := pow_ne_zero _ h0
    have h2 : omegaK 3 ^ 4 * L.G 4 = L.G 4 := by
      conv_lhs => rw [key]
      rw [mul_inv_cancel_left₀ h40]
    rw [h4] at h2
    have h3 : (omegaK 3 + 1) * L.G 4 = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (by linear_combination h) h1
    · exact h
  rw [PeriodPair.g₂, hG, mul_zero]

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedGcd
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem rootPoly_monic' {E : Type} [Field E] (xs : Finset E) : (rootPoly xs).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

theorem rootPoly_inter_mul_sdiff {E : Type} [Field E] (xs ys : Finset E) :
    rootPoly (xs ∩ ys) * rootPoly (xs \ ys) = rootPoly xs := by
  unfold rootPoly
  rw [← Finset.prod_union (Finset.disjoint_sdiff_inter xs ys).symm, Finset.union_comm,
    Finset.sdiff_union_inter]

theorem rootPoly_isCoprime_of_disjoint {E : Type} [Field E] (xs ys : Finset E) (h : Disjoint xs ys) :
    IsCoprime (rootPoly xs) (rootPoly ys) := by
  unfold rootPoly
  refine IsCoprime.prod_left fun x hx => IsCoprime.prod_right fun y hy => ?_
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  have hne : x ≠ y := fun e => Finset.disjoint_left.1 h hx (e ▸ hy)
  exact (sub_ne_zero.2 hne).isUnit

theorem exists_poly_map_subfield {E : Type} [Field E] [DecidableEq E] (k : Subfield E) (P : E[X])
    (h : ∀ i, P.coeff i ∈ k) : ∃ p : (k)[X], p.map k.subtype = P := by
  have : P ∈ Polynomial.lifts k.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  exact this

theorem rootPoly_inter_mem {E : Type} [Field E] (k : Subfield E) (xs ys : Finset E)
    (hx : ∀ i, (rootPoly xs).coeff i ∈ k) (hy : ∀ i, (rootPoly ys).coeff i ∈ k) :
    ∀ i, (rootPoly (xs ∩ ys)).coeff i ∈ k := by
  obtain ⟨p, hp⟩ := exists_poly_map_subfield k _ hx
  obtain ⟨q, hq⟩ := exists_poly_map_subfield k _ hy
  set R := rootPoly (xs ∩ ys) with hR
  set g0 := EuclideanDomain.gcd p q with hg0
  set g := g0.map k.subtype with hg
  have hgP : g ∣ rootPoly xs := by
    rw [← hp]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_left p q)
  have hgQ : g ∣ rootPoly ys := by
    rw [← hq]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_right p q)
  have hA := rootPoly_inter_mul_sdiff xs ys
  have hB := rootPoly_inter_mul_sdiff ys xs
  rw [Finset.inter_comm ys xs] at hB
  have hdisj : Disjoint (xs \ ys) (ys \ xs) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1
  obtain ⟨u, v, huv⟩ := rootPoly_isCoprime_of_disjoint _ _ hdisj
  have hgR : g ∣ R := by
    have : R = u * rootPoly xs + v * rootPoly ys := by
      rw [← hA, ← hB]
      linear_combination (-R) * huv
    rw [this]
    exact dvd_add (hgP.mul_left _) (hgQ.mul_left _)
  have hRg : R ∣ g := by
    have e : g = EuclideanDomain.gcd (rootPoly xs) (rootPoly ys) := by
      rw [← hp, ← hq, Polynomial.gcd_map]
    rw [e]
    exact EuclideanDomain.dvd_gcd ⟨_, hA.symm⟩ ⟨_, hB.symm⟩
  have hRm : R.Monic := rootPoly_monic' _
  have hg0' : g ≠ 0 := fun e => hRm.ne_zero (by simpa [e] using hgR)
  have hg00 : g0 ≠ 0 := fun e => hg0' (by rw [hg, e, Polynomial.map_zero])
  have hmon : (g0 * C g0.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hg00
  have hmon' : ((g0 * C g0.leadingCoeff⁻¹).map k.subtype).Monic := hmon.map _
  have hassoc : Associated ((g0 * C g0.leadingCoeff⁻¹).map k.subtype) R := by
    have h1 : Associated g R := associated_of_dvd_dvd hgR hRg
    refine Associated.trans ?_ h1
    rw [Polynomial.map_mul, Polynomial.map_C]
    refine (associated_mul_unit_left g _ ?_).symm.symm
    refine Polynomial.isUnit_C.2 (IsUnit.mk0 _ ?_)
    simpa using hg00
  have heq := eq_of_monic_of_associated hmon' hRm hassoc
  intro i
  rw [← heq, Polynomial.coeff_map]
  exact (((g0 * C g0.leadingCoeff⁻¹).coeff i)).2

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedHalf
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}

theorem IsHalfReps.notMem (h : IsHalfReps L α T) {P : ℂ} (hP : P ∈ T) : P ∉ L.lattice := by
  intro hPL
  apply (h.1 P hP).2
  rw [two_mul]
  exact add_mem hPL hPL

theorem IsHalfReps.kerReps (h : IsHalfReps L α T) :
    IsKerReps L α (T ∪ T.image (fun P => -P)) ∧ Disjoint T (T.image (fun P => -P)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact ⟨(h.1 P hP).1, h.notMem hP⟩
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      refine ⟨?_, ?_⟩
      · rw [mul_neg]; exact neg_mem (h.1 Q hQ).1
      · intro hn; exact h.notMem hQ (by simpa using neg_mem hn)
  · intro P hP Q hQ hPQ
    rcases Finset.mem_union.mp hP with hP | hP <;> rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact h.2.1 P hP Q hQ (Or.inl hPQ)
    · obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have e : P = Q' := h.2.1 P hP Q' hQ' (Or.inr (by simpa using hPQ))
      subst e
      exact absurd (by rw [two_mul]; simpa using hPQ) (h.1 P hP).2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      have h1 : P' + Q ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - Q) = P' + Q := by ring
        rwa [e] at this
      have e : P' = Q := h.2.1 P' hP' Q hQ (Or.inr h1)
      subst e
      exact absurd (by rw [two_mul]; exact h1) (h.1 P' hP').2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have h1 : P' - Q' ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - -Q') = P' - Q' := by ring
        rwa [e] at this
      rw [h.2.1 P' hP' Q' hQ' (Or.inl h1)]
  · intro z hz hzL
    obtain ⟨P, hP, hzP | hzP⟩ := h.2.2 z hz hzL
    · exact ⟨P, Finset.mem_union_left _ hP, hzP⟩
    · exact ⟨-P, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hP), by simpa using hzP⟩
  · rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP'
    have h0 : P + Q ∈ L.lattice := by rw [← hQP]; simp
    have e : P = Q := h.2.1 P hP Q hQ (Or.inr h0)
    subst e
    exact (h.1 P hP).2 (by rw [two_mul]; exact h0)

theorem IsHalfReps.card (h : IsHalfReps L α T) (hα : α ≠ 0) (hs : MulStable L α) :
    2 * (T.card : ℝ) + 1 = Complex.normSq α := by
  have h1 := kerRepsCard L α _ hα hs h.kerReps.1
  rw [Finset.card_union_of_disjoint h.kerReps.2, Finset.card_image_of_injective _ neg_injective] at h1
  rw [← h1]; push_cast; ring

theorem IsHalfReps.injOn (h : IsHalfReps L α T) : Set.InjOn L.weierstrassP (T : Set ℂ) := by
  intro P hP Q hQ hPQ
  exact h.2.1 P hP Q hQ ((pInjective L P Q (h.notMem hP) (h.notMem hQ)).mp hPQ)

theorem IsHalfReps.card_xsOf (h : IsHalfReps L α T) : (xsOf L T).card = T.card :=
  Finset.card_image_of_injOn h.injOn

theorem IsHalfReps.fW_ne (h : IsHalfReps L α T) {x : ℂ} (hx : x ∈ xsOf L T) : fW L.g₂ L.g₃ x ≠ 0 := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
  have hPL := h.notMem hP
  unfold fW
  rw [← L.derivWeierstrassP_sq P hPL]
  exact pow_ne_zero 2 (fun h0 => (h.1 P hP).2 ((pDerivZero L P hPL).mp h0))

theorem IsHalfReps.mem_xsOf (h : IsHalfReps L α T) (hs : MulStable L α) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassP z ∈ xsOf L T ↔ α * z ∈ L.lattice := by
  constructor
  · intro hx
    obtain ⟨P, hP, hPz⟩ := Finset.mem_image.mp hx
    rcases (pInjective L z P hz (h.notMem hP)).mp hPz.symm with h1 | h1
    · have e : α * z = α * (z - P) + α * P := by ring
      rw [e]; exact add_mem (hs _ h1) (h.1 P hP).1
    · have e : α * z = α * (z + P) - α * P := by ring
      rw [e]; exact sub_mem (hs _ h1) (h.1 P hP).1
  · intro hk
    obtain ⟨P, hP, h1⟩ := h.2.2 z hk hz
    exact Finset.mem_image.mpr ⟨P, hP, ((pInjective L z P hz (h.notMem hP)).mpr h1).symm⟩

theorem ker_norm (hs : MulStable L α) {N : ℕ} (hN : Complex.normSq α = N) {z : ℂ}
    (hz : α * z ∈ L.lattice) : (N : ℂ) * z ∈ L.lattice := by
  obtain ⟨t, n, ht, -, -⟩ := mulStableIntegral L α hs
  have h1 : (N : ℂ) = α * (starRingEnd ℂ) α := by
    rw [Complex.mul_conj, hN]; simp
  have e : (N : ℂ) * z = t • (α * z) - α * (α * z) := by
    rw [h1, zsmul_eq_mul, ← ht]; ring
  rw [e]
  exact sub_mem (zsmul_mem hz t) (hs _ hz)

theorem halfReps_exist (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (hs : MulStable L α) (N : ℕ)
    (hN : Complex.normSq α = N) (hodd : Odd N) : ∃ T : Finset ℂ, IsHalfReps L α T := by
  obtain ⟨S, hS⟩ := kerRepsExist L α hα hs
  let g : ℂ → ℂ := fun x => Classical.epsilon (fun Q => Q ∈ S ∧ L.weierstrassP Q = x)
  have hg : ∀ P ∈ S, g (L.weierstrassP P) ∈ S ∧ L.weierstrassP (g (L.weierstrassP P)) = L.weierstrassP P :=
    fun P hP => Classical.epsilon_spec (p := fun Q => Q ∈ S ∧ L.weierstrassP Q = L.weierstrassP P) ⟨P, hP, rfl⟩
  refine ⟨(S.image L.weierstrassP).image g, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    have hk := hS.1 _ (hg P0 hP0).1
    refine ⟨hk.1, fun h2 => hk.2 ?_⟩
    obtain ⟨k, hk'⟩ := hodd
    have h3 := ker_norm hs hN hk.1
    have e : g (L.weierstrassP P0) = (N : ℂ) * g (L.weierstrassP P0) - (k : ℤ) • (2 * g (L.weierstrassP P0)) := by
      rw [hk', zsmul_eq_mul]; push_cast; ring
    rw [e]
    exact sub_mem h3 (zsmul_mem h2 _)
  · intro P hP Q hQ hPQ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨Q0, hQ0, rfl⟩ := Finset.mem_image.mp hy
    have h1 := (pInjective L _ _ (hS.1 _ (hg P0 hP0).1).2 (hS.1 _ (hg Q0 hQ0).1).2).mpr hPQ
    rw [(hg P0 hP0).2, (hg Q0 hQ0).2] at h1
    rw [h1]
  · intro z hz hzL
    obtain ⟨P0, hP0, h0⟩ := hS.2.2 z hz hzL
    refine ⟨g (L.weierstrassP P0),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hP0), ?_⟩
    apply (pInjective L _ _ hzL (hS.1 _ (hg P0 hP0).1).2).mp
    rw [(hg P0 hP0).2]
    exact (pInjective L _ _ hzL (hS.1 _ hP0).2).mpr (Or.inl h0)

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedProjA
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] (U : PowerSeries K)

theorem homS_add (m : ℕ) (P Q : K[X]) : homS U m (P + Q) = homS U m P + homS U m Q := by
  simp only [homS, coeff_add, map_add, add_mul, Finset.sum_add_distrib]

theorem homS_sub (m : ℕ) (P Q : K[X]) : homS U m (P - Q) = homS U m P - homS U m Q := by
  simp only [homS, coeff_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem homS_zero (m : ℕ) : homS U m (0 : K[X]) = 0 := by
  simp [homS]

theorem homS_sum {ι : Type} (s : Finset ι) (m : ℕ) (f : ι → K[X]) :
    homS U m (∑ i ∈ s, f i) = ∑ i ∈ s, homS U m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [homS_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homS_add, ih]

theorem homS_monomial (m i : ℕ) (hi : i ≤ m) (a : K) :
    homS U m (monomial i a) = PowerSeries.C a * U ^ i * PowerSeries.X ^ (2 * (m - i)) := by
  unfold homS
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [coeff_monomial, if_neg (Ne.symm hb)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem homS_mul (m n : ℕ) (P Q : K[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    homS U (m + n) (P * Q) = homS U m P * homS U n Q := by
  have eP : P = ∑ i ∈ Finset.range (m + 1), monomial i (P.coeff i) :=
    P.as_sum_range' (m + 1) (Nat.lt_succ_of_le hP)
  have eQ : Q = ∑ j ∈ Finset.range (n + 1), monomial j (Q.coeff j) :=
    Q.as_sum_range' (n + 1) (Nat.lt_succ_of_le hQ)
  have e : P * Q = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      monomial (i + j) (P.coeff i * Q.coeff j) := by
    conv_lhs => rw [eP, eQ]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [e, homS_sum]
  simp only [homS_sum]
  unfold homS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have := homS_monomial U (m + n) (i + j) (by omega) (P.coeff i * Q.coeff j)
  unfold homS at this
  rw [this]
  have h2 : 2 * (m + n - (i + j)) = 2 * (m - i) + 2 * (n - j) := by omega
  rw [h2, pow_add, pow_add, map_mul]
  ring

theorem homS_eq_zero (hU : PowerSeries.constantCoeff U = 1) (m : ℕ) (P : K[X]) (hP : P.natDegree ≤ m)
    (h : homS U m P = 0) : P = 0 := by
  have h1 : PowerSeries.coeff (2 * (m - P.natDegree)) (homS U m P) = P.leadingCoeff := by
    unfold homS
    rw [map_sum, Finset.sum_eq_single P.natDegree]
    · rw [PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_mul, map_pow, hU]
      simp
    · intro b hb hne
      have hb' : b ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp
    · intro hh
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hP)) hh
  rw [h, map_zero] at h1
  exact leadingCoeff_eq_zero.1 h1.symm

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedSqrt
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem sqrt_poly {E : Type} [Field E] [CharZero E] (k : Subfield E) (h : E[X]) (hm : h.Monic)
    (hk : ∀ i, (h ^ 2).coeff i ∈ k) : ∀ i, h.coeff i ∈ k := by
  have key : ∀ m i : ℕ, h.natDegree ≤ i + m → h.coeff i ∈ k := by
    intro m
    induction m with
    | zero =>
      intro i hi
      rcases Nat.eq_or_lt_of_le (by simpa using hi : h.natDegree ≤ i) with h1 | h1
      · rw [← h1, hm.coeff_natDegree]; exact k.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt h1]; exact k.zero_mem
    | succ m ih =>
      intro i hi
      by_cases h0 : h.natDegree ≤ i + m
      · exact ih i h0
      have hin : i < h.natDegree := by omega
      set n := h.natDegree with hn
      have hmem : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (i + n),
          h.coeff x.1 * h.coeff x.2 - (if x = (i, n) then h.coeff i else 0)
            - (if x = (n, i) then h.coeff i else 0) ∈ k := by
        rintro ⟨a, b⟩ hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        simp only at hx
        by_cases ha : a = i
        · have hb : b = n := by omega
          subst ha; subst hb
          have hne : ¬ ((a, h.natDegree) = (h.natDegree, a)) := by
            intro he
            have := (Prod.mk.injEq _ _ _ _ ▸ he : a = h.natDegree ∧ h.natDegree = a).1
            omega
          rw [if_pos rfl, if_neg hne, hm.coeff_natDegree]
          simp [k.zero_mem]
        by_cases ha' : a = n
        · have hb : b = i := by omega
          subst hb
          rw [ha']
          have hne : ¬ ((n, b) = (b, n)) := by
            intro he
            have := (Prod.mk.injEq _ _ _ _ ▸ he : n = b ∧ b = n).1
            omega
          rw [if_neg hne, if_pos rfl, hn, hm.coeff_natDegree]
          simp [k.zero_mem]
        have hne1 : ¬ ((a, b) = (i, n)) := fun he => ha (congrArg Prod.fst he)
        have hne2 : ¬ ((a, b) = (n, i)) := fun he => ha' (congrArg Prod.fst he)
        rw [if_neg hne1, if_neg hne2, sub_zero, sub_zero]
        rcases lt_or_gt_of_ne ha with h1 | h1
        · have : n < b := by omega
          show h.coeff a * h.coeff b ∈ k
          rw [coeff_eq_zero_of_natDegree_lt this, mul_zero]; exact k.zero_mem
        · rcases lt_or_gt_of_ne ha' with h2 | h2
          · exact k.mul_mem (ih a (by omega)) (ih b (by omega))
          · show h.coeff a * h.coeff b ∈ k
            rw [coeff_eq_zero_of_natDegree_lt h2, zero_mul]; exact k.zero_mem
      have hsum := k.sum_mem hmem
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← coeff_mul, ← pow_two,
        Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (by simp),
        if_pos (by simp [add_comm])] at hsum
      have h2 : (2 : E) * h.coeff i ∈ k := by
        have := k.sub_mem (hk (i + n)) hsum
        have e : (h ^ 2).coeff (i + n) - ((h ^ 2).coeff (i + n) - h.coeff i - h.coeff i)
            = 2 * h.coeff i := by ring
        rwa [e] at this
      have h2k : (2 : E) ∈ k := by
        have := k.add_mem k.one_mem k.one_mem
        rwa [one_add_one_eq_two] at this
      have := k.mul_mem (k.inv_mem h2k) h2
      rwa [← mul_assoc, inv_mul_cancel₀ (two_ne_zero), one_mul] at this
  intro i
  exact key h.natDegree i (by omega)

end ReciprocityTheory.ChartRestriction.L1
end
end

