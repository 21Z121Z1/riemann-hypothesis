import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0001

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.AlgHomFixesSupportedPolynomials
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem det_mem_subalgebra_of_entries {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] (T : Subalgebra R P) {n : ℕ}
    (N : Matrix (Fin n) (Fin n) P) (h : ∀ i j, N i j ∈ T) : N.det ∈ T := by
  let M : Matrix (Fin n) (Fin n) T := Matrix.of fun i j => ⟨N i j, h i j⟩
  have hM : (T.val.toRingHom).mapMatrix M = N := by ext i j; rfl
  rw [← hM, ← RingHom.map_det]
  exact M.det.2

theorem divisor_supported_of_supported {R σ : Type*} [CommRing R] [IsDomain R] {s : Set σ} {f q : MvPolynomial σ R}
    (hf : f ≠ 0) (hs : f ∈ supported R s) (hq : q ∣ f) : q ∈ supported R s := by
  rw [mem_supported] at hs ⊢
  obtain ⟨g, rfl⟩ := hq
  have hq0 : q ≠ 0 := by rintro rfl; simp at hf
  have hg0 : g ≠ 0 := by rintro rfl; simp at hf
  intro v hv
  by_contra hvs
  have h1 : degreeOf v (q * g) = degreeOf v q + degreeOf v g := degreeOf_mul_eq hq0 hg0
  have h2 : degreeOf v (q * g) = 0 := by
    rw [degreeOf_eq_sup]
    refine Nat.le_zero.mp (Finset.sup_le fun m hm => ?_)
    by_contra hmv
    exact hvs (hs ((mem_vars v).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr (by omega)⟩))
  have h3 : degreeOf v q ≠ 0 := by
    obtain ⟨m, hm, hvm⟩ := (mem_vars v).mp hv
    have := monomial_le_degreeOf v hm
    have := Finsupp.mem_support_iff.mp hvm
    omega
  omega

theorem algHom_fixes_supported_polynomials {R σ : Type*} [CommRing R] {s : Set σ} (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (h : ∀ v ∈ s, φ (X v) = X v) {q : MvPolynomial σ R} (hq : q ∈ supported R s) : φ q = q := by
  rw [supported_eq_adjoin_X] at hq
  have hle : Algebra.adjoin R (X '' s) ≤ AlgHom.equalizer φ (AlgHom.id R _) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  exact hle hq

def cofactorMatrix (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  (matA R A).updateRow (lastIdx r) (Pi.single a 1)

def cofactorMatrixColumnCleared (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  Matrix.of fun i j => if i = lastIdx r then (if j = a then 1 else 0) else (if j = a then 0 else X (A i, j))

theorem adjugate_last_row_eq_cofactor_det (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (matA R A).adjugate a (lastIdx r) = (cofactorMatrix R A a).det := by
  rw [Matrix.adjugate_apply]; rfl

theorem cofactor_det_eq_cleared_det (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (cofactorMatrix R A a).det = (cofactorMatrixColumnCleared R A a).det := by
  symm
  classical
  refine Matrix.det_eq_of_forall_row_eq_smul_add_const
    (fun i => if i = lastIdx r then 0 else -X (A i, a)) (lastIdx r) (by simp) ?_
  intro i j
  by_cases hi : i = lastIdx r
  · subst hi
    simp [cofactorMatrix, cofactorMatrixColumnCleared, Matrix.updateRow_self, Pi.single_apply]
  · by_cases hj : j = a
    · subst hj
      simp [cofactorMatrix, cofactorMatrixColumnCleared, hi, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA]
    · simp [cofactorMatrix, cofactorMatrixColumnCleared, hi, hj, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA, Pi.single_apply]

def cofactorVariables {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) : Set (ι × Fin r) :=
  {v | (∃ i, i ≠ lastIdx r ∧ v.1 = A i) ∧ v.2 ≠ a}

theorem cofactor_last_row_supported (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (matA R A).adjugate a (lastIdx r) ∈ supported R (cofactorVariables A a) := by
  rw [adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]
  apply det_mem_subalgebra_of_entries
  intro i j
  simp only [cofactorMatrixColumnCleared, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _
  · exact Subalgebra.zero_mem _
  · rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨_, ⟨⟨i, h1, rfl⟩, h3⟩, rfl⟩

open Classical in

theorem adjugate_last_row_ne_zero (R : Type) [CommRing R] [Nontrivial R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι)
    (hA : Function.Injective A) (a : Fin r) : (matA R A).adjugate a (lastIdx r) ≠ 0 := by
  rw [adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]
  intro h0
  set σ : Equiv.Perm (Fin r) := Equiv.swap a (lastIdx r) with hσ
  let g : ι × Fin r → R := fun v => if ∃ i, v = (A i, σ i) then 1 else 0
  have hmap : (eval g).mapMatrix (cofactorMatrixColumnCleared R A a) = σ.permMatrix R := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, cofactorMatrixColumnCleared, Matrix.of_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq]
    by_cases hi : i = lastIdx r
    · subst hi
      by_cases hj : j = a
      · subst hj; simp [hσ, Equiv.swap_apply_right]
      · have : σ (lastIdx r) ≠ j := by rw [hσ, Equiv.swap_apply_right]; exact Ne.symm hj
        simp [hj, this]
    · have hσi : σ i ≠ a := by
        intro h
        apply hi
        have := congrArg σ h
        rwa [hσ, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have key : (∃ i', A i = A i' ∧ j = σ i') ↔ σ i = j := by
        constructor
        · rintro ⟨i', h1, h2⟩
          rw [hA h1]; exact h2.symm
        · intro h; exact ⟨i, rfl, h.symm⟩
      by_cases hj : j = a
      · subst hj; simp [hi, hσi]
      · simp [hi, hj, g, key]
  have hdet := congrArg (eval g) h0
  rw [RingHom.map_det, hmap, Matrix.det_permutation, map_zero] at hdet
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs] at hdet

open Classical in

def lastRowSubstitution (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    MvPolynomial (ι × Fin r) R →ₐ[R] MvPolynomial (ι × Fin r) R :=
  aeval fun v => if v.1 = A (lastIdx r) then (if v.2 = a then 1 else 0) else X v

theorem substitution_det_eq_adjugate (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι)
    (hA : Function.Injective A) (a : Fin r) :
    lastRowSubstitution R A a (detA (R := R) A) = (matA R A).adjugate a (lastIdx r) := by
  rw [adjugate_last_row_eq_cofactor_det]
  unfold detA
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, cofactorMatrix, lastRowSubstitution, aeval_X, matA]
  by_cases hi : i = lastIdx r
  · subst hi
    simp [Matrix.updateRow_self, Pi.single_apply]
  · have : A i ≠ A (lastIdx r) := hA.ne hi
    simp [this, Matrix.updateRow_ne hi, matA]

theorem hCop_proved : HCop := by
  intro R _ ι r _ A hA
  have hC := adjugate_last_row_ne_zero R A hA (lastIdx r)
  refine ⟨hC, ?_⟩
  intro d hd1 hd2
  have hd0 : d ≠ 0 := by rintro rfl; exact hC (zero_dvd_iff.mp hd2)
  have hsL : d ∈ supported R (cofactorVariables A (lastIdx r)) :=
    divisor_supported_of_supported hC (cofactor_last_row_supported R A _) hd2
  have hall : ∀ a, d ∈ supported R (cofactorVariables A a) := by
    intro a
    have hfix : lastRowSubstitution R A a d = d := by
      refine algHom_fixes_supported_polynomials _ ?_ hsL
      rintro v ⟨⟨i, hi, hv⟩, -⟩
      have : v.1 ≠ A (lastIdx r) := by rw [hv]; exact hA.ne hi
      simp [lastRowSubstitution, this]
    have hdv : d ∣ (matA R A).adjugate a (lastIdx r) := by
      rw [← substitution_det_eq_adjugate R A hA a, ← hfix]; exact map_dvd _ hd1
    exact divisor_supported_of_supported (adjugate_last_row_ne_zero R A hA a) (cofactor_last_row_supported R A a) hdv
  have hsub : (d.vars : Set (ι × Fin r)) ⊆ ∅ := by
    intro v hv
    exact ((mem_supported.mp (hall v.2)) hv).2 rfl
  have h0 : d ∈ supported R (∅ : Set (ι × Fin r)) := mem_supported.mpr hsub
  rw [supported_empty, Algebra.mem_bot] at h0
  obtain ⟨c, rfl⟩ := h0
  have hc : c ≠ 0 := by rintro rfl; exact hd0 (map_zero _)
  exact (IsUnit.mk0 c hc).map (algebraMap R _)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialExpansionCoeffZeroOfDeg
section
noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem coeff_binomial_power_divisibility (p P : ℕ) (hP : 0 < P) (h : ℤ[X]) (l : ℕ) : ∀ (f : ℤ[X]) (j : ℕ),
    (p : ℤ) ^ (l - j / P) ∣ (f * (X ^ P + C (p : ℤ) * h) ^ l).coeff j := by
  induction l with
  | zero => intro f j; simp
  | succ l ih =>
    intro f j
    have e : f * (X ^ P + C (p : ℤ) * h) ^ (l + 1) =
        X ^ P * (f * (X ^ P + C (p : ℤ) * h) ^ l) + C (p : ℤ) * ((f * h) * (X ^ P + C (p : ℤ) * h) ^ l) := by
      ring
    rw [e, coeff_add, coeff_X_pow_mul', coeff_C_mul]
    refine dvd_add ?_ ?_
    · split_ifs with hj
      · obtain ⟨q, rfl⟩ : ∃ q, j = q + P := ⟨j - P, by omega⟩
        rw [Nat.add_sub_cancel, Nat.add_div_right _ hP]
        exact dvd_trans (pow_dvd_pow _ (by omega)) (ih f q)
      · exact dvd_zero _
    · refine dvd_trans (pow_dvd_pow _ (show l + 1 - j / P ≤ l - j / P + 1 by omega)) ?_
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih (f * h) j)

def binomialExpansionCoeff (P rho M l : ℕ) : ℤ := (((1 + X) ^ rho * ((1 + X) ^ P - 1) ^ l : ℤ[X])).coeff M

theorem binomial_expansion_coeff_padic_dvd (p t : ℕ) (hp : p.Prime) (rho M l : ℕ) :
    (p : ℤ) ^ (l - M / p ^ t) ∣ binomialExpansionCoeff (p ^ t) rho M l := by
  have hP : 0 < p ^ t := pow_pos hp.pos t

  obtain ⟨h, hh⟩ : ∃ h : ℤ[X], (1 + X) ^ (p ^ t) - 1 = X ^ (p ^ t) + C (p : ℤ) * h := by
    have hd : C (p : ℤ) ∣ ((1 + X) ^ (p ^ t) - 1 - X ^ (p ^ t) : ℤ[X]) := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      simp only [coeff_sub, coeff_one_add_X_pow, coeff_one, coeff_X_pow]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [hP.ne']
        rw [if_neg (ne_of_lt hP)]
        exact dvd_zero _
      · by_cases hiP : i = p ^ t
        · subst hiP
          simp [hP.ne']
          rw [if_neg (by simp [hp.ne_zero])]
          exact dvd_zero _
        · by_cases hlt : i < p ^ t
          · have hdv := hp.dvd_choose_pow hi.ne' hiP
            simp only [if_neg hi.ne', if_neg hiP, sub_zero]
            exact_mod_cast hdv
          · rw [Nat.choose_eq_zero_of_lt (by omega)]
            simp [hi.ne', hiP]
    obtain ⟨h, hh⟩ := hd
    exact ⟨h, by rw [← hh]; ring⟩
  unfold binomialExpansionCoeff
  rw [hh]
  exact coeff_binomial_power_divisibility p (p ^ t) hP h l _ M

theorem binomial_expansion_coeff_zero_of_gt (P rho M l : ℕ) (h : M < l) : binomialExpansionCoeff P rho M l = 0 := by
  unfold binomialExpansionCoeff
  obtain ⟨q, hq⟩ : X ∣ ((1 + X) ^ P - 1 : ℤ[X]) := by
    rw [X_dvd_iff]
    simp [coeff_one_add_X_pow]
  rw [hq, mul_pow, show (1 + X : ℤ[X]) ^ rho * (X ^ l * q ^ l) = X ^ l * ((1 + X) ^ rho * q ^ l) by ring,
    coeff_X_pow_mul', if_neg (by omega)]

theorem binomial_expansion_coeff_zero_of_deg (P rho M l : ℕ) (h : rho + P * l < M) : binomialExpansionCoeff P rho M l = 0 := by
  unfold binomialExpansionCoeff
  apply coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt ?_ h
  have h1 : ((1 + X : ℤ[X])).natDegree ≤ 1 := (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
  have h2 : ((1 + X : ℤ[X]) ^ P - 1).natDegree ≤ P := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    exact natDegree_pow_le.trans ((Nat.mul_le_mul_left P h1).trans (by simp))
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · exact natDegree_pow_le.trans ((Nat.mul_le_mul_left rho h1).trans (by simp))
  · exact natDegree_pow_le.trans ((Nat.mul_le_mul_left l h2).trans (le_of_eq (mul_comm _ _)))

theorem choose_shift_binomial_expansion (P rho M e : ℕ) :
    (((rho + P * e).choose M : ℕ) : ℤ) = ∑ l ∈ range (M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by

  have hpoly : ((1 + X : ℤ[X])) ^ (rho + P * e) =
      ∑ l ∈ range (e + 1), C ((e.choose l : ℕ) : ℤ) * ((1 + X) ^ rho * ((1 + X) ^ P - 1) ^ l) := by
    rw [pow_add, pow_mul, show ((1 + X : ℤ[X]) ^ P) = ((1 + X) ^ P - 1) + 1 by ring,
      add_pow ((1 + X : ℤ[X]) ^ P - 1) 1 e, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [one_pow, mul_one, C_eq_natCast, add_sub_cancel_right]
    ring
  have hc := congrArg (fun q : ℤ[X] => q.coeff M) hpoly
  simp only [coeff_one_add_X_pow, finset_sum_coeff, coeff_C_mul] at hc
  rw [hc]
  calc ∑ l ∈ range (e + 1), ((e.choose l : ℕ) : ℤ) * ((1 + X : ℤ[X]) ^ rho * ((1 + X) ^ P - 1) ^ l).coeff M
      = ∑ l ∈ range (e + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) :=
        Finset.sum_congr rfl (fun l _ => by rw [mul_comm]; rfl)
    _ = ∑ l ∈ range (e + M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)
        simp only [Finset.mem_range] at hl hn
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    _ = ∑ l ∈ range (M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by
        refine (Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)).symm
        simp only [Finset.mem_range] at hl hn
        rw [binomial_expansion_coeff_zero_of_gt P rho M l (by omega)]
        simp

theorem derivative_digit_expansion (D : Formalism.BasicNotions.D7) : DerivativeDigitExpansion D := by
  intro p hp _ t σ _ rho M _ c
  classical
  have hP : 0 < p ^ t := pow_pos hp.pos t
  let a : σ → ℕ → ℤ := fun k l => binomialExpansionCoeff (p ^ t) (rho k) (M k) l

  let good : (σ → ℕ) → Prop := fun l => (∀ k, M k ≤ rho k + p ^ t * l k) ∧ ∑ k, (l k - M k / p ^ t) < c
  let B : Finset (σ → ℕ) := Fintype.piFinset (fun k => range (M k + 1))
  refine ⟨B.filter good, fun l => ∏ k, a k (l k), ?_, ?_, ?_⟩
  · intro l hl
    have hl' := (Finset.mem_filter.1 hl).2.2
    have h1 : ∑ k, l k ≤ ∑ k, (l k - M k / p ^ t) + ∑ k, M k / p ^ t := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun k _ => le_tsub_add)
    have h2 : (∑ k, M k / p ^ t) ≤ (∑ k, M k) / p ^ t := by
      rw [Nat.le_div_iff_mul_le hP, Finset.sum_mul]
      exact Finset.sum_le_sum (fun k _ => Nat.div_mul_le_self _ _)
    have h3 : ((((∑ k, M k) / p ^ t : ℕ)) : ℝ) ≤ ((∑ k, M k : ℕ) : ℝ) / ((p ^ t : ℕ) : ℝ) := Nat.cast_div_le
    have h4 : ∑ k, l k ≤ c + (∑ k, M k) / p ^ t := by omega
    have h5 : ((∑ k, l k : ℕ) : ℝ) ≤ (c : ℝ) + ((((∑ k, M k) / p ^ t : ℕ)) : ℝ) := by exact_mod_cast h4
    linarith
  · intro l hl k
    exact (Finset.mem_filter.1 hl).2.1 k
  · intro e'
    have hexp : ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) =
        ∑ l ∈ B, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)) := by
      calc ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ)
          = ∏ k, ∑ j ∈ range (M k + 1), a k j * (((e' k).choose j : ℕ) : ℤ) :=
            Finset.prod_congr rfl (fun k _ => choose_shift_binomial_expansion (p ^ t) (rho k) (M k) (e' k))
        _ = _ := Finset.prod_univ_sum _ _
    have hT : ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ) =
        ∑ l ∈ B.filter good, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)) :=
      Finset.sum_congr rfl (fun l _ => Finset.prod_mul_distrib.symm)
    have hsplit := Finset.sum_filter_add_sum_filter_not B good
      (fun l => ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)))
    show (p : ℤ) ^ c ∣ ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) -
      ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ)
    rw [hexp, hT, ← hsplit, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro l hl
    have hng := (Finset.mem_filter.1 hl).2
    rw [Finset.prod_mul_distrib]
    apply Dvd.dvd.mul_right
    by_cases hdeg : ∀ k, M k ≤ rho k + p ^ t * l k
    · have hc : c ≤ ∑ k, (l k - M k / p ^ t) := by
        by_contra hh
        exact hng ⟨hdeg, by omega⟩
      refine dvd_trans (pow_dvd_pow _ hc) ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun k _ => binomial_expansion_coeff_padic_dvd p t hp (rho k) (M k) (l k))
    · push_neg at hdeg
      obtain ⟨k, hk⟩ := hdeg
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (binomial_expansion_coeff_zero_of_deg (p ^ t) (rho k) (M k) (l k) hk)]
      exact dvd_zero _

theorem unit_product_eq_choose (P n rho : ℕ) : dUnit P n rho = (((rho + P * n).choose rho : ℕ) : ℚ) := by
  induction rho with
  | zero => simp [dUnit]
  | succ r ih =>
    show (∏ y ∈ Finset.Icc 1 (r + 1), (1 + (P : ℚ) * n / y)) = _
    rw [Finset.prod_Icc_succ_top (by omega)]
    have ih' : (∏ y ∈ Finset.Icc 1 r, (1 + (P : ℚ) * n / y)) = (((r + P * n).choose r : ℕ) : ℚ) := ih
    rw [ih', show r + 1 + P * n = r + P * n + 1 by ring]

    have hc : (((r + P * n + 1 : ℕ) : ℚ)) * (((r + P * n).choose r : ℕ) : ℚ) =
        (((r + P * n + 1).choose (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (r + P * n) r
    have hr : ((r : ℚ) + 1) ≠ 0 := by positivity
    push_cast at hc ⊢
    field_simp
    linear_combination hc

theorem hdU_proved {p : ℕ} (hp : p.Prime) : HdU p := by
  intro t rho hrho
  refine ⟨fun l => binomialExpansionCoeff (p ^ (t + 1)) rho rho l, fun n => ?_, fun l => ?_⟩
  · rw [unit_product_eq_choose]
    exact_mod_cast choose_shift_binomial_expansion (p ^ (t + 1)) rho rho n
  · have h := binomial_expansion_coeff_padic_dvd p (t + 1) hp rho rho l
    rw [Nat.div_eq_of_lt hrho, Nat.sub_zero] at h
    exact h

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def restrictStableOperators {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (W : Submodule K V)
    (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) : GLOps n K W := fun a b => (E a b).restrict (h a b)

def CompleteReducibilityIsotypic : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def ContravariantIsotypicOrthogonal : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ B : V →ₗ[K] V →ₗ[K] K, (∀ a b x y, B (E a b x) y = B x (E b a y)) →
      ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0

def HighestWeightDominant : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ lam v, IsHWV E lam v → Dominant lam

def SubrepRestrictionRep : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W),
      IsGLRep (restrictStableOperators E W h) ∧
      (∀ (mu : Fin n → ℤ) (x : W), x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu) ∧
      (∀ a b k (x : W), ((divPowE (restrictStableOperators E W h) a b k x : W) : V) = divPowE E a b k x) ∧
      (∀ a k (x : W), ((binomE (restrictStableOperators E W h) a k x : W) : V) = binomE E a k x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e →
        ∃ e' : Module.End K W, IsIsoProj (restrictStableOperators E W h) lam e' ∧ ∀ x : W, ((e' x : W) : V) = e x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e → (¬ ∃ v : W, IsHWV (restrictStableOperators E W h) lam v) →
        ∀ x ∈ W, e x = 0)

def PolynomialGLRepresentation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (LL : Letters ι),
    (∀ S, IsGLRep (glOps K n LL S)) ∧
    (∀ S S' : Set ι, Disjoint S S' → ∀ a b c d,
      glOps K n LL S a b * glOps K n LL S' c d = glOps K n LL S' c d * glOps K n LL S a b) ∧
    (∀ S S' : Set ι, S ⊆ S' → ∀ a b, glOps K n LL S' a b = glOps K n LL S a b + glOps K n LL (S' \ S) a b) ∧
    (∀ S d a b, ∀ F ∈ Pol K n d, glOps K n LL S a b F ∈ Pol K n d) ∧
    (∀ d : ι → ℕ, FiniteDimensional K (Pol K n d)) ∧
    (∀ S mu F, F ∈ weightSp (glOps K n LL S) mu → ∀ m ∈ F.support, wtS LL S m = mu) ∧
    (∃ B : MvPolynomial (ι × Fin n) K →ₗ[K] MvPolynomial (ι × Fin n) K →ₗ[K] K,
      (∀ F G, B F G = fock F G) ∧ ∀ S a b F G, B (glOps K n LL S a b F) G = B F (glOps K n LL S b a G))

def latticeMultidegreePart {O : Type} [CommRing O] [IsDomain O] {ι : Type} {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ) : Submodule O (Pol (KK O) n d) :=
  L.comap (((Pol (KK O) n d).subtype).restrictScalars O)

def AdmissibleDVRIntegralFormLatticesStable : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O → CharZero (KK O) ∧
    ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι),
      (∀ S : Set ι, PolUZStable LL S (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S),
        (∀ F ∈ IntPol O (ι × Fin n), u F ∈ IntPol O (ι × Fin n)) ∧
        ∀ F : MvPolynomial (ι × Fin n) (KK O), InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      ∃ BBs : Submodule O (MvPolynomial (ι × Fin n) (KK O)), (∀ F, F ∈ BBs ↔ InBB (O := O) p F) ∧
        ∀ d : ι → ℕ, (latticeMultidegreePart (IntPol O (ι × Fin n)) d).FG ∧ MQ (K := KK O) (latticeMultidegreePart (IntPol O (ι × Fin n)) d) = ⊤ ∧
          (latticeMultidegreePart BBs d).FG ∧ MQ (K := KK O) (latticeMultidegreePart BBs d) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorLinftyBound
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def linf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (W : Submodule K V) : ℕ :=
  sSup {k | ∃ nu ∈ wtsOf E W, (∑ a, nu a = 0) ∧ ∃ a, k = (nu a).natAbs}

def InvariantDenominatorLinftyBound : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        ∀ x ∈ M, ((p : O) ^ (N0 n * deF p n (linf E (MQ M)))) • Inv x ∈ M

def InvariantProjectionDenominator : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        ∀ x ∈ M, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • Inv x ∈ M

end Formalism.MainNotions.G.GLWeightTheory
end
end

