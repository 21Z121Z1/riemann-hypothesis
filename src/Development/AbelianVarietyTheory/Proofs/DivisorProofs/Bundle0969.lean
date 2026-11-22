import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import ReciprocityTheory.SemistableReduction.Bundle0001
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0004
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtD
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInducedTypeCharEqProductList
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerLeftCommutesEmbedding
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair.Down

variable {P Q R : ℕ}

theorem pderiv_pderiv_comm {σ : Type} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  have h0 : ⁅(pderiv i : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)),
      (pderiv j : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have := congrArg (fun D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) => D f) h0
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem pderiv_s_mR (a' a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inl a', Sum.inl c) (mR P Q R a b) =
      if a' = a then X (Sum.inr b, Sum.inl c) else 0 := by
  classical
  simp [mR, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  rcases eq_or_ne a' a with rfl | ha
  · simp
  · simp [ha, Ne.symm ha]

theorem pderiv_w_mR (b' : Fin Q) (a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b', Sum.inl c) (mR P Q R a b) =
      if b' = b then X (Sum.inl a, Sum.inl c) else 0 := by
  classical
  simp [mR, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  rcases eq_or_ne b' b with rfl | hb
  · simp
  · simp [hb, Ne.symm hb]

theorem embR_eq (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    embR P Q R h k G = aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G * detR P Q R h ^ k := by
  simp [embR]

theorem derivation_det_eq_zero {σ : Type} {n : ℕ} (d : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hM : ∀ i j, d (M i j) = 0) : d M.det = 0 := by
  have e : M.det = aeval (fun ij : Fin n × Fin n => M ij.1 ij.2)
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)) := by
    rw [← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext i j; simp [Matrix.mvPolynomialX]
  rw [e, ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq]
  simp [hM]

def blockR (h : P ≤ R) : Matrix (Fin P) (Fin P) (Pol P Q R 0) :=
  Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)

theorem detR_eq (h : P ≤ R) : detR P Q R h = (blockR (Q := Q) h).det := rfl

theorem pderiv_w_detR (h : P ≤ R) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h) = 0 := by
  classical
  rw [detR_eq]
  apply derivation_det_eq_zero
  intro i j
  simp [blockR, pderiv_X, Pi.single_apply]

theorem pderiv_s_detR (h : P ≤ R) (a : Fin P) (c : Fin R) :
    pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      ∑ j : Fin P, if Fin.castLE h j = c then (blockR (Q := Q) h).adjugate j a else 0 := by
  classical
  rw [detR_eq, Matrix.det_eq_sum_mul_adjugate_row _ a, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hadj : pderiv (Sum.inl a, Sum.inl c) ((blockR (Q := Q) h).adjugate j a) = 0 := by
    rw [Matrix.adjugate_apply]
    apply derivation_det_eq_zero
    intro i j'
    rw [Matrix.updateRow_apply]
    split_ifs with hi
    · simp [Pi.single_apply]; split_ifs <;> simp
    · simp [blockR, pderiv_X, Pi.single_apply, hi]
  rw [Derivation.leibniz, hadj]
  simp [blockR, pderiv_X, Pi.single_apply, eq_comm]
  done

theorem sum_s_pderiv_detR (h : P ≤ R) (a' a : Fin P) :
    ∑ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      if a' = a then detR P Q R h else 0 := by
  classical
  have e : ∀ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      ∑ j : Fin P, if Fin.castLE h j = c then blockR (Q := Q) h a' j * (blockR (Q := Q) h).adjugate j a
        else 0 := by
    intro c
    rw [pderiv_s_detR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · simp [blockR, hj]
    · simp
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Matrix.mul_apply, Matrix.mul_adjugate, detR_eq]
  simp [Matrix.one_apply]

abbrev phiR (P Q R : ℕ) : Mdl P Q →ₐ[ℂ] Pol P Q R 0 := aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2

theorem pderiv_s_phiR (a : Fin P) (c : Fin R) (H : Mdl P Q) :
    pderiv (Sum.inl a, Sum.inl c) (phiR P Q R H) =
      ∑ b' : Fin Q, phiR P Q R (pderiv (a, b') H) * X (Sum.inr b', Sum.inl c) := by
  classical
  rw [ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq, Fintype.sum_prod_type]
  simp only [pderiv_s_mR, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

theorem pderiv_w_phiR (b : Fin Q) (c : Fin R) (H : Mdl P Q) :
    pderiv (Sum.inr b, Sum.inl c) (phiR P Q R H) =
      ∑ a' : Fin P, phiR P Q R (pderiv (a', b) H) * X (Sum.inl a', Sum.inl c) := by
  classical
  rw [ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq, Fintype.sum_prod_type]
  simp only [pderiv_w_mR, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq]

theorem pderiv_w_detR_pow (h : P ≤ R) (k : ℕ) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h ^ k) = 0 := by
  rw [Derivation.leibniz_pow, pderiv_w_detR]; simp

theorem pderiv_w_s_detR_pow (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) = 0 := by
  rw [pderiv_pderiv_comm, pderiv_w_detR_pow]; simp

theorem sum_s_pderiv_detR_pow (h : P ≤ R) (k : ℕ) (a' a : Fin P) :
    ∑ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k) =
      if a' = a then (k : Pol P Q R 0) * detR P Q R h ^ k else 0 := by
  classical
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  have e : ∀ c : Fin R, X (Sum.inl a', Sum.inl c) *
      ((k : Pol P Q R 0) * (detR P Q R h ^ (k - 1) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h))) =
      (k : Pol P Q R 0) * detR P Q R h ^ (k - 1) *
        (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h)) := fun c => by ring
  rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.mul_sum, sum_s_pderiv_detR]
  split_ifs
  · rcases k with _ | k
    · simp
    · simp [pow_succ]; ring
  · simp

theorem omE_down (a : Fin P) (b : Fin Q) (c : Fin R) (f : Pol P Q R 0) :
    omE ((Sum.inr b, Sum.inl c) : Ln P Q R 0) (Sum.inl a, Sum.inl c) f =
      -(pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) f)) := by
  simp [omE, raiB, lowB, linePos]

theorem partial_derivative_weight_space_formula (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (c : Fin R) (G : Mdl P Q) :
    pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) (phiR P Q R G * detR P Q R h ^ k)) =
      (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) * detR P Q R h ^ k
        + phiR P Q R (pderiv (a, b) G) * detR P Q R h ^ k
        + ∑ a' : Fin P, phiR P Q R (pderiv (a', b) G) *
          (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) := by
  classical
  have hw : pderiv (Sum.inr b, Sum.inl c) (∑ b' : Fin Q, phiR P Q R (pderiv (a, b') G) *
      X (Sum.inr b', Sum.inl c)) = (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) + phiR P Q R (pderiv (a, b) G) := by
    simp only [map_sum, Derivation.leibniz, pderiv_w_phiR, pderiv_X, smul_eq_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b' _ => by ring
    · simp only [Pi.single_apply, Prod.mk.injEq, Sum.inr.injEq, and_true, mul_ite, mul_one, mul_zero]
      simp
  rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, Derivation.leibniz, Derivation.leibniz,
    pderiv_s_phiR, hw, pderiv_w_phiR, pderiv_w_s_detR_pow, pderiv_w_detR_pow]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun a' _ => (by ring :
    pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k) * (phiR P Q R (pderiv (a', b) G) * X (Sum.inl a', Sum.inl c)) =
      phiR P Q R (pderiv (a', b) G) * (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)))]
  ring

theorem opR_down (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    opR P Q R k (Sum.inr b) (Sum.inl a) G =
      -(∑ a' : Fin P, ∑ b' : Fin Q, X (a', b') * pderiv (a', b) (pderiv (a, b') G)
        + ((R + k : ℕ) : ℂ) • pderiv (a, b) G) := by
  simp [opR, LinearMap.sum_apply, Module.End.mul_apply]

theorem sum_A (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) * detR P Q R h ^ k =
      (∑ a' : Fin P, ∑ b' : Fin Q, mR P Q R a' b' * phiR P Q R (pderiv (a', b) (pderiv (a, b') G))) *
        detR P Q R h ^ k := by
  rw [← Finset.sum_mul]
  congr 1
  simp only [mR, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b'; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem sum_C (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, ∑ a' : Fin P, phiR P Q R (pderiv (a', b) G) *
        (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) =
      phiR P Q R (pderiv (a, b) G) * ((k : Pol P Q R 0) * detR P Q R h ^ k) := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_s_pderiv_detR_pow, mul_ite, mul_zero]
  simp

theorem embR_eq' (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    embR P Q R h k G = phiR P Q R G * detR P Q R h ^ k := embR_eq h k G

end GlobalTheory.CharPair.Down

namespace GlobalTheory.CharPair

open GlobalTheory.CharPair.Down in

theorem fockAct1_embR_inr_inl (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inl a)) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inl a) G) := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [embR_eq', embR_eq', opR_down]
  simp only [omE_down, partial_derivative_weight_space_formula, Finset.sum_neg_distrib, Finset.sum_add_distrib, sum_A, sum_C,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [map_neg, map_add, map_sum, map_mul, map_smul, phiR, aeval_X]
  rw [nsmul_eq_mul, Algebra.smul_def, map_natCast]
  push_cast
  ring

end GlobalTheory.CharPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionUpperLeftCommutesEmbedding
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.FirstBlock

section General

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem der_aeval {σ : Type} [Fintype σ] [DecidableEq σ] (d : Derivation K A A) (z : σ → A)
    (G : MvPolynomial σ K) : d (aeval z G) = ∑ i, aeval z (pderiv i G) * d (z i) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e : ∀ i, aeval z (pderiv i (p * X n)) * d (z i) =
        (if n = i then aeval z p * d (z i) else 0) + z n * (aeval z (pderiv i p) * d (z i)) := by
      intro i
      by_cases hi : n = i
      · subst hi
        simp [Derivation.leibniz]; ring
      · simp [Derivation.leibniz, hi, pderiv_X, Pi.single_apply]; ring
    simp only [e, Finset.sum_add_distrib]
    simp [hp, Finset.mul_sum]

theorem der_prod {ι : Type} [DecidableEq ι] (d : Derivation K A A) (s : Finset ι) (f : ι → A) :
    d (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * d (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun e => ha (e ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      mul_assoc]

theorem der_det {n : Type} [Fintype n] [DecidableEq n] (d : Derivation K A A) (M : Matrix n n A) :
    d M.det = ∑ i, (M.updateRow i fun j => d (M i j)).det := by
  simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.smul_sum, Units.smul_def, Units.smul_def, map_zsmul, der_prod,
    ← Equiv.sum_comp σ (fun i => ∏ x, (M.updateRow i fun j => d (M i j)) (σ x) x)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Matrix.updateRow_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Matrix.updateRow_ne (fun e => (Finset.mem_erase.1 hj).1 (σ.injective e))]

end General

variable {P Q R : ℕ}

noncomputable def rowDer (Q R : ℕ) (a a' : Fin P) : Derivation ℂ (Pol P Q R 0) (Pol P Q R 0) :=
  ∑ c : Fin R, (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)

theorem rowDer_apply (a a' : Fin P) (F : Pol P Q R 0) :
    rowDer Q R a a' F = ∑ c : Fin R, X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F := by
  have := map_sum (Derivation.coeFnAddMonoidHom (R := ℂ) (A := Pol P Q R 0) (M := Pol P Q R 0))
    (fun c : Fin R => (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)) Finset.univ
  have h2 := congrFun this F
  rw [Finset.sum_apply] at h2
  exact h2

theorem rowDer_X_inl_inl (a a' i : Fin P) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inl i, Sum.inl c)) = if i = a' then X (Sum.inl a, Sum.inl c) else 0 := by
  rw [rowDer_apply]
  by_cases h : i = a' <;> simp [pderiv_X, Pi.single_apply, h]

theorem rowDer_w (a a' : Fin P) (b : Fin Q) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inr b, Sum.inl c)) = 0 := by
  rw [rowDer_apply]
  simp [pderiv_X, Pi.single_apply]

theorem rowDer_mR (a a' i : Fin P) (b : Fin Q) :
    rowDer Q R a a' (mR P Q R i b) = if i = a' then mR P Q R a b else 0 := by
  simp only [mR, map_sum, Derivation.leibniz, rowDer_X_inl_inl, rowDer_w, smul_eq_mul]
  split_ifs <;> simp [mul_comm]

theorem rowDer_detR (h : P ≤ R) (a a' : Fin P) :
    rowDer Q R a a' (detR P Q R h) = if a = a' then detR P Q R h else 0 := by
  rw [detR, der_det, Finset.sum_eq_single a']
  · simp only [Matrix.of_apply, rowDer_X_inl_inl, if_true]
    split_ifs with e
    · subst e
      congr 1
      exact Matrix.updateRow_eq_self _ _
    · exact Matrix.det_updateRow_eq_zero (M := Matrix.of fun a c : Fin P =>
        (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) e
  · intro i _ hi
    simp only [Matrix.of_apply, rowDer_X_inl_inl, if_neg hi]
    exact Matrix.det_eq_zero_of_row_eq_zero i (by simp)
  · simp

theorem act_eq (a a' : Fin P) (F : Pol P Q R 0) :
    fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) F =
      rowDer Q R a a' F + (if a = a' then (R : ℂ) / 2 else 0) • F := by
  have hpp : ∀ c : Fin R, omE (p := P) (q := Q) (r := R) (s := 0) (Sum.inl a, Sum.inl c) (Sum.inl a', Sum.inl c) F =
      X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F + (if a = a' then (1 / 2 : ℂ) else 0) • F := by
    intro c
    simp only [omE, raiB, lowB, linePos]
    by_cases e : a = a' <;> simp [e]
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowDer_apply]
  simp only [hpp, Finset.sum_add_distrib, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  split_ifs
  · congr 2; ring
  · simp

theorem act_first_block : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a a' : Fin P) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inl a') G) := by
  intro P Q R h k a a' G
  have hk : rowDer Q R a a' (detR P Q R h ^ k) = (if a = a' then (k : ℂ) else 0) • detR P Q R h ^ k := by
    rw [Derivation.leibniz_pow, rowDer_detR]
    split_ifs
    · rcases k with _ | k
      · simp
      · rw [Nat.cast_smul_eq_nsmul, Nat.add_sub_cancel, smul_eq_mul, ← pow_succ]
    · simp
  have hG : rowDer Q R a a' (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      ∑ b, mR P Q R a b * aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (pderiv (a', b) G) := by
    rw [der_aeval, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [rowDer_mR, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_comm]
  have he : ∀ H, embR P Q R h k H =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) H * detR P Q R h ^ k := fun H => rfl
  have ho : opR P Q R k (Sum.inl a) (Sum.inl a') G =
      ∑ b, X (a, b) * pderiv (a', b) G + (if a = a' then (k : ℂ) + (R : ℂ) / 2 else 0) • G := by
    by_cases e : a = a' <;> simp [opR, LinearMap.sum_apply, e]
  rw [act_eq, he, he, ho, Derivation.leibniz, hk, hG, map_add, map_sum, map_smul]
  simp only [map_mul, aeval_X, smul_eq_mul, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [mul_comm (detR P Q R h ^ k)]
  split_ifs
  · module
  · simp

end GlobalTheory.CharPair.FirstBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobQFixedMemRange
section
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime]

noncomputable def frobQEquiv (r : ℕ) (hr : 0 < r) : Qr p r ≃ₐ[ℚ_[p]] Qr p r :=
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  AlgEquiv.ofBijective (frobQ p r)
    ((frobQ p r).toLinearMap.injective_iff_surjective.mp (frobQ p r).toRingHom.injective |>
      fun hs => ⟨(frobQ p r).toRingHom.injective, hs⟩)

theorem frobQEquiv_pow_apply (r : ℕ) (hr : 0 < r) (i : ℕ) (b : Qr p r) :
    (((frobQEquiv p r hr ^ i) b : Qr p r) : PadicAlgCl p) = (frobK p (Q0 p) ^ i) (b : PadicAlgCl p) := by
  induction i generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]
    rfl

theorem orderOf_frobQEquiv (r : ℕ) (hr : 0 < r) : orderOf (frobQEquiv p r hr) = r := by
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  have key : ∀ i : ℕ, frobQEquiv p r hr ^ i = 1 ↔ r ∣ i := by
    intro i
    rw [← IsFrobOn.pow_fixes_iff p (Q0 p) hK hr ((isFrob_frobK hK).isFrobOn r) i]
    constructor
    · intro h x hx
      have := frobQEquiv_pow_apply p r hr i ⟨x, hx⟩
      rw [h] at this
      exact this.symm
    · intro h
      refine AlgEquiv.ext fun b => Subtype.ext ?_
      rw [frobQEquiv_pow_apply]
      exact h _ b.2
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((key r).2 dvd_rfl)
  · exact (key _).1 (pow_orderOf_eq_one _)

end GlobalTheory.LKRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPreservesIntegerRingStatement
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_preserves_integer_ring : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), ∀ x ∈ intR p K r, frobR p K r x ∈ intR p K r := by
  first | exact @GlobalTheory.LKLoc.frobR_mem_intR | exact GlobalTheory.LKLoc.frobR_mem_intR | (intros; apply GlobalTheory.LKLoc.frobR_mem_intR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FujisakiDivisionQuaternionAlgebraModCentreStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fujisaki_divisionQuaternionAlgebra_mod_centre : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∃ C : Set (DA F a b), IsCompact C ∧ ∀ y : DA F a b, IsUnit (nrm y) → ∃ (δ : ℍ[F, a, b]) (l : AF F) (c c' : DA F a b), nrm δ ≠ 0 ∧ IsUnit l ∧ c ∈ C ∧ c' ∈ C ∧ c * c' = 1 ∧ c' * c = 1 ∧ y = l • (rat δ * c) := by
  first | exact @GlobalTheory.QSA.FujisakiQ.fujisaki_mod_centre | exact GlobalTheory.QSA.FujisakiQ.fujisaki_mod_centre | (intros; apply GlobalTheory.QSA.FujisakiQ.fujisaki_mod_centre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfStepsStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeHermitianCombination_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FinSt := by
  first | exact @GlobalTheory.IsoTriv.HermRead.finSt_of | exact GlobalTheory.IsoTriv.HermRead.finSt_of | (intros; apply GlobalTheory.IsoTriv.HermRead.finSt_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormScaledEqSignAbsInvStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussIntegral_normForm_scaled_eq_sign_abs_inv : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : Fˣ, HasGauss μ (fun z => ψ ((t : F) * Algebra.norm F z)) (g * (sgn E t * ((nabs F t)⁻¹ : ℝ))) := by
  first | exact @GlobalTheory.KSp.hasGauss_norm_mul | exact GlobalTheory.KSp.hasGauss_norm_mul | (intros; apply GlobalTheory.KSp.hasGauss_norm_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermConstantsEqAlongAffineSpaceSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem germ_cstT_eq_germ_ringOf_C : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (n : ℕ) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg n → ∀ (z : X) (r : Rg), gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f r) = gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g (MvPolynomial.C r)) := by
  intro Rg _ A₀ T X f n g φ p h z r
  have e0 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
  have e1 : gs φ z ⊤ (cstT f r) = gs (φ ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) :=
    gs_pull φ f z ⊤ trivial _
  have h1 := gs_pull (p ≫ g) (affπ Rg n) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)
  have h2 := gs_pull p g z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r))
  rw [Category.assoc] at h1
  rw [e1, h, ← h1]
  refine Eq.trans ?_ h2.symm
  change gs (p ≫ g) z ⊤ ((affπ Rg n).appTop _) = _
  rw [e0]

end GlobalTheory.FormsLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInducedTypeCharEqProductListStatement
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInducedTypeChar_eq_productList : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (s : SSParam p ℂ r), ∃ l : List (Cyc s.1), l.Nodup ∧ (∀ c, c ∈ l) ∧ typeChar s = GlobalTheory.GLq.hcL (l.map fun c => (⟨cycLen s.1 c, cuspOn (s.2 c)⟩ : GlobalTheory.GLq.Pc p)) r := by
  first | exact @GlobalTheory.TypeCharProduct.typeChar_eq_hcL | exact GlobalTheory.TypeCharProduct.typeChar_eq_hcL | (intros; apply GlobalTheory.TypeCharProduct.typeChar_eq_hcL <;> assumption)
end

