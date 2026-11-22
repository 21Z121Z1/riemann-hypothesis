import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

def μc (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

lemma μc_prim (q : ℕ) [NeZero q] : IsPrimitiveRoot (μc q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma aeval_cyc {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    aeval x (cyclotomic n ℤ) = eval x (cyclotomic n R) := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]

lemma transfer {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (P : ℤ[X])
    (hP : aeval (μc q) P = 0) : aeval ζ.1 P = 0 := by
  have hμ := μc_prim q
  have h1 : cyclotomic q ℤ = minpoly ℤ (μc q) := cyclotomic_eq_minpoly hμ (NeZero.pos q)
  have hd : cyclotomic q ℤ ∣ P := h1 ▸ minpoly.isIntegrallyClosed_dvd (hμ.isIntegral (NeZero.pos q)) hP
  obtain ⟨Q, rfl⟩ := hd
  rw [map_mul, ζ.2.2, zero_mul]

lemma transfer2 {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (F : (ℤ[X])[X])
    (hF : F.map (aeval (μc q)).toRingHom = 0) : F.map (aeval ζ.1).toRingHom = 0 := by
  ext k
  rw [coeff_map, coeff_zero]
  apply transfer ζ
  have := congrArg (fun G => coeff G k) hF
  simpa [coeff_map] using this

lemma nthRoots_eq (q : ℕ) [NeZero q] :
    nthRootsFinset q (1 : ℂ) = (Finset.range q).image (fun a => μc q ^ a) := by
  have hμ := μc_prim q
  ext z
  rw [mem_nthRootsFinset (NeZero.pos q), Finset.mem_image]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hμ.eq_pow_of_pow_eq_one hz
    exact ⟨i, Finset.mem_range.2 hi, rfl⟩
  · rintro ⟨a, -, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]

lemma primRoots_eq (q : ℕ) [NeZero q] :
    primitiveRoots q ℂ = ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun a => μc q ^ a) := by
  have hμ := μc_prim q
  ext z
  rw [mem_primitiveRoots (NeZero.pos q), Finset.mem_image]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hμ.eq_pow_of_pow_eq_one hz.pow_eq_one
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, (hμ.pow_iff_coprime (NeZero.pos q) i).1 hz⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact hμ.pow_of_coprime a (Finset.mem_filter.1 ha).2

lemma injOn (q : ℕ) [NeZero q] (s : Finset ℕ) (hs : s ⊆ Finset.range q) :
    Set.InjOn (fun a => μc q ^ a) s := by
  intro i hi j hj h
  exact (μc_prim q).pow_inj (Finset.mem_range.1 (hs hi)) (Finset.mem_range.1 (hs hj)) h

lemma C_prod_range (q : ℕ) [NeZero q] :
    ∏ a ∈ Finset.range q, (X - C (μc q ^ a)) = (X ^ q - 1 : ℂ[X]) := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos q) (μc_prim q), nthRoots_eq,
    Finset.prod_image (injOn q _ (subset_refl _))]

lemma C_prod_coprime (q : ℕ) [NeZero q] :
    ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C (μc q ^ a)) = cyclotomic q ℂ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (μc_prim q), primRoots_eq,
    Finset.prod_image (injOn q _ (Finset.filter_subset _ _))]

lemma C_prod_erase (q : ℕ) [NeZero q] :
    ∏ a ∈ (Finset.range q).erase 0, (X - C (μc q ^ a)) = ∑ i ∈ Finset.range q, (X ^ i : ℂ[X]) := by
  have h0 : 0 ∈ Finset.range q := Finset.mem_range.2 (NeZero.pos q)
  have h := Finset.mul_prod_erase (Finset.range q) (fun a => (X - C (μc q ^ a) : ℂ[X])) h0
  have hne : (X - C (1 : ℂ) : ℂ[X]) ≠ 0 := X_sub_C_ne_zero 1
  apply mul_left_cancel₀ hne
  calc (X - C (1 : ℂ)) * ∏ a ∈ (Finset.range q).erase 0, (X - C (μc q ^ a))
      = ∏ a ∈ Finset.range q, (X - C (μc q ^ a)) := by simpa only [pow_zero] using h
    _ = X ^ q - 1 := C_prod_range q
    _ = (X - C (1 : ℂ)) * ∑ i ∈ Finset.range q, (X ^ i : ℂ[X]) := by
        rw [map_one, mul_comm, geom_sum_mul]

end GlobalTheory.EtC.PrimBasic

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

lemma prim_pow_q {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := transfer ζ (X ^ q - 1) (by simp [(μc_prim q).pow_eq_one])
  simpa [sub_eq_zero] using h

lemma prod_range {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ Finset.range q, (X - C (ζ.1 ^ a)) = (X ^ q - 1 : A[X]) := by
  have h := transfer2 ζ (∏ a ∈ Finset.range q, (X - C X ^ a) - (X ^ q - 1 : (ℤ[X])[X])) (by
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_range, sub_self])
  simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  simpa only [← C_pow, sub_eq_zero] using h

lemma prod_coprime {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C (ζ.1 ^ a)) = cyclotomic q A := by
  have h := transfer2 ζ (∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C X ^ a)
      - cyclotomic q (ℤ[X])) (by
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_coprime, sub_self])
  simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  simpa only [← C_pow, sub_eq_zero] using h

lemma prod_erase {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ (Finset.range q).erase 0, (1 - ζ.1 ^ a) = (q : A) := by
  have h := transfer2 ζ (∏ a ∈ (Finset.range q).erase 0, (X - C X ^ a) - ∑ i ∈ Finset.range q, (X ^ i : (ℤ[X])[X])) (by
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_erase, sub_self])
  simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  have h2 := congrArg (eval (1 : A)) h
  simp only [eval_sub, eval_prod, eval_finset_sum, eval_X, eval_C, eval_pow, one_pow, eval_zero,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, sub_eq_zero] at h2
  simpa [← C_pow] using h2

end GlobalTheory.EtC.PrimBasic

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

lemma isUnit_one_sub {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (c : ℕ)
    (hc : c % q ≠ 0) : IsUnit (1 - ζ.1 ^ c) := by
  have hmem : c % q ∈ (Finset.range q).erase 0 :=
    Finset.mem_erase.2 ⟨hc, Finset.mem_range.2 (Nat.mod_lt _ (NeZero.pos q))⟩
  have hd : (1 - ζ.1 ^ (c % q)) ∣ (q : A) :=
    (Finset.dvd_prod_of_mem (fun a => 1 - ζ.1 ^ a) hmem).trans (dvd_of_eq (prod_erase ζ))
  rw [pow_eq_pow_mod c (prim_pow_q ζ)]
  exact isUnit_of_dvd_unit hd ζ.2.1

lemma isUnit_val {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : IsUnit ζ.1 := by
  refine isUnit_iff_exists_inv.2 ⟨ζ.1 ^ (q - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q), prim_pow_q ζ]

lemma isUnit_pow_sub_pow_of_le {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (a b : ℕ)
    (hab : ¬ a ≡ b [MOD q]) (hle : b ≤ a) : IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hd : d % q ≠ 0 := by
    intro h0
    apply hab
    exact (Nat.modEq_iff_dvd' hle).2 (by simpa using Nat.dvd_of_mod_eq_zero h0) |>.symm
  have e : ζ.1 ^ (b + d) - ζ.1 ^ b = -(ζ.1 ^ b * (1 - ζ.1 ^ d)) := by ring
  rw [e]
  exact (((isUnit_val ζ).pow b).mul (isUnit_one_sub ζ d hd)).neg

theorem prim_basic : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], (∀ ζ : Prim q A, ζ.1 ^ q = 1) ∧ (∀ (ζ : Prim q A) (a : ℕ), Nat.Coprime a q → ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ a) ∧ (∀ (ζ : Prim q A) (a b : ℕ), ¬ a ≡ b [MOD q] → IsUnit (ζ.1 ^ a - ζ.1 ^ b)) ∧ (∀ (ζ : Prim q A) (x : A), x ^ q = 1 → ∏ a ∈ Finset.range q, (x - ζ.1 ^ a) = 0) ∧ (∀ (ζ ξ : Prim q A), ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (ξ.1 - ζ.1 ^ a) = 0) ∧ ∀ (r : ℕ), r ∣ q → ∀ ζ : Prim q A, ∃ ξ : Prim r A, ξ.1 = ζ.1 ^ (q / r) := by
  intro q _ A _
  refine ⟨fun ζ => prim_pow_q ζ, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ a ha
    have h : aeval (ζ.1 ^ a) (cyclotomic q ℤ) = 0 := by
      rw [← aeval_X_pow (R := ℤ), ← aeval_comp]
      apply transfer ζ
      rw [aeval_comp, aeval_X_pow, aeval_cyc]
      exact ((μc_prim q).pow_of_coprime a ha).isRoot_cyclotomic (NeZero.pos q)
    exact ⟨(⟨ζ.1 ^ a, ζ.2.1, h⟩ : {z : A // IsUnit (q : A) ∧ aeval z (cyclotomic q ℤ) = 0}), rfl⟩
  · intro ζ a b hab
    rcases le_total b a with hle | hle
    · exact isUnit_pow_sub_pow_of_le ζ a b hab hle
    · have := isUnit_pow_sub_pow_of_le ζ b a (fun h => hab h.symm) hle
      have e : ζ.1 ^ a - ζ.1 ^ b = -(ζ.1 ^ b - ζ.1 ^ a) := by ring
      rw [e]; exact this.neg
  · intro ζ x hx
    have h := congrArg (eval x) (prod_range ζ)
    simpa [eval_prod, hx] using h
  · intro ζ ξ
    have h := congrArg (eval ξ.1) (prod_coprime ζ)
    rw [← aeval_cyc, ξ.2.2] at h
    simpa [eval_prod] using h
  · intro r hr ζ
    have hq0 : q ≠ 0 := NeZero.ne q
    have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (Nat.eq_zero_of_zero_dvd hr)
    have hk0 : q / r ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hr) (Nat.pos_of_ne_zero hr0)).ne'
    have hunit : IsUnit (r : A) := by
      obtain ⟨k, hk⟩ := hr
      have : IsUnit ((r : A) * k) := by rw [← Nat.cast_mul, ← hk]; exact ζ.2.1
      exact isUnit_of_mul_isUnit_left this
    have h : aeval (ζ.1 ^ (q / r)) (cyclotomic r ℤ) = 0 := by
      rw [← aeval_X_pow (R := ℤ), ← aeval_comp]
      apply transfer ζ
      rw [aeval_comp, aeval_X_pow, aeval_cyc]
      have hp := (μc_prim q).pow_of_dvd hk0 (Nat.div_dvd_of_dvd hr)
      rw [Nat.div_div_self hr hq0] at hp
      exact hp.isRoot_cyclotomic (Nat.pos_of_ne_zero hr0)
    exact ⟨(⟨ζ.1 ^ (q / r), hunit, h⟩ : {z : A // IsUnit (r : A) ∧ aeval z (cyclotomic r ℤ) = 0}), rfl⟩

end GlobalTheory.EtC.PrimBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoUnitaryOffDiagNormSqZeroIffMemMaxCompact
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.OffDiagK

def sgn {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 1 else -1

def fi {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 0 else 1

lemma Jm_eq {n : ℕ} (ε : Fin n → Bool) :
    Jm ε = Matrix.diagonal (fun a => ((sgn ε a : ℝ) : ℂ)) := by
  unfold Jm sgn; congr 1; funext a; split_ifs <;> simp

lemma star_mul_self' (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl

lemma mul_star_self' (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, star_mul_self']

lemma col_sum {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) (b : Fin n) :
    ∑ a, sgn ε a * ‖M a b‖ ^ 2 = sgn ε b := by
  have hb := congrFun (congrFun h b) b
  rw [Jm_eq, Matrix.mul_apply] at hb
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at hb
  apply Complex.ofReal_injective
  push_cast
  rw [← hb]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_right_comm, star_mul_self']; push_cast; ring

lemma row_sum {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : M * Jm ε * Mᴴ = Jm ε) (a : Fin n) :
    ∑ b, sgn ε b * ‖M a b‖ ^ 2 = sgn ε a := by
  have ha := congrFun (congrFun h a) a
  rw [Jm_eq, Matrix.mul_apply] at ha
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at ha
  apply Complex.ofReal_injective
  push_cast
  rw [← ha]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_right_comm, mul_star_self']; push_cast; ring

lemma other_side {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) : M * Jm ε * Mᴴ = Jm ε := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have h1 : (Jm ε * Mᴴ * Jm ε) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, h, hJ]
  have h2 : M * (Jm ε * Mᴴ * Jm ε) = 1 := mul_eq_one_comm.mp h1
  calc M * Jm ε * Mᴴ = M * (Jm ε * Mᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h2, Matrix.one_mul]

lemma key {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) :
    ∑ a, ∑ b, (fi ε b * sgn ε a - fi ε a * sgn ε b) * ‖M a b‖ ^ 2 = 0 := by
  have h1 : ∑ b, fi ε b * (∑ a, sgn ε a * ‖M a b‖ ^ 2) = ∑ b, fi ε b * sgn ε b := by
    simp only [col_sum ε M h]
  have h2 : ∑ a, fi ε a * (∑ b, sgn ε b * ‖M a b‖ ^ 2) = ∑ a, fi ε a * sgn ε a := by
    simp only [row_sum ε M (other_side ε M h)]
  simp only [Finset.mul_sum] at h1 h2
  rw [Finset.sum_comm] at h1
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ a, ∑ b, fi ε b * sgn ε a * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε b * (sgn ε a * ‖M a b‖ ^ 2) by
      simp only [mul_assoc],
    show (∑ a, ∑ b, fi ε a * sgn ε b * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε a * (sgn ε b * ‖M a b‖ ^ 2) by
      simp only [mul_assoc], h1, h2, sub_self]

lemma offdiag_zero {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) (hTF : ∀ a b, ε a = true → ε b = false → M a b = 0) :
    ∀ a b, ε a = false → ε b = true → M a b = 0 := by
  have hk := key ε M h
  have hs : ∑ a, ∑ b, (fi ε b * sgn ε a - fi ε a * sgn ε b) * ‖M a b‖ ^ 2
      = - ∑ a, ∑ b, (if ε a = false ∧ ε b = true then ‖M a b‖ ^ 2 else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    cases ha : ε a <;> cases hb : ε b <;> simp [fi, sgn, ha, hb, hTF a b]
  rw [hs, neg_eq_zero] at hk
  intro a b ha hb
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs <;> positivity)).mp hk a (Finset.mem_univ _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by
    split_ifs <;> positivity)).mp h0 b (Finset.mem_univ _)
  simp only [ha, hb, and_self, if_true] at h1
  simpa using h1

lemma comm_of {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hTF : ∀ a b, ε a = true → ε b = false → M a b = 0)
    (hFT : ∀ a b, ε a = false → ε b = true → M a b = 0) : M * Jm ε = Jm ε * M := by
  ext a b
  rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases ha : ε a <;> cases hb : ε b <;> simp [sgn, ha, hb, hTF a b, hFT a b]

end GlobalTheory.OffDiagK

open GlobalTheory.OffDiagK in

theorem GlobalTheory.offDiag_zero_iff_mem_K : ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε),
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 = 0 ↔ g ∈ KG ε := by
  intro n ε g
  have hg : (toM g)ᴴ * Jm ε * toM g = Jm ε := g.2
  rw [Formalism.REAL.mem_KG, Fintype.sum_eq_zero_iff_of_nonneg (fun _ => by positivity)]
  constructor
  · intro h0
    have hTF : ∀ a b, ε a = true → ε b = false → toM g a b = 0 := by
      intro a b ha hb
      have := congrFun h0 ⟨(a, b), ha, hb⟩
      simpa using this
    have hFT := offdiag_zero ε _ hg hTF
    have hc := comm_of ε _ hTF hFT
    refine ⟨?_, hc⟩
    rw [Matrix.mem_unitaryGroup_iff']
    have hJ := Formalism.REAL.Jm_mul_self ε
    calc star (toM g) * toM g = (toM g)ᴴ * (toM g * Jm ε) * Jm ε := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.star_eq_conjTranspose]
      _ = 1 := by rw [hc, ← Matrix.mul_assoc, hg, hJ]
  · rintro ⟨_, hc⟩
    funext z
    obtain ⟨⟨a, b⟩, ha, hb⟩ := z
    simp only at ha hb
    have e := congrFun (congrFun hc a) b
    rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [sgn, ha, hb] at e
    push_cast at e
    have h0 : toM g a b = 0 := by linear_combination (-1/2 : ℂ) * e
    simp [h0]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientTransitionSurjectiveSameSubgroup
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.QuotTransition

theorem transition_surjective : ∀ (O : Type) [CommRing O] (A₁ : Type) [CommRing A₁] [HopfAlgebra O A₁] [IsCocomm O A₁] [Module.Finite O A₁] [Module.Projective O A₁] (A₂ : Type) [CommRing A₂] [HopfAlgebra O A₂] [IsCocomm O A₂] [Module.Finite O A₂] [Module.Projective O A₂] (B₁ : Type) [CommRing B₁] [HopfAlgebra O B₁] [IsCocomm O B₁] [Module.Finite O B₁] [Module.Projective O B₁] (B₂ : Type) [CommRing B₂] [HopfAlgebra O B₂] [IsCocomm O B₂] [Module.Finite O B₂] [Module.Projective O B₂] (π : A₂ →ₐc[O] A₁) (j₁ : B₁ →ₐc[O] A₁) (j₂ : B₂ →ₐc[O] A₂) (r : B₂ →ₐc[O] B₁) (ρ : A₁ →ₗ[O] B₁), (∀ b, ρ (j₁ b) = b) → (∀ b, j₁ (r b) = π (j₂ b)) → kerIdeal j₁ = Ideal.map (π : A₂ →ₐ[O] A₁) (kerIdeal j₂) → Function.Surjective r := by
  intro O _ A₁ _ _ _ _ _ A₂ _ _ _ _ _ B₁ _ _ _ _ _ B₂ _ _ _ _ _ π j₁ j₂ r ρ hρ hsq hker
  let j₁' : B₁ →ₗ[O] A₁ := (j₁ : B₁ →ₐ[O] A₁).toLinearMap
  let r' : B₂ →ₗ[O] B₁ := (r : B₂ →ₐ[O] B₁).toLinearMap
  have hcomp : j₁' ∘ₗ r' = ((π.comp j₂ : B₂ →ₐc[O] A₁) : B₂ →ₐ[O] A₁).toLinearMap := by
    ext b
    exact hsq b
  have hs : Function.Surjective r' := by
    refine GlobalTheory.surjective_of_fibre_rank O B₂ B₁ r' fun q => ?_
    have hinj : Function.Injective (j₁'.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := ρ.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have hid : ρ ∘ₗ j₁' = LinearMap.id := LinearMap.ext hρ
      rw [hid, LinearMap.baseChange_id, LinearMap.id_apply]
    have h1 : fibreRank (j₁' ∘ₗ r') q = fibreRank r' q := by
      rw [fibreRank, fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp]
      exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    have h2 : fibreRank j₁' q = fibreDim B₁ q := LinearMap.finrank_range_of_inj hinj
    have h3 := fibreDim_eq_ker_mul_range (π.comp j₂) q
    have h4 := fibreDim_eq_ker_mul_range j₁ q
    rw [kerIdeal_comp, ← hker, ← hcomp] at h3
    have h5 : fibreDim (A₁ ⧸ kerIdeal j₁) q ≠ 0 := fun h0 =>
      fibreDim_ne_zero (A := A₁) q (by rw [h4, h0, zero_mul])
    have h6 : fibreRank (j₁' ∘ₗ r') q = fibreRank j₁' q :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5) (h3.symm.trans h4)
    have h7 : fibreRank r' q = fibreDim B₁ q := by rw [← h1, h6, h2]
    exact h7
  exact hs

end GlobalTheory.QuotTransition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartShearInvariance
section
open GlobalTheory.WeilM Matrix

noncomputable section
open Filter
open scoped Topology

namespace GlobalTheory.RankChart

theorem sb_shear_invariant :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D],
      ∀ f ∈ SB (Matrix (R ⊕ T) D k), ∃ b : kˣ, ∀ (Y : Matrix (R ⊕ T) D k),
        ∀ c ∈ GlobalTheory.LocMod.Inhab.box T R b, f (GlobalTheory.RankChart.shear c Y) = f Y := by
  intro k _ _ _ _ R T D _ _ _ _ _ _ f hf
  obtain ⟨Λ, hΛo, hΛ⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k _ _ f hf
  have hK : IsCompact (tsupport f) := hf.2
  have hc : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k =>
      fromRows (0 : Matrix R D k) (p.1 * p.2.toRows₁) := by
    have hm : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k => p.1 * p.2.toRows₁ :=
      continuous_fst.matrix_mul (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply (Sum.inl i) j).comp continuous_snd)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i
    · simpa using continuous_const
    · simp only [fromRows_apply_inr]
      exact (continuous_apply_apply i j).comp hm
  have hev : ∀ᶠ c in 𝓝 (0 : Matrix T R k), ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ :=
    hK.eventually_forall_of_forall_eventually fun Y _ => by
      have h0 : fromRows (0 : Matrix R D k) ((0 : Matrix T R k) * Y.toRows₁) ∈ Λ := by
        simp
      exact (hc.tendsto ((0 : Matrix T R k), Y)) (hΛo.mem_nhds h0)
  obtain ⟨b, hb⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset hev
  refine ⟨b, fun Y c hcb => ?_⟩
  have hZ : ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ := hb c hcb
  by_cases hY : Y ∈ tsupport f
  · rw [← hΛ Y _ (hZ Y hY), ← shear_sub_self, add_sub_cancel]
  by_cases hY' : shear c Y ∈ tsupport f
  · have h1 := hZ _ hY'
    rw [toRows₁_shear, ← shear_sub_self] at h1
    rw [← hΛ (shear c Y) _ (Λ.neg_mem h1), neg_sub, add_sub_cancel]
  · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hY']

end GlobalTheory.RankChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecomposition
section
open GlobalTheory.WeilM Matrix

namespace GlobalTheory.RankChart

theorem exists_eq_stack (k : Type) [Field k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T]
    [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) (Y : Matrix (R ⊕ T) D k)
    (hrank : Y.rank ≤ Fintype.card R) (hdet : (Y.submatrix Sum.inl τ).det ≠ 0) :
    ∃ C : Matrix T R k, Y = GlobalTheory.RankChart.stack Y.toRows₁ C := by
  classical
  set Y₁ := Y.toRows₁ with hY₁

  have hA : LinearIndependent k (fun i : R => fun j : R => Y (Sum.inl i) (τ j)) := by
    have hu : IsUnit (Y.submatrix Sum.inl τ) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet)
    exact Matrix.linearIndependent_rows_of_isUnit hu
  have hli : LinearIndependent k (fun i : R => Y₁ i) := by
    apply LinearIndependent.of_comp (LinearMap.funLeft k k τ)
    exact hA
  have hfin₁ : Module.finrank k (Submodule.span k (Set.range fun i : R => Y₁ i)) = Fintype.card R :=
    finrank_span_eq_card hli
  have hle : Submodule.span k (Set.range fun i : R => Y₁ i) ≤ Submodule.span k (Set.range Y.row) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩
  have heq : Submodule.span k (Set.range fun i : R => Y₁ i) = Submodule.span k (Set.range Y.row) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hfin₁, ← Matrix.rank_eq_finrank_span_row]
    exact hrank
  have hmem : ∀ t : T, ∃ c : R → k, ∑ i, c i • Y₁ i = Y (Sum.inr t) := by
    intro t
    have : Y (Sum.inr t) ∈ Submodule.span k (Set.range fun i : R => Y₁ i) := by
      rw [heq]; exact Submodule.subset_span ⟨Sum.inr t, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun k).1 this
  choose C hC using hmem
  refine ⟨Matrix.of fun t i => C t i, ?_⟩
  ext (i | t) j
  · simp [stack, hY₁]
  · have := congrFun (hC t) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [stack, fromRows_apply_inr, Matrix.mul_apply, Matrix.of_apply]
    rw [← this]

end GlobalTheory.RankChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLintegralSqNeTopStatement
section
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  first | exact @GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | exact GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | (intros; apply GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnityStatement
section
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_partition_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ι : Type) [Finite ι] (U : ι → Set (Matrix A D k)), (∀ i, IsOpen (U i)) → ∀ f ∈ SB (Matrix A D k), (∀ Y, f Y ≠ 0 → ∃ i, Y ∈ U i) → f ∈ Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} := by
  first | exact @GlobalTheory.CoverSB.mem_span_of_cover | exact GlobalTheory.CoverSB.mem_span_of_cover | (intros; apply GlobalTheory.CoverSB.mem_span_of_cover <;> assumption)
end

