import Formalism.ResultantValuation.Bundle0001
import Mathlib

-- bundled from Formalism.ResultantValuation.ResultantAdjugateProofs.Adjugate
section
open Matrix

noncomputable section

namespace Formalism.ResultantValuation

namespace AdjugateJacobi

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

def minorF (M : Matrix n n R) (k i l j : n) : R :=
  M.adjugate k l * M.adjugate i j - M.adjugate i l * M.adjugate k j

def minorQ (M : Matrix n n R) (k i l j : n) : R :=
  ((M.updateCol i (Pi.single j 1)).updateCol k (Pi.single l 1)).det

def twoCol (k i : n) (u v : n → R) : Matrix n n R :=
  ((1 : Matrix n n R).updateCol k u).updateCol i v

theorem det_twoCol {k i : n} (hki : k ≠ i) (u v : n → R) :
    (twoCol k i u v).det = u k * v i - u i * v k := by
  classical
  let p : n → Prop := fun a => a ≠ k ∧ a ≠ i
  have h : ∀ a, ¬p a → ∀ b, p b → twoCol k i u v a b = 0 := by
    intro a ha b hb
    have hab : a ≠ b := by
      rintro rfl
      exact ha hb
    simp only [twoCol, updateCol_ne hb.2, updateCol_ne hb.1, one_apply_ne hab]
  rw [twoBlockTriangular_det _ p h]
  have h1 : (toSquareBlockProp (twoCol k i u v) p).det = 1 := by
    have : toSquareBlockProp (twoCol k i u v) p = 1 := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      rw [toSquareBlockProp_def, of_apply]
      simp only [twoCol, updateCol_ne hb.2, updateCol_ne hb.1]
      by_cases hab : a = b
      · subst hab; simp
      · rw [one_apply_ne hab, one_apply_ne (fun h => hab (congrArg Subtype.val h))]
    rw [this, det_one]
  rw [h1, one_mul]
  let f : Fin 2 → { a // ¬p a } := ![⟨k, fun h => h.1 rfl⟩, ⟨i, fun h => h.2 rfl⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [f, Subtype.ext_iff, Ne.symm hki]
    · rintro ⟨a, ha⟩
      simp only [p, not_and_or, not_not] at ha
      rcases ha with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  let e : Fin 2 ≃ { a // ¬p a } := Equiv.ofBijective f hf
  rw [← det_submatrix_equiv_self e, det_fin_two]
  simp [e, f, toSquareBlockProp_def, twoCol, updateCol_apply, hki]
  ring

theorem mulVec_adjugate_col (M : Matrix n n R) (l : n) :
    M *ᵥ (fun r => M.adjugate r l) = M.det • Pi.single l 1 := by
  ext a
  have := congrFun (congrFun (mul_adjugate M) a) l
  rw [mul_apply, Matrix.smul_apply, one_apply, smul_eq_mul] at this
  simp only [mulVec, dotProduct, this, Pi.smul_apply, Pi.single_apply, smul_eq_mul, eq_comm]

theorem key (M : Matrix n n R) {k i : n} (hki : k ≠ i) (l j : n) :
    M.det * minorF M k i l j = M.det * (M.det * minorQ M k i l j) := by
  have hN : (twoCol k i (fun r => M.adjugate r l) (fun r => M.adjugate r j)).det =
      minorF M k i l j := by
    rw [det_twoCol hki, minorF]
  have hMN : M * twoCol k i (fun r => M.adjugate r l) (fun r => M.adjugate r j) =
      ((M.updateCol i (M.det • Pi.single j 1)).updateCol k (M.det • Pi.single l 1)) := by
    rw [twoCol, mul_updateCol, mul_updateCol, mul_one, mulVec_adjugate_col,
      mulVec_adjugate_col, updateCol_comm _ hki]
  have := congrArg det hMN
  rw [det_mul, hN, det_updateCol_smul, updateCol_comm _ (Ne.symm hki), det_updateCol_smul,
    updateCol_comm _ hki] at this
  rw [this, minorQ]

end AdjugateJacobi

end Formalism.ResultantValuation
end
end

-- bundled from Formalism.ResultantValuation.ResultantAdjugateProofs.Koszul
section
open Polynomial

noncomputable section

namespace Formalism.ResultantValuation

namespace KoszulProof

variable {k : Type} [Field k] {n : ℕ}

abbrev tT (k : Type) [Field k] (n : ℕ) : truncPoly k n := Ideal.Quotient.mk _ X

lemma tT_pow : (tT k n) ^ n = 0 := by
  rw [tT, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

lemma tT_pow_pred_mul (hn : 1 ≤ n) (a : truncPoly k n) :
    tT k n * (tT k n ^ (n - 1) * a) = 0 := by
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, tT_pow, zero_mul]

abbrev tI (k : Type) [Field k] (n : ℕ) : Submodule (truncPoly k n) (truncPoly k n) :=
  Ideal.span {tT k n}

abbrev tK (k : Type) [Field k] (n : ℕ) : Submodule (truncPoly k n) (truncPoly k n) :=
  LinearMap.ker (tT k n • LinearMap.id : truncPoly k n →ₗ[truncPoly k n] truncPoly k n)

lemma mem_tK (z : truncPoly k n) : z ∈ tK k n ↔ tT k n * z = 0 := by
  simp [tK]

def powMap (hn : 1 ≤ n) : truncPoly k n →ₗ[truncPoly k n] tK k n :=
  LinearMap.codRestrict (tK k n) (tT k n ^ (n - 1) • LinearMap.id) (fun a => by
    rw [mem_tK]; simpa using tT_pow_pred_mul hn a)

end KoszulProof

namespace KoszulProof

variable {k : Type} [Field k] {n : ℕ}

lemma mem_ker_koszul_second_differential (r : ℕ) (x y : truncPoly k n) (v : (Fin r → truncPoly k n) × (Fin r → truncPoly k n)) :
    v ∈ LinearMap.ker (koszulSecondDifferential r x y) ↔ ∀ i, y * v.1 i - x * v.2 i = 0 := by
  rw [LinearMap.mem_ker, funext_iff]
  simp only [koszulSecondDifferential, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]

section Main

variable (hn : 1 ≤ n) (r : ℕ) (u : (truncPoly k n)ˣ) (w : truncPoly k n)

abbrev koszulSecondKernel : Submodule (truncPoly k n) ((Fin r → truncPoly k n) × (Fin r → truncPoly k n)) :=
  LinearMap.ker (koszulSecondDifferential r (tT k n * (u : truncPoly k n)) (tT k n * w))

def fA : koszulSecondKernel r u w →ₗ[truncPoly k n] (Fin r → truncPoly k n ⧸ tI k n) :=
  LinearMap.pi (fun i => (tI k n).mkQ ∘ₗ LinearMap.proj i ∘ₗ
    LinearMap.fst _ _ _ ∘ₗ (koszulSecondKernel r u w).subtype)

def gB : koszulSecondKernel r u w →ₗ[truncPoly k n] (Fin r → truncPoly k n) :=
  (w • LinearMap.fst _ _ _ - (u : truncPoly k n) • LinearMap.snd _ _ _) ∘ₗ (koszulSecondKernel r u w).subtype

lemma gB_apply (v : koszulSecondKernel r u w) (i : Fin r) :
    gB r u w v i = w * v.1.1 i - (u : truncPoly k n) * v.1.2 i := by
  simp [gB]

lemma gB_mem (v : koszulSecondKernel r u w) (i : Fin r) : gB r u w v i ∈ tK k n := by
  rw [mem_tK, gB_apply]
  have h := (mem_ker_koszul_second_differential r _ _ v.1).mp v.2 i
  linear_combination h

def fB : koszulSecondKernel r u w →ₗ[truncPoly k n] (Fin r → tK k n) :=
  LinearMap.pi (fun i => LinearMap.codRestrict (tK k n) (LinearMap.proj i ∘ₗ gB r u w)
    (fun v => by simpa using gB_mem r u w v i))

def fAB : koszulSecondKernel r u w →ₗ[truncPoly k n] (Fin r → truncPoly k n ⧸ tI k n) × (Fin r → tK k n) :=
  (fA r u w).prod (fB r u w)

end Main

end KoszulProof

end Formalism.ResultantValuation
end
end

-- bundled from Formalism.ResultantValuation.ResultantAdjugateProofs.Window
section
open Finset

noncomputable section

namespace Formalism.ResultantValuation

section Padic

variable {l : ℕ} [Fact l.Prime]

private theorem pow_dvd_iff_le_valuation_lemma {x : ℤ_[l]} (hx : x ≠ 0) (n : ℕ) :
    (l : ℤ_[l]) ^ n ∣ x ↔ n ≤ x.valuation := by
  simpa [Ideal.mem_span_singleton] using PadicInt.mem_span_pow_iff_le_valuation x hx n

lemma emultiplicity_eq_valuation {x : ℤ_[l]} (hx : x ≠ 0) :
    emultiplicity (l : ℤ_[l]) x = (x.valuation : ℕ∞) := by
  rw [emultiplicity_eq_coe]
  refine ⟨(pow_dvd_iff_le_valuation_lemma hx _).2 le_rfl, fun h => ?_⟩
  have h1 := (pow_dvd_iff_le_valuation_lemma hx _).1 h
  omega

private theorem not_dvd_one'_lemma_2 : ¬ (l : ℤ_[l]) ∣ 1 := by
  intro h
  have h1 := (pow_dvd_iff_le_valuation_lemma (one_ne_zero : (1 : ℤ_[l]) ≠ 0) 1).1 (by rwa [pow_one])
  rw [PadicInt.valuation_one] at h1
  omega

private theorem prime_l_lemma_3 : Prime (l : ℤ_[l]) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  · intro h
    exact not_dvd_one'_lemma_2 (isUnit_iff_dvd_one.mp h)
  · intro a b hab
    by_cases ha : a = 0
    · left; rw [ha]; exact dvd_zero _
    by_cases hb : b = 0
    · right; rw [hb]; exact dvd_zero _
    have h1 := (pow_dvd_iff_le_valuation_lemma (mul_ne_zero ha hb) 1).1 (by rwa [pow_one])
    rw [PadicInt.valuation_mul ha hb] at h1
    rcases Nat.eq_zero_or_pos a.valuation with h0 | h0
    · right
      have h2 := (pow_dvd_iff_le_valuation_lemma hb 1).2 (by omega)
      rwa [pow_one] at h2
    · left
      have h2 := (pow_dvd_iff_le_valuation_lemma ha 1).2 (by omega)
      rwa [pow_one] at h2

end Padic

lemma lte_unit (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : (u - 1).valuation = 1)
    (i : ℕ) (hi : 1 ≤ i) : ((u ^ i - 1).valuation : ℕ) = 1 + padicValNat l i := by
  classical
  have hp : l.Prime := Fact.out
  have hprime := prime_l_lemma_3 (l := l)
  have hu0 : u - 1 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at hu
    omega
  have hdvd : (l : ℤ_[l]) ∣ u - 1 := by
    have h1 := (pow_dvd_iff_le_valuation_lemma hu0 1).2 (by omega)
    rwa [pow_one] at h1
  have hndvd : ¬ (l : ℤ_[l]) ∣ u := by
    intro h
    apply not_dvd_one'_lemma_2 (l := l)
    have h1 := dvd_sub h hdvd
    rwa [sub_sub_cancel] at h1
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hp.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero l)
  have hv : padicValNat l (l ^ a * m) = a := by
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have h1 := emultiplicity_pow_prime_pow_sub_pow_prime_pow hprime (hp.odd_of_ne_two hl2) hdvd hndvd a
  rw [one_pow] at h1
  have hdvd2 : (l : ℤ_[l]) ∣ u ^ l ^ a - 1 := by
    refine hdvd.trans ?_
    simpa using sub_dvd_pow_sub_pow u 1 (l ^ a)
  have hndvd2 : ¬ (l : ℤ_[l]) ∣ u ^ l ^ a := fun h => hndvd (hprime.dvd_of_dvd_pow h)
  have hm' : ¬ (l : ℤ_[l]) ∣ (m : ℤ_[l]) := by
    intro h
    have hc : Nat.Coprime m l := ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
    obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 hc
    have hst' : (s : ℤ_[l]) * (m : ℤ_[l]) + (t : ℤ_[l]) * (l : ℤ_[l]) = 1 := by
      have h3 := congrArg (Int.cast : ℤ → ℤ_[l]) hst
      push_cast at h3
      exact h3
    apply not_dvd_one'_lemma_2 (l := l)
    rw [← hst']
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)
  have h2 := emultiplicity_pow_sub_pow_of_prime hprime hdvd2 hndvd2 hm'
  rw [one_pow, ← pow_mul] at h2
  have hE : emultiplicity (l : ℤ_[l]) (u ^ (l ^ a * m) - 1) = ((1 + a : ℕ) : ℕ∞) := by
    rw [h2, h1, emultiplicity_eq_valuation hu0, hu]
    norm_cast
  have hne : u ^ (l ^ a * m) - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hE
    exact (ENat.natCast_ne_top (1 + a)) hE.symm
  rw [hv]
  exact_mod_cast (emultiplicity_eq_valuation hne).symm.trans hE

theorem powSubOneValuation : LTEUnit := by
  intro l _ hl2 u hu i hi
  exact lte_unit l hl2 u hu i hi

end Formalism.ResultantValuation
end
end

