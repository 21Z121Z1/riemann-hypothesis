import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import GroundTheory.FunctionField.PlaceSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculus
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.OrdCalc

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem vne (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≠ 0 := (map_ne_zero v.1).2 hx

theorem ord_mul (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (vne v hx) (vne v hy)]; ring

theorem ord_zpow (v : Place k F) (x : F) (m : ℤ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_zpow₀, WithZero.log_zpow]; simp [smul_eq_mul]

theorem le_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) one_ne_zero, WithZero.log_one, neg_nonneg]

theorem le_iff (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) (vne v hy), neg_le_neg_iff]

theorem eq_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x = 1 ↔ ord v x = 0 := by
  have h1 := WithZero.log_le_log (vne v hx) (one_ne_zero (α := WithZero (Multiplicative ℤ)))
  have h2 := WithZero.log_le_log (one_ne_zero (α := WithZero (Multiplicative ℤ))) (vne v hx)
  rw [WithZero.log_one] at h1 h2
  unfold ord
  constructor
  · intro h; rw [h, WithZero.log_one]; simp
  · intro h
    exact le_antisymm (h1.1 (by omega)) (h2.1 (by omega))

theorem exists_unif (v : Place k F) : ∃ π : F, π ≠ 0 ∧ ord v π = 1 := by
  obtain ⟨π, hπ⟩ := v.2.1 (WithZero.exp (-1 : ℤ))
  refine ⟨π, ?_, ?_⟩
  · rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  · unfold ord; rw [hπ, WithZero.log_exp]; simp

theorem nrm_max (v : Place k F) (n : ℕ) (x : Fin n → F) (hx : x ≠ 0) :
    ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hx
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i0, Finset.mem_univ _⟩ (fun i => v.1 (x i))
  have hle : ∀ j, v.1 (x j) ≤ v.1 (x i) := fun j => by
    rw [← hi]; exact Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j)
  refine ⟨i, ?_, hi, ?_, hle⟩
  · intro h0
    have := hle i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  · unfold ordVec ord nrm; rw [hi]

theorem nrm_smul (v : Place k F) (n : ℕ) (x : Fin n → F) (c : F) :
    nrm v (c • x) = v.1 c * nrm v x := by
  unfold nrm
  apply le_antisymm
  · apply Finset.sup_le; intro i _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_mul' le_rfl (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ i))
  · rcases isEmpty_or_nonempty (Fin n) with h | h
    · simp [Finset.univ_eq_empty]
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => v.1 (x i))
      rw [hi]
      calc v.1 c * v.1 (x i) = v.1 ((c • x) i) := by simp
      _ ≤ _ := Finset.le_sup (f := fun i => v.1 ((c • x) i)) (Finset.mem_univ i)

theorem nrm_mulVec_le (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : nrm v (u.mulVec x) ≤ nrm v x := by
  unfold nrm
  apply Finset.sup_le; intro i _
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (u i j) * v.1 (x j) ≤ 1 * Finset.univ.sup (fun i => v.1 (x i)) :=
        mul_le_mul' (hu i j) (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j))
  _ = _ := one_mul _

theorem mul_int (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hu' : ∀ i j, v.1 (u' i j) ≤ 1) : ∀ i j, v.1 ((u * u') i j) ≤ 1 := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [map_mul]
  calc v.1 (u i l) * v.1 (u' l j) ≤ 1 * 1 := mul_le_mul' (hu i l) (hu' l j)
  _ = 1 := one_mul _

theorem det_adj_int (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : v.1 u.det ≤ 1 ∧ ∀ i j, v.1 (u.adjugate i j) ≤ 1 := by
  let M : Matrix (Fin n) (Fin n) v.O := fun i j => ⟨u i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu i j)⟩
  have hM : M.map v.O.subtype = u := by ext i j; rfl
  constructor
  · have e : u.det = ((M.det : v.O) : F) := by
      rw [← hM]; exact (RingHom.map_det v.O.subtype M).symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.det).2
  · intro i j
    have e : u.adjugate i j = ((M.adjugate i j : v.O) : F) := by
      rw [← hM]
      have := congrFun (congrFun (RingHom.map_adjugate v.O.subtype M) i) j
      exact this.symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.adjugate i j).2

theorem unimod_mul_inv (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : Unimod v u) (hu' : Unimod v u') : Unimod v (u * u') ∧ Unimod v u⁻¹ := by
  refine ⟨⟨mul_int v n u u' hu.1 hu'.1, by rw [Matrix.det_mul, map_mul, hu.2, hu'.2, one_mul]⟩, ?_⟩
  have hd : u.det ≠ 0 := fun h => by have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hu.2, inv_one, one_mul]
    exact (det_adj_int v n u hu.1).2 i j
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hu.2, inv_one]

theorem nrm_unimod (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : Unimod v u) : nrm v (u.mulVec x) = nrm v x := by
  have hd : IsUnit u.det := isUnit_iff_ne_zero.2 (fun h => by
    have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this)
  apply le_antisymm (nrm_mulVec_le v n u x hu.1)
  have h := nrm_mulVec_le v n u⁻¹ (u.mulVec x) (unimod_mul_inv v n u u hu hu).2.1
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul u hd, Matrix.one_mulVec] at h

end GlobalTheory.Nef.OrdCalc

open GlobalTheory.Nef.OrdCalc in
theorem GlobalTheory.Nef.ord_calculus : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by
  intro k F _ _ _ v
  exact ⟨fun x y hx hy => ord_mul v x y hx hy, fun x _ m => ord_zpow v x m,
    fun x hx => le_one_iff v x hx, fun x hx => eq_one_iff v x hx, fun x y hx hy => le_iff v x y hx hy,
    exists_unif v, fun n x hx => nrm_max v n x hx, fun n x c => nrm_smul v n x c,
    fun n u x hu => nrm_unimod v n u x hu, fun n u u' hu hu' => unimod_mul_inv v n u u' hu hu'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.PlaceResiduePowerBound

open WithZero

variable {F : Type} [Field F]

theorem pow_inj {e : ℕ} (he : e ≠ 0) {a b : ℤᵐ⁰} (h : a ^ e = b ^ e) : a = b :=
  le_antisymm ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.le)
    ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.ge)

theorem pow_le_one_iff' {e : ℕ} (he : e ≠ 0) {a : ℤᵐ⁰} : a ^ e ≤ 1 ↔ a ≤ 1 := by
  simpa using (pow_le_pow_iff_left₀ (zero_le' (a := a)) (zero_le' (a := (1 : ℤᵐ⁰))) he)

theorem pow_of_iff (v q : Valuation F ℤᵐ⁰) (hq : Function.Surjective q)
    (h : ∀ x, v x ≤ 1 ↔ q x ≤ 1) : ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  obtain ⟨π, hπ⟩ := hq (exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hvπ0 : v π ≠ 0 := (Valuation.ne_zero_iff v).2 hπ0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, v π = exp b := ⟨log (v π), (exp_log hvπ0).symm⟩
  have hb0 : b < 0 := by
    have h1 : v π ≤ 1 := (h π).2 (by rw [hπ, ← exp_zero, exp_le_exp]; norm_num)
    have h2 : v π ≠ 1 := by
      intro h1'
      have : q π⁻¹ ≤ 1 := (h _).1 (by rw [map_inv₀, h1', inv_one])
      rw [map_inv₀, hπ, ← exp_neg, ← exp_zero, exp_le_exp] at this
      norm_num at this
    rw [hb, ← exp_zero, exp_le_exp] at h1
    rw [hb, ne_eq, exp_eq_one] at h2
    omega
  have hbe : (((-b).toNat : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
  refine ⟨(-b).toNat, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero, zero_pow (by omega)]
  have hqx : q x ≠ 0 := (Valuation.ne_zero_iff q).2 hx
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx
  obtain ⟨c, hc⟩ : ∃ c : ℤ, q x = exp c := ⟨log (q x), (exp_log hqx).symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a := ⟨log (v x), (exp_log hvx).symm⟩
  have hqu : q (x * π ^ c) = 1 := by
    rw [map_mul, map_zpow₀, hc, hπ, ← exp_zsmul, ← exp_add, exp_eq_one, smul_eq_mul]; ring
  have hvu : v (x * π ^ c) = exp (a + c * b) := by
    rw [map_mul, map_zpow₀, ha, hb, ← exp_zsmul, ← exp_add, smul_eq_mul]
  have h1 : v (x * π ^ c) ≤ 1 := (h _).2 hqu.le
  have h2 : v (x * π ^ c)⁻¹ ≤ 1 := (h _).2 (by rw [map_inv₀, hqu, inv_one])
  rw [hvu, ← exp_zero, exp_le_exp] at h1
  rw [map_inv₀, hvu, ← exp_neg, ← exp_zero, exp_le_exp] at h2
  have h3 : a + c * b = 0 := by omega
  rw [ha, hc, ← exp_nsmul, exp_inj, nsmul_eq_mul, hbe]
  linear_combination h3

theorem root (v : Valuation F ℤᵐ⁰) (hv : ∃ a, 1 < v a) :
    ∃ q : Valuation F ℤᵐ⁰, Function.Surjective q ∧ ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  classical
  have hS : ∃ n : ℕ, 0 < n ∧ ∃ x, v x = exp (n : ℤ) := by
    obtain ⟨a, ha⟩ := hv
    have ha0 : v a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
    obtain ⟨b, hb⟩ : ∃ b : ℤ, v a = exp b := ⟨_, (exp_log ha0).symm⟩
    rw [hb, ← exp_zero, exp_lt_exp] at ha
    exact ⟨b.toNat, by omega, a, by rw [hb, Int.toNat_of_nonneg ha.le]⟩
  have he0 : 0 < Nat.find hS := (Nat.find_spec hS).1
  obtain ⟨π, hπ⟩ := (Nat.find_spec hS).2
  have hdvd : ∀ x, x ≠ 0 → ∃ m : ℤ, v x = exp ((Nat.find hS : ℤ) * m) := by
    intro x hx
    obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a :=
      ⟨_, (exp_log ((Valuation.ne_zero_iff v).2 hx)).symm⟩
    refine ⟨a / (Nat.find hS : ℤ), ?_⟩
    have hr0 : 0 ≤ a % (Nat.find hS : ℤ) := Int.emod_nonneg _ (by omega)
    have hr1 : a % (Nat.find hS : ℤ) < Nat.find hS := Int.emod_lt_of_pos _ (by omega)
    have hdec := Int.mul_ediv_add_emod a (Nat.find hS : ℤ)
    by_contra hne
    have hr : 0 < a % (Nat.find hS : ℤ) := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hne; rw [ha, exp_inj]; linear_combination -hdec - h
    have hval : v (x * π ^ (-(a / (Nat.find hS : ℤ)))) = exp (((a % (Nat.find hS : ℤ)).toNat : ℕ) : ℤ) := by
      rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, Int.toNat_of_nonneg hr0, exp_inj,
        smul_eq_mul]
      linear_combination -hdec
    exact Nat.find_min hS (show (a % (Nat.find hS : ℤ)).toNat < Nat.find hS by omega)
      ⟨by omega, _, hval⟩
  have hroot : ∀ x, ∃ c : ℤᵐ⁰, c ^ Nat.find hS = v x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero, zero_pow he0.ne']⟩
    · obtain ⟨m, hm⟩ := hdvd x hx
      exact ⟨exp m, by rw [hm, ← exp_nsmul, nsmul_eq_mul]⟩
  choose qf hqf using hroot
  have hle : ∀ {a b : ℤᵐ⁰}, a ^ Nat.find hS ≤ b ^ Nat.find hS → a ≤ b :=
    fun h => (pow_le_pow_iff_left₀ zero_le' zero_le' he0.ne').1 h
  let q : Valuation F ℤᵐ⁰ :=
    { toFun := qf
      map_zero' := pow_inj he0.ne' (by rw [hqf, map_zero, zero_pow he0.ne'])
      map_one' := pow_inj he0.ne' (by rw [hqf, map_one, one_pow])
      map_mul' := fun x y => pow_inj he0.ne' (by rw [hqf, mul_pow, hqf, hqf, map_mul])
      map_add_le_max' := fun x y => by
        have h := v.map_add x y
        rw [← hqf x, ← hqf y, ← hqf (x + y)] at h
        rcases le_max_iff.1 h with h | h
        · exact le_max_of_le_left (hle h)
        · exact le_max_of_le_right (hle h) }
  have hqq : ∀ x, q x = qf x := fun _ => rfl
  refine ⟨q, ?_, Nat.find hS, he0, fun x => by rw [hqq, hqf]⟩
  have hqπ : q π = exp 1 :=
    pow_inj he0.ne' (by rw [hqq, hqf, hπ, ← exp_nsmul, nsmul_eq_mul, mul_one])
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · exact ⟨0, map_zero q⟩
  · refine ⟨π ^ log t, ?_⟩
    rw [map_zpow₀, hqπ, ← exp_zsmul, smul_eq_mul, mul_one, exp_log ht]

theorem exists_one_lt {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : Valuation E ℤᵐ⁰) (hp : Function.Surjective p) : ∃ a : F, 1 < p (algebraMap F E a) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy⟩ := hp (exp (1 : ℤ))
  have hy1 : 1 < p y := by rw [hy, ← exp_zero, exp_lt_exp]; norm_num
  obtain ⟨f, hfm, hfy⟩ := Algebra.IsIntegral.isIntegral (R := F) y
  rw [hfm.as_sum] at hfy
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hfy
  have hlt : p (∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i) <
      p y ^ f.natDegree := by
    apply p.map_sum_lt (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hy1)))
    intro i hi
    rw [map_mul, map_pow]
    calc p (algebraMap F E (f.coeff i)) * p y ^ i ≤ 1 * p y ^ i := mul_le_mul_of_nonneg_right (hcon _) zero_le'
      _ = p y ^ i := one_mul _
      _ < p y ^ f.natDegree := pow_lt_pow_right₀ hy1 (Finset.mem_range.1 hi)
  have hs : ∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i =
      -(y ^ f.natDegree) := by linear_combination hfy
  rw [hs, Valuation.map_neg, map_pow] at hlt
  exact lt_irrefl _ hlt

end GlobalTheory.Nef.PlaceResiduePowerBound

namespace GlobalTheory.Nef

open WithZero

theorem place_res_exists_pow : ∀ (k F E : Type) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E],
    (∃ ρ : Place k E → Place k F, IsRes ρ) ∧ ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ p,
      ∃ e : ℕ, 0 < e ∧ (∀ x : F, p.1 (algebraMap F E x) = (ρ p).1 x ^ e) ∧
        ∀ x : F, ord p (algebraMap F E x) = e * ord (ρ p) x := by
  intro k F E _ _ _ _ _ _ _ _
  refine ⟨?_, fun ρ hρ p => ?_⟩
  · have hex : ∀ p : Place k E, ∃ q : Place k F,
        ∀ x, p.1 (algebraMap F E x) ≤ 1 ↔ q.1 x ≤ 1 := by
      intro p
      obtain ⟨a, ha⟩ := PlaceResiduePowerBound.exists_one_lt (F := F) p.1 p.2.1
      obtain ⟨q, hq, e, he, hpow⟩ := PlaceResiduePowerBound.root (p.1.comap (algebraMap F E)) ⟨a, ha⟩
      refine ⟨⟨q, hq, fun c hc => ?_⟩, fun x => ?_⟩
      · apply PlaceResiduePowerBound.pow_inj he.ne'
        rw [← hpow, Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, p.2.2 c hc, one_pow]
      · have h := hpow x
        rw [Valuation.comap_apply] at h
        rw [h, PlaceResiduePowerBound.pow_le_one_iff' he.ne']
    choose ρ hρ using hex
    exact ⟨ρ, hρ⟩
  · obtain ⟨e, he, hpow⟩ :=
      PlaceResiduePowerBound.pow_of_iff (p.1.comap (algebraMap F E)) (ρ p).1 (ρ p).2.1 (fun x => hρ p x)
    refine ⟨e, he, fun x => hpow x, fun x => ?_⟩
    have h : p.1 (algebraMap F E x) = (ρ p).1 x ^ e := hpow x
    unfold ord
    rw [h, log_pow, nsmul_eq_mul]
    ring

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceSumOrderEqFinrank
section
set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.FundId

variable {k F : Type} [Field k] [Field F] [Algebra k F]

noncomputable def toRing (v : Place k F) : GroundTheory.FunctionField.Place k F where
  ring := v.1.valuationSubring
  ne_top := by
    intro h
    obtain ⟨x, hx⟩ := v.2.1 (WithZero.exp 1)
    have hm : x ∈ v.1.valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hm
    omega
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (v.2.2 c hc).le

theorem valuation_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) :
    (toRing v).valuation = v.1 := by
  refine GroundTheory.FunctionField.valuation_eq_of_isEquiv ?_ (toRing v).valuation_surjective v.2.1
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [GroundTheory.FunctionField.Place.valuation_le_one_iff]
  rfl

theorem ord_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) (x : F) :
    (toRing v).ord x = ord v x := by
  unfold ord
  rw [← valuation_toRing]
  rfl

theorem toRing_injective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Injective (toRing : Place k F → _) := fun v w h =>
  Subtype.ext (by rw [← valuation_toRing, ← valuation_toRing, h])

theorem toRing_surjective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Surjective (toRing : Place k F → _) := by
  intro w
  refine ⟨⟨w.valuation, w.valuation_surjective, fun c hc => ?_⟩, ?_⟩
  · exact w.valuation_algebraMap' hc
  · ext x
    exact w.valuation_le_one_iff x

theorem deg_eq_one [IsAlgClosed k] [GroundTheory.FunctionField.IsFunctionField k F]
    (w : GroundTheory.FunctionField.Place k F) : w.deg = 1 := by
  have h : Function.Bijective (algebraMap k w.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have e : k ≃ₗ[k] w.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap k w.ResidueField) h
  have := e.finrank_eq
  rw [Module.finrank_self] at this
  exact this.symm

theorem sum_ord_eq_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (v : Place k F) (π : F), π ≠ 0 → ord v π = 1 → {p | ρ p = v}.Finite ∧ ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E π) = Module.finrank F E := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hF ρ hρ v π _ hπ
  classical
  haveI : GroundTheory.FunctionField.IsFunctionField k F := ⟨hF⟩
  haveI : GroundTheory.FunctionField.IsFunctionField k E :=
    GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional (k := k) (K := F)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have key : ∀ p : Place k E, ρ p = v ↔ (toRing p).LiesOver (toRing v) := by
    intro p
    have h1 : (toRing p).LiesOver (toRing (ρ p)) := by
      ext x
      exact hρ p x
    constructor
    · rintro rfl; exact h1
    · intro h
      exact toRing_injective (GroundTheory.FunctionField.Place.ext (h1.symm.trans h))
  have hfin := (toRing v).finite_liesOver (K' := E)
  have hfin' : {p | ρ p = v}.Finite := by
    refine (hfin.preimage toRing_injective.injOn).subset fun p hp => (key p).1 hp
  refine ⟨hfin', ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', ← (toRing v).sum_ramificationIdx_mul_inertiaDeg (K' := E),
    Nat.cast_sum]
  refine Finset.sum_bij (fun p _ => toRing p) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [key] using hp
  · intro p _ q _ h
    exact toRing_injective h
  · intro w hw
    obtain ⟨p, rfl⟩ := toRing_surjective w
    exact ⟨p, by simpa [key] using hw, rfl⟩
  · intro p hp
    have h : (toRing p).LiesOver (toRing v) := by simpa [key] using hp
    rw [← ord_toRing, h.ord_algebraMap, ord_toRing, hπ, GroundTheory.FunctionField.Place.inertiaDeg,
      deg_eq_one, deg_eq_one]
    simp

end GlobalTheory.Nef.FundId
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreCompatibility
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_compatibility : ∀ (T O A A₁ R R₁ : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R] [CommRing R₁] [Algebra A₁ R₁]
    (j : A →+* A₁) (i₁ : A₁ →+* T), Function.Injective j → Function.Injective i₁ →
    ∀ (jA : R →+* O) (jA₁ : R₁ →+* O) (γ : R →+* R₁)
      (ψA : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib T O),
    jA₁.comp (algebraMap A₁ R₁) = (algebraMap T O).comp i₁ →
    γ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp j →
    jA₁.comp γ = jA →
    ψA.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∃ (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O)
      (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
      ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ ∧
      ψA₁.comp β = ψA ∧
      β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := by
  first | (exact @GlobalTheory.GenFibBaseChange.exists_genFib_maps) | (exact GlobalTheory.GenFibBaseChange.exists_genFib_maps) | (intros; apply GlobalTheory.GenFibBaseChange.exists_genFib_maps  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLIsCharacter
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.HCChar

theorem gal_id_apply {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem hc_isChar : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsChar ℂ ℂ α → IsChar ℂ ℂ β → IsChar ℂ ℂ (hc a b α β n) := by
  intro F _ _ a b n hn α β hα hβ
  obtain ⟨H, π, hH, -, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  haveI : Finite (GL (Fin n) F) := inferInstance
  have h1 : IsChar ℂ ℂ (fun p : H => α (π p).1) := by
    obtain ⟨m, ρ, hρ⟩ := hα
    exact ⟨m, ρ.comp ((MonoidHom.fst _ _).comp π), fun p => hρ _⟩
  have h2 : IsChar ℂ ℂ (fun p : H => β (π p).2) := by
    obtain ⟨m, ρ, hρ⟩ := hβ
    exact ⟨m, ρ.comp ((MonoidHom.snd _ _).comp π), fun p => hρ _⟩
  have hψ : IsChar ℂ ℂ ((fun p : H => α (π p).1) * (fun p : H => β (π p).2)) := isChar_mul_complex h1 h2
  have hind := isChar_ind ℂ ℂ (GL (Fin n) F) H _ hψ
  convert hind using 1
  funext x
  have hcard : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) = (Nat.card H : ℂ) := by
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => (hH x).symm))
  unfold hc hcTw ind
  rw [hcard]
  congr 1
  apply finsum_congr
  intro y
  rw [gal_id_apply]
  unfold ext0
  by_cases hy : y⁻¹ * x * y ∈ H
  · rw [dif_pos hy, if_pos ((hH _).1 hy), Pi.mul_apply, hπ]
  · rw [dif_neg hy, if_neg (fun e => hy ((hH _).2 e))]

end GlobalTheory.Shin.HCChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompactOpenPiStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaussIntegralCompactOpen_pi : ∀ (Y : Type) [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (_ : Good Y) (μ : Measure Y) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (f : ι → Y → ℂ) (γ : ι → ℂ), (∀ i, HasGauss μ (f i) (γ i)) → HasGauss (Measure.pi fun _ : ι => μ) (fun x => ∏ i, f i (x i)) (∏ i, γ i) := by
  first | exact @GlobalTheory.KSp.hasGauss_pi | exact GlobalTheory.KSp.hasGauss_pi | (intros; apply GlobalTheory.KSp.hasGauss_pi <;> assumption)
end

