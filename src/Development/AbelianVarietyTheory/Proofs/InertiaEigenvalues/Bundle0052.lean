import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommonEigenvectorCommuting
section
open scoped BigOperators

namespace GlobalTheory.CommTriang

theorem exists_common_eigenvector_commuting {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : ι → Module.End k V) (hc : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ → (∀ i, ∀ w ∈ W, f i w ∈ W) →
      ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : k, f i x = c • x := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | (apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target ..)

theorem exists_common_eigenvector : ∀ (k ι : Type) [Field k] [IsAlgClosed k] (n : ℕ)
    (T : ι → Matrix (Fin (n+1)) (Fin (n+1)) k), (∀ i j, T i * T j = T j * T i) →
    ∃ v : Fin (n+1) → k, v ≠ 0 ∧ ∃ χ : ι → k, ∀ i, (T i).mulVec v = χ i • v := by
  intro k ι _ _ n T hT
  have hc : ∀ i j, Matrix.toLin' (T i) * Matrix.toLin' (T j) = Matrix.toLin' (T j) * Matrix.toLin' (T i) := by
    intro i j
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hT]
  obtain ⟨x, -, hx0, hx⟩ := exists_common_eigenvector_commuting (fun i => Matrix.toLin' (T i)) hc _ ⊤ rfl
    (by simp) (fun _ _ _ => Submodule.mem_top)
  choose χ hχ using hx
  exact ⟨x, hx0, χ, fun i => by simpa using hχ i⟩

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

theorem exists_unit_col_zero : ∀ (k : Type) [Field k] (n : ℕ) (v : Fin (n+1) → k), v ≠ 0 →
    ∃ P : Matrix (Fin (n+1)) (Fin (n+1)) k, IsUnit P ∧ ∀ a, P a 0 = v a := by
  first
  | exact @_root_.GlobalTheory.IntegralCriterion.main
  | exact _root_.GlobalTheory.IntegralCriterion.main
  | (apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralCriterion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralCriterion.main ..)

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

theorem lift_eigen : ∀ (k ι V : Type) [Field k] [AddCommGroup V] [Module k V] (f : ι → Module.End k V) (v u : V) (χ μ r : ι → k),
    (∀ i j, f i * f j = f j * f i) → v ≠ 0 → (∀ t : k, u + t • v ≠ 0) → (∀ i, f i v = χ i • v) →
    (∀ i, f i u = μ i • u + r i • v) → ∃ x : V, x ≠ 0 ∧ ∀ i, f i x = μ i • x := by
  intro k ι V _ _ _ f v u χ μ r hc hv0 hu0 hv hu
  by_cases h : ∀ i, χ i = μ i
  · exact ⟨v, hv0, fun i => by rw [hv, h]⟩
  push_neg at h
  obtain ⟨i₀, hi₀⟩ := h
  have hd : μ i₀ - χ i₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hi₀)
  set t : k := r i₀ / (μ i₀ - χ i₀) with ht
  have htd : t * (μ i₀ - χ i₀) = r i₀ := div_mul_cancel₀ _ hd
  have hfx : ∀ j, f j (u + t • v) = μ j • (u + t • v) + (r j + t * χ j - t * μ j) • v := by
    intro j
    rw [map_add, map_smul, hu, hv]
    module
  have h0 : f i₀ (u + t • v) = μ i₀ • (u + t • v) := by
    rw [hfx]
    have : r i₀ + t * χ i₀ - t * μ i₀ = 0 := by rw [← htd]; ring
    rw [this, zero_smul, add_zero]
  obtain ⟨x, hx⟩ : ∃ x, x = u + t • v := ⟨_, rfl⟩
  rw [← hx] at hfx h0
  refine ⟨x, hx ▸ hu0 t, fun j => ?_⟩
  have e1 : f i₀ (f j x) = f j (f i₀ x) := by
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
  rw [h0, map_smul, hfx j, map_add, map_smul, map_smul, h0, hv] at e1
  have e2 : ((r j + t * χ j - t * μ j) * (χ i₀ - μ i₀)) • v = 0 := by
    linear_combination (norm := module) e1
  rcases smul_eq_zero.mp e2 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rw [hfx j, h, zero_smul, add_zero]
    · exact absurd (sub_eq_zero.mp h) hi₀
  · exact absurd h hv0

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

open Matrix

def blockOne {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n+1)) (Fin (n+1)) k :=
  Matrix.of fun a b => Fin.cases (motive := fun _ => k) (Fin.cases (motive := fun _ => k) 1 (fun _ => 0) b)
    (fun a' => Fin.cases (motive := fun _ => k) 0 (fun b' => Q a' b') b) a

section
variable {k : Type} [Field k] {n : ℕ}

@[simp] theorem blockOne_zero_zero (Q : Matrix (Fin n) (Fin n) k) : blockOne Q 0 0 = 1 := rfl
@[simp] theorem blockOne_zero_succ (Q : Matrix (Fin n) (Fin n) k) (b : Fin n) : blockOne Q 0 b.succ = 0 := rfl
@[simp] theorem blockOne_succ_zero (Q : Matrix (Fin n) (Fin n) k) (a : Fin n) : blockOne Q a.succ 0 = 0 := rfl
@[simp] theorem blockOne_succ_succ (Q : Matrix (Fin n) (Fin n) k) (a b : Fin n) : blockOne Q a.succ b.succ = Q a b := rfl

theorem blockOne_mul (Q R : Matrix (Fin n) (Fin n) k) : blockOne Q * blockOne R = blockOne (Q * R) := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockOne_one : blockOne (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Matrix.one_apply, Fin.succ_ne_zero] <;> exact (Fin.succ_ne_zero _).symm

theorem conj_succ_succ (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a b : Fin n) :
    (blockOne R * S * blockOne Q) a.succ b.succ = (R * S.submatrix Fin.succ Fin.succ * Q) a b := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem conj_succ_zero (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a : Fin n) :
    (blockOne R * S * blockOne Q) a.succ 0 = ∑ c, R a c * S c.succ 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem conj_zero_zero (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) :
    (blockOne R * S * blockOne Q) 0 0 = S 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

end

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang
open Matrix

theorem isUnit_blockOne {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) (hQ : IsUnit Q) :
    IsUnit (blockOne Q) ∧ (blockOne Q)⁻¹ = blockOne Q⁻¹ := by
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have h : blockOne Q * blockOne Q⁻¹ = 1 := by
    rw [blockOne_mul, Matrix.mul_nonsing_inv _ hQd, blockOne_one]
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h), Matrix.inv_eq_right_inv h⟩

theorem exists_triangular (k ι : Type) [Field k] [IsAlgClosed k] : ∀ (n : ℕ) (T : ι → Matrix (Fin n) (Fin n) k),
    (∀ i j, T i * T j = T j * T i) →
    ∃ P : Matrix (Fin n) (Fin n) k, IsUnit P ∧ (∀ i, (P⁻¹ * T i * P).BlockTriangular id) ∧
      ∀ a, ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, (T i).mulVec x = (P⁻¹ * T i * P) a a • x := by
  intro n
  induction n with
  | zero => intro T _; exact ⟨1, isUnit_one, fun i a b _ => a.elim0, fun a => a.elim0⟩
  | succ n ih =>
    intro T hT
    obtain ⟨v, hv0, χ, hv⟩ := exists_common_eigenvector k ι n T hT
    obtain ⟨P₀, hP₀, hP₀v⟩ := exists_unit_col_zero k n v hv0
    have hP₀d : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det P₀).mp hP₀
    have hl : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hP₀d
    have hr : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP₀d
    set S : ι → Matrix (Fin (n+1)) (Fin (n+1)) k := fun i => P₀⁻¹ * T i * P₀ with hSdef
    have hST : ∀ i, P₀ * S i = T i * P₀ := by
      intro i; simp only [hSdef, ← Matrix.mul_assoc, hr, Matrix.one_mul]
    have hSc : ∀ i j, S i * S j = S j * S i := by
      intro i j
      have e : ∀ i j, S i * S j = P₀⁻¹ * (T i * T j) * P₀ := by
        intro i j
        simp only [hSdef, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P₀ P₀⁻¹, hr, Matrix.one_mul]
      rw [e, e, hT]
    set e0 : Fin (n+1) → k := Pi.single 0 1 with he0
    have hPe : P₀.mulVec e0 = v := by
      ext a; simp [he0, Matrix.mulVec, dotProduct, Pi.single_apply, hP₀v]
    have hSe : ∀ i, (S i).mulVec e0 = χ i • e0 := by
      intro i
      have : P₀⁻¹.mulVec v = e0 := by rw [← hPe, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
      simp only [hSdef]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPe, hv, Matrix.mulVec_smul, this]
    have hScol : ∀ i a, S i a 0 = χ i * e0 a := by
      intro i a
      have := congrFun (hSe i) a
      simpa [he0, Matrix.mulVec, dotProduct, Pi.single_apply] using this
    have hS0 : ∀ i (a : Fin n), S i a.succ 0 = 0 := by
      intro i a; rw [hScol]; simp [he0, Fin.succ_ne_zero]
    have hS00 : ∀ i, S i 0 0 = χ i := by
      intro i; rw [hScol]; simp [he0]
    set B : ι → Matrix (Fin n) (Fin n) k := fun i => (S i).submatrix Fin.succ Fin.succ with hBdef
    have hBc : ∀ i j, B i * B j = B j * B i := by
      intro i j; ext a b
      have := congrFun (congrFun (hSc i j) a.succ) b.succ
      simpa [hBdef, Matrix.mul_apply, Fin.sum_univ_succ, hS0] using this
    obtain ⟨Q, hQ, hQtri, hQev⟩ := ih B hBc
    obtain ⟨hDQ, hDQinv⟩ := isUnit_blockOne Q hQ
    refine ⟨P₀ * blockOne Q, hP₀.mul hDQ, ?_⟩
    have hM : ∀ i, (P₀ * blockOne Q)⁻¹ * T i * (P₀ * blockOne Q) = blockOne Q⁻¹ * S i * blockOne Q := by
      intro i
      rw [Matrix.mul_inv_rev, hDQinv]
      simp only [hSdef, Matrix.mul_assoc]
    refine ⟨?_, ?_⟩
    · intro i a b hab
      rw [hM]
      cases a using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ a =>
        cases b using Fin.cases with
        | zero => rw [conj_succ_zero]; simp [hS0]
        | succ b =>
          rw [conj_succ_succ]
          exact hQtri i (by simpa using hab)
    · intro a
      cases a using Fin.cases with
      | zero =>
        refine ⟨v, hv0, fun i => ?_⟩
        rw [hM, conj_zero_zero, hS00, hv]
      | succ a =>
        obtain ⟨y, hy0, hy⟩ := hQev a
        set μ : ι → k := fun i => (Q⁻¹ * B i * Q) a a with hμ
        set u : Fin (n+1) → k := Fin.cons 0 y with hu
        obtain ⟨x', hx'0, hx'⟩ := lift_eigen k ι (Fin (n+1) → k) (fun i => Matrix.toLin' (S i)) e0 u χ μ
          (fun i => ∑ b, S i 0 b.succ * y b)
          (by intro i j; rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hSc])
          (by simp [he0])
          (by
            intro t h
            obtain ⟨b, hb⟩ := Function.ne_iff.mp hy0
            have := congrFun h b.succ
            simp [hu, he0, Fin.succ_ne_zero] at this
            exact hb this)
          (fun i => by simpa using hSe i)
          (by
            intro i
            ext c
            cases c using Fin.cases with
            | zero => simp [hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
            | succ c =>
              have hyi : (B i).mulVec y = μ i • y := hy i
              have := congrFun hyi c
              simp only [hBdef, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, smul_eq_mul] at this
              simp [hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hS0, Fin.succ_ne_zero, this])
        refine ⟨P₀.mulVec x', ?_, fun i => ?_⟩
        · intro h
          apply hx'0
          apply (Matrix.mulVec_injective_iff_isUnit.mpr hP₀)
          rw [h, Matrix.mulVec_zero]
        · have hx := hx' i
          simp only [Matrix.toLin'_apply] at hx
          rw [hM, conj_succ_succ, Matrix.mulVec_mulVec, ← hST, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang
open Matrix

end GlobalTheory.CommTriang
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstOfLvlInvariant
section
noncomputable section

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr.LvlInv

theorem aeval_eq_zero_of_complex {N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {R : Type} [CommRing R] {t : R} (ht : Polynomial.aeval t (Polynomial.cyclotomic N ℤ) = 0)
    (f : Polynomial ℤ) (hf : Polynomial.aeval ζ f = 0) : Polynomial.aeval t f = 0 := by
  have h := minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hN) hf
  rw [← Polynomial.cyclotomic_eq_minpoly hζ hN] at h
  obtain ⟨q, rfl⟩ := h
  rw [map_mul, ht, zero_mul]

theorem exists_geom_int {w : ℂ} {n : ℕ} (h : w ^ n = 1) :
    ∃ c : ℤ, ∑ a ∈ Finset.range n, w ^ a = c := by
  by_cases hw : w = 1
  · exact ⟨n, by simp [hw]⟩
  · refine ⟨0, ?_⟩
    have := geom_sum_mul w n
    rw [h, sub_self] at this
    simpa using (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hw)

theorem exists_sum_int {l k : ℕ} (hl : 0 < l) {w : ℂ} (h : w ^ l ^ (k + 1) = 1) :
    ∃ c : ℤ, ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a), w ^ a = c := by
  obtain ⟨c, hc⟩ := exists_geom_int h
  obtain ⟨d, hd⟩ := exists_geom_int (w := w ^ l) (n := l ^ k) (by rw [← pow_mul, ← pow_succ', h])
  refine ⟨c - d, ?_⟩
  have e := Finset.sum_filter_add_sum_filter_not (Finset.range (l ^ (k + 1))) (fun a => l ∣ a)
    (fun a => w ^ a)
  have e2 : ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => l ∣ a), w ^ a =
      ∑ a ∈ Finset.range (l ^ k), (w ^ l) ^ a := by
    symm
    refine Finset.sum_bij (fun a _ => l * a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_range, Finset.mem_filter] at ha ⊢
      exact ⟨by rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_left ha hl, dvd_mul_right _ _⟩
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hl hab
    · intro b hb
      simp only [Finset.mem_range, Finset.mem_filter] at hb
      obtain ⟨h1, a, rfl⟩ := hb
      refine ⟨a, ?_, rfl⟩
      rw [pow_succ'] at h1
      exact Finset.mem_range.2 (Nat.lt_of_mul_lt_mul_left h1)
    · intro a _
      rw [pow_mul]
  rw [e2, hc, hd] at e
  push_cast
  linear_combination e

theorem aeval_cyc {l : ℕ} (hl : l.Prime) (k : ℕ) {R : Type} [CommRing R] (t : R) :
    Polynomial.aeval t (Polynomial.cyclotomic (l ^ (k + 1)) ℤ) =
      ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i := by
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl]
  simp

theorem root_pow {l : ℕ} (hl : l.Prime) (k : ℕ) {R : Type} [CommRing R] {t : R}
    (ht : ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i = 0) {a : ℕ} (ha : ¬ l ∣ a) :
    ∑ i ∈ Finset.range l, ((t ^ a) ^ l ^ k) ^ i = 0 := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.pos _
  have hζ := Complex.isPrimitiveRoot_exp _ hN.ne'
  rw [← aeval_cyc hl] at ht ⊢
  have h := aeval_eq_zero_of_complex hN hζ ht
    ((Polynomial.cyclotomic (l ^ (k + 1)) ℤ).comp (Polynomial.X ^ a)) (by
      have h2 := hζ.pow_of_coprime a
        (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hl).2 ha).symm)
      have h3 := h2.isRoot_cyclotomic hN
      rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact h3)
  rwa [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X] at h

theorem sum_pow_int {l : ℕ} (hl : l.Prime) (k : ℕ) {R : Type} [CommRing R] {t : R}
    (ht : ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i = 0) (j : ℕ) :
    ∃ c : ℤ, ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a), (t ^ a) ^ j = c := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.pos _
  have hζ := Complex.isPrimitiveRoot_exp _ hN.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (l ^ (k + 1) : ℕ))
  obtain ⟨c, hc⟩ := exists_sum_int (k := k) hl.pos (w := ζ ^ j)
    (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
  rw [← aeval_cyc hl] at ht
  have h := aeval_eq_zero_of_complex hN hζ ht
    (∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a), (Polynomial.X ^ j) ^ a
      - (c : Polynomial ℤ)) (by
      simp only [map_sub, map_sum, map_pow, Polynomial.aeval_X, map_intCast, hc, sub_self])
  simp only [map_sub, map_sum, map_pow, Polynomial.aeval_X, map_intCast, sub_eq_zero] at h
  refine ⟨c, ?_⟩
  rw [← h]
  exact Finset.sum_congr rfl fun a _ => by rw [← pow_mul, ← pow_mul, mul_comm]

theorem sum_aeval_const {l : ℕ} (hl : l.Prime) (k : ℕ) {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] {t : R} (ht : ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i = 0) (s : Polynomial O) :
    ∃ c : O, ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a),
      Polynomial.aeval (t ^ a) s = algebraMap O R c := by
  induction s using Polynomial.induction_on' with
  | add r s hr hs =>
    obtain ⟨c, hc⟩ := hr
    obtain ⟨d, hd⟩ := hs
    exact ⟨c + d, by simp only [map_add, Finset.sum_add_distrib, hc, hd]⟩
  | monomial j x =>
    obtain ⟨c, hc⟩ := sum_pow_int hl k ht j
    refine ⟨x * c, ?_⟩
    simp only [Polynomial.aeval_monomial, ← Finset.mul_sum, hc, map_mul, map_intCast]

def lvlPoly (l : ℕ) (O : Type) [CommRing O] (k : ℕ) : Polynomial O :=
  ∑ i ∈ Finset.range l, ((1 + Polynomial.X : Polynomial O) ^ l ^ k) ^ i

theorem coe_lvlPoly (l : ℕ) (O : Type) [CommRing O] (k : ℕ) :
    ((lvlPoly l O k : Polynomial O) : O⟦X⟧) = lvl l O k := by
  have := map_sum (Polynomial.coeToPowerSeries.ringHom (R := O))
    (fun i => ((1 + Polynomial.X : Polynomial O) ^ l ^ k) ^ i) (Finset.range l)
  simp only [map_pow, map_add, map_one, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X] at this
  exact this

theorem algHom_lvl (l : ℕ) {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (k : ℕ)
    (f : O⟦X⟧ →ₐ[O] R) : f (lvl l O k) = ∑ i ∈ Finset.range l, (f (1 + X) ^ l ^ k) ^ i := by
  simp only [lvl, map_sum, map_pow]

theorem lvlPoly_monic {l : ℕ} (hl : l.Prime) (O : Type) [CommRing O] [Nontrivial O] (k : ℕ) :
    (lvlPoly l O k).Monic := by
  have : lvlPoly l O k =
      (Polynomial.cyclotomic (l ^ (k + 1)) O).comp (Polynomial.X + Polynomial.C 1) := by
    rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl, lvlPoly]
    simp [Polynomial.sum_comp, add_comm]
  rw [this]
  exact (Polynomial.cyclotomic.monic _ _).comp_X_add_C _

theorem lvlPoly_map (l : ℕ) {O F : Type} [CommRing O] [CommRing F] (j : O →+* F) (k : ℕ) :
    (lvlPoly l O k).map j = lvlPoly l F k := by
  simp [lvlPoly, Polynomial.map_sum]

theorem lvlPoly_of_char {l : ℕ} [Fact l.Prime] {F : Type} [CommRing F] [IsDomain F]
    (h : (l : F) = 0) (k : ℕ) : lvlPoly l F k = Polynomial.X ^ (l ^ k * (l - 1)) := by
  have hl : l.Prime := Fact.out
  haveI : CharP F l := (CharP.charP_iff_prime_eq_zero hl).2 h
  have e := geom_sum_mul ((1 + Polynomial.X : Polynomial F) ^ l ^ k) l
  rw [← pow_mul, ← pow_succ] at e
  change lvlPoly l F k * _ = _ at e
  rw [add_pow_char_pow, add_pow_char_pow, one_pow, one_pow, add_sub_cancel_left,
    add_sub_cancel_left] at e
  apply mul_right_cancel₀ (pow_ne_zero (l ^ k) Polynomial.X_ne_zero)
  rw [e, ← pow_add]
  congr 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne_zero
  simp [pow_succ, mul_add]

theorem lvlPoly_distinguished {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    (h : ¬ IsUnit (l : O)) (k : ℕ) :
    (lvlPoly l O k).IsDistinguishedAt (IsLocalRing.maximalIdeal O) := by
  have hm := lvlPoly_monic (l := l) Fact.out O k
  refine ⟨⟨fun {n} hn => ?_⟩, hm⟩
  have h0 : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact h
  have h1 := lvlPoly_map l (IsLocalRing.residue O) k
  rw [lvlPoly_of_char h0] at h1
  have h2 := hm.natDegree_map (IsLocalRing.residue O)
  rw [h1, Polynomial.natDegree_X_pow] at h2
  have h3 := congrArg (fun p => Polynomial.coeff p n) h1
  rw [← h2] at hn
  simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow, hn.ne, if_false] at h3
  exact (IsLocalRing.residue_eq_zero_iff _).1 h3

end GlobalTheory.CycFr.LvlInv

namespace GlobalTheory.CycFr

open LvlInv

theorem exists_const_of_lvl_invariant {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O]
    [Algebra ℤ_[l] O] (hu : ¬ IsUnit (l : O)) (k : ℕ) (b : O⟦X⟧)
    (hb : ∀ a : ℕ, ¬ l ∣ a → lvl l O k ∣ act O (a : ℤ_[l]) b - b) :
    ∃ c : O, lvl l O k ∣ b - C c := by
  have hl : l.Prime := Fact.out
  have H := lvlPoly_distinguished hu k
  set π := Ideal.Quotient.mkₐ O (Ideal.span {lvl l O k}) with hπ
  have hz : ∀ x, π x = 0 ↔ lvl l O k ∣ x := fun x => by
    rw [hπ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have ht : ∑ i ∈ Finset.range l, ((π (1 + X)) ^ l ^ k) ^ i = 0 := by
    rw [← algHom_lvl]
    exact (hz _).2 dvd_rfl
  obtain ⟨r, hr, q, hq⟩ := GlobalTheory.NB.LT.exists_poly_mod H b
  rw [coe_lvlPoly] at hq
  have hbr : b = r + lvl l O k * q := by rw [← hq]; ring
  obtain ⟨c, hc⟩ := sum_aeval_const hl k ht (r.comp (Polynomial.X - 1))
  set S := (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a) with hS
  have h1 : ∀ a ∈ S, Polynomial.aeval ((π (1 + X)) ^ a) (r.comp (Polynomial.X - 1)) = π r := by
    intro a ha
    have ha' : ¬ l ∣ a := (Finset.mem_filter.1 ha).2
    have e1 : π (act O (a : ℤ_[l]) (lvl l O k)) = 0 := by
      have := root_pow hl k ht ha'
      rw [← AlgHom.comp_apply, algHom_lvl, AlgHom.comp_apply, act_one_add_X, bin_nat, map_pow]
      exact this
    have e2 := (hz _).2 (hb a ha')
    rw [hbr] at e2
    simp only [map_sub, map_add, map_mul, e1, (hz _).2 dvd_rfl, zero_mul, add_zero,
      sub_eq_zero] at e2
    rw [← e2, GlobalTheory.NB.LT.algHom_coe, act_nat_X, ← Polynomial.aeval_algHom_apply,
      Polynomial.aeval_comp]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const] at hc
  have hn : S.card ≠ 0 := Finset.card_ne_zero.2 ⟨1, Finset.mem_filter.2
    ⟨Finset.mem_range.2 (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt), hl.not_dvd_one⟩⟩
  set p := lvlPoly l O k with hp
  have h6 : (p : O⟦X⟧) ∣
      ((Polynomial.C (S.card : O) * r - Polynomial.C c : Polynomial O) : O⟦X⟧) := by
    rw [hp, coe_lvlPoly, ← hz, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_C, map_natCast, map_sub, map_mul, map_natCast, algHom_C, ← hc, nsmul_eq_mul,
      sub_self]
  have h7 := GlobalTheory.NB.LT.poly_dvd_of_dvd H h6
  by_cases h0 : r = 0
  · exact ⟨0, q, by simpa [h0] using hq⟩
  have hpos : 0 < p.degree := (Polynomial.zero_le_degree_iff.2 h0).trans_lt hr
  have hn' : (S.card : O) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h8 : Polynomial.C (S.card : O) * r - Polynomial.C c = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt h7 ?_
    refine (Polynomial.degree_sub_le _ _).trans_lt (max_lt ?_ (Polynomial.degree_C_le.trans_lt hpos))
    rwa [Polynomial.degree_C_mul hn']
  have h9 : r.degree ≤ 0 := by
    rw [← Polynomial.degree_C_mul (p := r) hn', sub_eq_zero.1 h8]
    exact Polynomial.degree_C_le
  refine ⟨r.coeff 0, q, ?_⟩
  rw [Polynomial.eq_C_of_degree_le_zero h9, Polynomial.coe_C] at hq
  exact hq

end GlobalTheory.CycFr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCosetRepresentativesOfFiniteSubgroupPadicIStatement
section
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coset_reps_finite_subgroup_padicInt_units : ∀ {l : ℕ} [Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ], l ≠ 2 → ∃ (e : ℕ) (a : Fin e → ℕ), e * Nat.card Δ = l - 1 ∧ (∀ τ, ¬ l ∣ a τ) ∧ (∀ τ τ', τ ≠ τ' → (a τ : ZMod l) ^ Nat.card Δ ≠ (a τ' : ZMod l) ^ Nat.card Δ) ∧ ∀ x : ZMod l, x ≠ 0 → ∃! p : Fin e × Δ, x = (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) := by
  first | exact @GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units | exact GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units | (intros; apply GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenvectorHasSumAdicCompleteFrobeniusStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by
  first | exact @GlobalTheory.abssum_eigen_lim | exact GlobalTheory.abssum_eigen_lim | (intros; apply GlobalTheory.abssum_eigen_lim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivDvrFgModuleStructureStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_dvr_fg_module_structure : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M], ∃ (n m : ℕ) (e : Fin m → ℕ), Nonempty (M ≃ₗ[O] (Fin n → O) × ((i : Fin m) → O ⧸ IsLocalRing.maximalIdeal O ^ e i)) := by
  first | exact @GlobalTheory.dvr_fg_module_structure | exact GlobalTheory.dvr_fg_module_structure | (intros; apply GlobalTheory.dvr_fg_module_structure <;> assumption)
end

