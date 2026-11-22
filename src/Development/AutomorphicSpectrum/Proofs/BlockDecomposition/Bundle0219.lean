import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0202
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrETransposeEqPhiSeq
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.GlTranspose

variable {n : ℕ} {A : Type} [Ring A]

theorem epw_zero (e : Fin n → Fin n → A) (a b : Fin n) :
    Epw e 0 a b = if a = b then 1 else 0 := by
  rw [Epw]

theorem epw_succ (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, e a c * Epw e m c b := by
  rw [Epw]

theorem epw_succ_right (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, Epw e m a c * e c b := by
  induction m generalizing a b with
  | zero =>
    simp [epw_succ, epw_zero]
  | succ m ih =>
    calc Epw e (m + 1 + 1) a b = ∑ c, e a c * ∑ d, Epw e m c d * e d b := by
          rw [epw_succ]
          exact sum_congr rfl fun c _ => by rw [ih]
      _ = ∑ d, (∑ c, e a c * Epw e m c d) * e d b := by
          simp only [mul_sum, sum_mul, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ c, Epw e (m + 1) a c * e c b := sum_congr rfl fun d _ => by rw [epw_succ]

theorem bco_zero_zero (N : A) (τ : ℕ → A) : bco N τ 0 0 = 1 := by rw [bco]

theorem bco_zero_succ (N : A) (τ : ℕ → A) (j : ℕ) : bco N τ 0 (j + 1) = 0 := by rw [bco]

theorem bco_succ_zero (N : A) (τ : ℕ → A) (m : ℕ) :
    bco N τ (m + 1) 0 = N * bco N τ m 0 - τ m := by rw [bco]

theorem bco_succ_succ (N : A) (τ : ℕ → A) (m j : ℕ) :
    bco N τ (m + 1) (j + 1) = bco N τ m j + N * bco N τ m (j + 1) := by rw [bco]

theorem bco_eq_zero (N : A) (τ : ℕ → A) (m j : ℕ) (h : m < j) : bco N τ m j = 0 := by
  induction m generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact bco_zero_succ N τ j
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [bco_succ_succ, ih j (by omega), ih (j + 1) (by omega)]
    simp

theorem bco_self (N : A) (τ : ℕ → A) (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => exact bco_zero_zero N τ
  | succ m ih =>
    rw [bco_succ_succ, ih, bco_eq_zero N τ m (m + 1) (by omega)]
    simp

theorem phiSeq_eq (N : A) (τ : ℕ → A) (m : ℕ) :
    phiSeq N τ m = τ m - ∑ j ∈ range m, bco N τ m j * phiSeq N τ j := by
  rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m]

section Gl

variable (e : Fin n → Fin n → A)
  (he : ∀ a b c d, e a b * e c d - e c d * e a b =
    (if b = c then e a d else 0) - (if a = d then e c b else 0))
include he

theorem comm_epw (m : ℕ) (a b c d : Fin n) :
    e a b * Epw e m c d - Epw e m c d * e a b =
      (if b = c then Epw e m a d else 0) - (if a = d then Epw e m c b else 0) := by
  induction m generalizing c d with
  | zero =>
    simp only [epw_zero]
    by_cases h1 : c = d
    · subst h1
      by_cases h2 : b = c
      · subst h2; simp
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h2, h3]
    · by_cases h2 : b = c
      · subst h2
        by_cases h3 : a = d
        · subst h3; simp [h1]
        · simp [h1, h3]
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h1, h2, h3]
  | succ m ih =>
    have step : ∀ f, e a b * (e c f * Epw e m f d) - (e c f * Epw e m f d) * e a b =
        ((if b = c then e a f else 0) - (if a = f then e c b else 0)) * Epw e m f d +
          e c f * ((if b = f then Epw e m a d else 0) - (if a = d then Epw e m f b else 0)) := by
      intro f
      rw [← he a b c f, ← ih f d]
      noncomm_ring
    rw [epw_succ e m c d, mul_sum, sum_mul, ← sum_sub_distrib, sum_congr rfl (fun f _ => step f)]
    simp only [sub_mul, mul_sub, sum_add_distrib, sum_sub_distrib, ite_mul, mul_ite, zero_mul,
      mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : a = d <;>
      simp only [h1, h2, if_true, if_false, ← epw_succ, sum_const_zero] <;> abel

theorem transpose_step (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) b a =
      ∑ c, Epw e m c a * e b c + (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
  have h : Epw e (m + 1) b a - ∑ c, Epw e m c a * e b c =
      (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
    rw [epw_succ, ← sum_sub_distrib,
      sum_congr rfl (fun c _ => comm_epw e he m b c c a), sum_sub_distrib]
    by_cases h1 : a = b
    · subst h1; simp [trE]
    · have h2 : ¬ b = a := fun h => h1 h.symm
      simp [h1, h2]
  rw [add_sub_assoc, ← h]
  abel

theorem transpose_poly (m : ℕ) (a b : Fin n) :
    Epw e m b a =
      ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * Epw (fun a b => e b a) j a b := by
  induction m generalizing a b with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, bco_zero_zero, one_mul, epw_zero]
    simp only [eq_comm]
  | succ m ih =>
    set f : Fin n → Fin n → A := fun a b => e b a with hf
    set N : A := (n : A) with hN
    set τ : ℕ → A := trE e with hτ
    have key : ∑ c, Epw e m c a * e b c =
        ∑ j ∈ range (m + 1), bco N τ m j * Epw f (j + 1) a b := by
      simp only [epw_succ_right f, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun c _ => ?_
      rw [ih a c, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_assoc]
    have hn : N * Epw e m b a =
        ∑ j ∈ range (m + 1), N * bco N τ m (j + 1) * Epw f (j + 1) a b +
          N * bco N τ m 0 * Epw f 0 a b := by
      rw [← sum_range_succ' (fun j => N * bco N τ m j * Epw f j a b) (m + 1),
        sum_range_succ _ (m + 1), bco_eq_zero N τ m (m + 1) (by omega), ih a b, mul_sum]
      simp [mul_assoc]
    rw [transpose_step e he, key, hn, sum_range_succ' _ (m + 1), bco_succ_zero]
    simp only [bco_succ_succ, add_mul, sum_add_distrib, sub_mul, epw_zero f]
    by_cases h1 : a = b
    · simp [h1]
      try abel
    · simp [h1]
      try abel

theorem trE_eq_sum (m : ℕ) :
    trE e m = ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * trE (fun a b => e b a) j := by
  have h : trE e m = ∑ a, Epw e m a a := rfl
  rw [h, sum_congr rfl (fun a _ => transpose_poly e he m a a), sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [trE, mul_sum]

end Gl

theorem trE_transpose_eq_phiSeq (n : ℕ) {A : Type} [Ring A] [Algebra ℂ A]
    (e : Fin n → Fin n → A)
    (he : ∀ a b c d, e a b * e c d - e c d * e a b =
      (if b = c then e a d else 0) - (if a = d then e c b else 0)) (m : ℕ) :
    trE (fun a b => e b a) m = phiSeq (n : A) (trE e) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h := trE_eq_sum e he m
    rw [sum_range_succ, bco_self, one_mul] at h
    have hs : ∑ j ∈ range m, bco (n : A) (trE e) m j * phiSeq (n : A) (trE e) j =
        ∑ j ∈ range m, bco (n : A) (trE e) m j * trE (fun a b => e b a) j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
    rw [phiSeq_eq, hs, h, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.WaveMult.GlTranspose
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementGelfandPolynomialFormula
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GelfRec

open Polynomial Matrix

noncomputable def entrySum {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ[X]) (A : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) : ℂ[X] :=
  ∑ a, ∑ b, (E * (A ^ k).map C) a b

theorem natDegree_adjugate_le (m : ℕ) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (a b : Fin (m + 1)) :
    (adjugate ((X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + B.map C) a b).natDegree
      ≤ m := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  have hs : ((X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + B.map C).submatrix
        b.succAbove a.succAbove =
      (X : ℂ[X]) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove).map C
        + (B.submatrix b.succAbove a.succAbove).map C := by
    rfl
  rw [hs]
  have h1 := natDegree_det_X_add_C_le
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove)
    (B.submatrix b.succAbove a.succAbove)
  rw [Fintype.card_fin] at h1
  refine natDegree_mul_le.trans ?_
  have h2 : ((-1 : ℂ[X]) ^ ((b : ℕ) + (a : ℕ))).natDegree = 0 := by
    rcases neg_one_pow_eq_or ℂ[X] ((b : ℕ) + (a : ℕ)) with h | h <;> simp [h]
  omega

theorem entrySum_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ[X]) (k : ℕ) :
    x * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A k
        + entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A (k + 1)
      = det (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C) * C (∑ a, ∑ b, (A ^ k) a b) := by
  set M := x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C with hM
  set E := adjugate M with hEdef
  have hE : E * M = M.det • (1 : Matrix (Fin n) (Fin n) ℂ[X]) := adjugate_mul M
  have hp : (A ^ (k + 1)).map C = A.map C * (A ^ k).map C := by
    rw [pow_succ']
    exact Matrix.map_mul
  have key : x • (E * (A ^ k).map C) + E * (A ^ (k + 1)).map C = M.det • (A ^ k).map C := by
    have h3 : (E * M) * (A ^ k).map C = M.det • (A ^ k).map C := by
      rw [hE, Matrix.smul_mul, Matrix.one_mul]
    rw [← h3, hp, hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_assoc]
  have h4 := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ[X] => ∑ a, ∑ b, B a b) key
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Matrix.map_apply] at h4
  simp only [entrySum, map_sum]
  exact h4

theorem newton_closed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ[X]) (N : ℕ) :
    x ^ (N + 1) * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A 0
        - det (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)
          * ∑ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)
      = (-1) ^ N * x * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : ∑ k ∈ Finset.range (N + 1), C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k)
        = x * ∑ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)
          + C ((-1 : ℂ) ^ N * ∑ a, ∑ b, (A ^ N) a b) * x := by
      have h1 : ∀ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k)
          = x * (C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)) := by
        intro k hk
        have hk' : k ≤ N := (Finset.mem_range.1 hk).le
        rw [Nat.succ_sub hk', pow_succ]
        ring
      rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, ← Finset.mul_sum]
      simp
    have hstep := entrySum_step A x N
    rw [hs]
    simp only [map_mul, map_pow, map_neg, map_one] at ih hstep ⊢
    linear_combination x * ih + (-1) ^ N * x * hstep

theorem shift_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    (X - C c : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C
      = (X : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ).map C + (A - c • (1 : Matrix (Fin n) (Fin n) ℂ)).map C := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    simp
    ring
  · simp [Matrix.one_apply_ne h]

theorem natDegree_entrySum_le (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c : ℂ) (k : ℕ) :
    (entrySum (adjugate ((X - C c : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X]) + A.map C))
      A k).natDegree ≤ m := by
  rw [shift_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  rw [Matrix.mul_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
  exact (natDegree_mul_C_le _ _).trans (natDegree_adjugate_le m _ a d)

theorem entrySum_zero {n : ℕ} (l : Fin n → ℂ) (x : ℂ[X]) :
    entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C))
        (Formalism.REAL.Amat l) 0
      = ∏ s, (x + C (l s) + 1) - ∏ s, (x + C (l s)) := by
  have hM : x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C
      = (compRingHom x).mapMatrix
        ((X : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C) := by
    refine Matrix.ext fun i j => ?_
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have h0 := congrArg (compRingHom x) (GlobalTheory.CompanionTheory.AdjSum.adj_sum n l)
  simp only [map_sum, map_sub, map_prod, map_add, map_one, coe_compRingHom_apply, X_comp, C_comp] at h0
  rw [← h0, hM, ← RingHom.map_adjugate]
  simp [entrySum]

theorem det_shift (m : ℕ) (χ : Fin (m + 1) → ℂ) :
    det ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
        + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C)
      = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := by
  rw [det_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun s _ => ?_
    have hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ) := by
      rw [← C_sub]
      congr 1
      push_cast
      ring
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.map_apply,
      Formalism.REAL.Amat, Matrix.of_apply, if_true, smul_eq_mul, mul_one]
    rw [hc]
    ring
  · intro i j hij
    have hij' : j < i := hij
    have hne : i ≠ j := ne_of_gt hij'
    simp [Formalism.REAL.Amat, Matrix.one_apply_ne hne, hne, not_lt.2 hij'.le]

theorem prod_monic (m : ℕ) (c : Fin (m + 1) → ℂ) :
    (∏ s, (X + C (c s))).coeff (m + 1) = 1 := by
  have hm : (∏ s, (X + C (c s))).Monic := monic_prod_of_monic _ _ fun s _ => monic_X_add_C _
  have hd : (∏ s, (X + C (c s))).natDegree = m + 1 := by
    rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
    simp
  have h1 := hm.coeff_natDegree
  rwa [hd] at h1

theorem gelfVal_newton : ∀ (m : ℕ) (χ : Fin (m + 1) → ℂ) (N : ℕ), ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).comp (Polynomial.X + 1) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2)))) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) = GlobalTheory.Dec.gelfVal χ N := by
  intro m χ N
  have hdet := det_shift m χ
  have hz := entrySum_zero (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) (X - C (m : ℂ))
  have hc := newton_closed (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N
  have hs := entrySum_step (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N
  have hdeg := natDegree_entrySum_le m (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (m : ℂ) (N + 1)
  have hterm : ∀ s : Fin (m + 1), (X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2)
      = X + C (χ s - (m : ℂ) / 2) := by
    intro s
    have hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ) := by
      rw [← C_sub]
      congr 1
      push_cast
      ring
    rw [hc]
    ring
  have hQ : (∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1)
      = ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) + 1) := by
    rw [prod_comp]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hterm s]
    simp
    ring
  have hP : ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2))
      = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := Finset.prod_congr rfl fun s _ => hterm s
  rw [hP, ← hQ] at hz
  rw [hz, hdet] at hc
  rw [hdet] at hs
  have hsq : (-1 : ℂ[X]) ^ N * (-1) ^ N = 1 := by
    rw [← mul_pow]
    simp
  change _ = ∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) ^ N) a b
  have hgoal : (-1 : ℂ[X]) ^ N * ((X - C (m : ℂ)) ^ (N + 1) * ((∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1) - (∏ s, (X + C (χ s - (m : ℂ) / 2)))) - (∏ s, (X + C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (X - C (m : ℂ)) ^ (N - k))
      = C (∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) ^ N) a b) * (∏ s, (X + C (χ s - (m : ℂ) / 2)))
        - entrySum (adjugate ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
            + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C))
          (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (N + 1) := by
    have hc' := hc
    simp only [GlobalTheory.Dec.gelfVal] at *
    linear_combination (-1 : ℂ[X]) ^ N * hc' + hs + (X - C (m : ℂ)) * entrySum (adjugate ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
            + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C))
          (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) N * hsq
  rw [hgoal, coeff_sub, coeff_C_mul, prod_monic m (fun s => χ s - (m : ℂ) / 2),
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hdeg)]
  simp

end GlobalTheory.CompanionTheory.GelfRec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TranslatedLengthBoundedDerivative
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

variable {n : ℕ}

def lmulCLM (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := mul_add a
      map_smul' := fun r y => by simp }

theorem lmulCLM_apply (a y : Mat n) : lmulCLM a y = a * y := rfl

theorem inv_mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x⁻¹ * y ∈ GLs n := by
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have h1 : IsUnit (x⁻¹).det := Matrix.isUnit_nonsing_inv_det x hxu
  show (x⁻¹ * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h1.ne_zero hy

theorem lg_left_facts : LgFacts → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ GLs n,
    ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧
    (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧
    ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C := by
  intro hL n
  obtain ⟨-, -, -, hsm, hcpt, -, C₀, hC₀⟩ := hL n
  refine ⟨2 * |C₀|, by positivity, fun x hx => ?_⟩
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have hsm' : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) :=
    hsm.comp (lmulCLM x⁻¹).contDiff.contDiffOn (fun y hy => inv_mul_mem_GLs hx hy)
  refine ⟨hsm', fun R => ?_, fun y hy p => ?_⟩
  · have hxU : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hxu
    let X : G n := hxU.unit
    have hXv : (X : Mat n) = x := rfl
    have hXi : ((X⁻¹ : G n) : Mat n) = x⁻¹ := by
      rw [Matrix.coe_units_inv, hXv]
    have hset : {y : G n | lg (x⁻¹ * y.val) ≤ R} = (fun z : G n => X * z) '' {z : G n | lg z.val ≤ R} := by
      ext y
      constructor
      · intro hy
        refine ⟨X⁻¹ * y, ?_, by simp⟩
        show lg ((X⁻¹ * y : G n) : Mat n) ≤ R
        rw [Units.val_mul, hXi]
        exact hy
      · rintro ⟨z, hz, rfl⟩
        show lg (x⁻¹ * ((X * z : G n) : Mat n)) ≤ R
        rw [Units.val_mul, ← hXi, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
        exact hz
    rw [hset]
    exact (hcpt R).image (continuous_const.mul continuous_id)
  · have hw : x⁻¹ * y ∈ GLs n := inv_mul_mem_GLs hx hy
    have hdiff : DifferentiableAt ℝ lg (x⁻¹ * y) :=
      (hsm.contDiffAt (isOpen_GLs.mem_nhds hw)).differentiableAt (by simp)
    have hder : fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y
        = (fderiv ℝ lg (x⁻¹ * y)).comp (lmulCLM x⁻¹) :=
      ((hdiff.hasFDerivAt).comp y (lmulCLM x⁻¹).hasFDerivAt).fderiv
    have hCle : C₀ ≤ |C₀| := le_abs_self C₀
    rw [hder, ContinuousLinearMap.comp_apply, lmulCLM_apply, ← mul_assoc]
    obtain ⟨b, i, j⟩ := p
    have h1 := abs_le.1 (hC₀ _ hw (b, i, j))
    have h2 := abs_le.1 (hC₀ _ hw (b, j, i))
    cases b
    · have e : hm ((false, i, j) : Ix n) = bs (false, i, j) - bs (false, j, i) := by
        simp [hm, bs]
      rw [e, mul_sub, map_sub, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have e : hm ((true, i, j) : Ix n) = bs (true, i, j) + bs (true, j, i) := by
        simp [hm, bs]
      rw [e, mul_add, map_add, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end GlobalTheory.CompanionTheory.WaveSpd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WvAlg
section
namespace GlobalTheory.CompanionTheory.WaveFc

open PositivityTheory.RgBcC.Fc

theorem wvAlg : WvAlg := by
  intro c N t y
  have hsq : ((y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = y := by
    rw [← Complex.cpow_nat_mul]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : Even 2 := ⟨1, rfl⟩
    have h0 : Even 0 := ⟨0, rfl⟩
    simp only [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj, h2, h0, if_true, hsq, pow_zero, one_mul]
    first
      | ring
      | (simp [hsq]; ring_nf)
      | simp [hsq]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · intro j
    simp only [PositivityTheory.RgBcC.Fc.wv]
    rw [pow_succ (1 + y ^ 2) N, mul_inv]
    push_cast
    ring

end GlobalTheory.CompanionTheory.WaveFc
end

