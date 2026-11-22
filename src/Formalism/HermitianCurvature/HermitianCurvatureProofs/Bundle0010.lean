import Formalism.HermitianCurvature.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0006
import Formalism.HermitianCurvature.LevelRecursionCondNeeded

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondKernelPropertyKernel
section
namespace Formalism.FourierDecayAlt.P.LastBlockReversal

theorem blk_last (l : List ℕ) : Formalism.DoubleCosetMeasures.blk (l ++ [1]) l.sum = l.length := by
  induction l with
  | nil => simp [Formalism.DoubleCosetMeasures.blk]
  | cons a l ih =>
    simp only [List.cons_append, List.sum_cons, List.length_cons, Formalism.DoubleCosetMeasures.blk]
    rw [if_neg (by omega), Nat.add_sub_cancel_left, ih]
    omega

theorem revIn_last (l : List ℕ) : Formalism.DoubleCosetMeasures.revIn (l ++ [1]) l.sum = l.sum := by
  induction l with
  | nil => simp [Formalism.DoubleCosetMeasures.revIn]
  | cons a l ih =>
    simp only [List.cons_append, List.sum_cons, Formalism.DoubleCosetMeasures.revIn]
    rw [if_neg (by omega), Nat.add_sub_cancel_left, ih]

end Formalism.FourierDecayAlt.P.LastBlockReversal

namespace Formalism.FourierDecayAlt.P.LastBlockReversalIndices

open Formalism.DoubleCosetMeasures MeasureTheory

theorem entry {K : Type} [CommRing K] {n : ℕ} (N : Fin n) (hN : N.val + 1 = n)
    (V W U : Matrix (Fin n) (Fin n) K) (hV : IsLowUni V) (hU : IsUpUni U) :
    (V * W * U)⁻¹ N N = W⁻¹ N N := by
  have hU' := isUpUni_inv K hU
  have hV' := isLowUni_inv K hV
  have hlast : ∀ i : Fin n, i ≤ N := fun i => by
    have := i.2
    rw [Fin.le_def]
    omega
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_apply, Finset.sum_eq_single N]
  · rw [Matrix.mul_apply, Finset.sum_eq_single N]
    · rw [hU'.2 N, hV'.2 N, one_mul, mul_one]
    · intro j _ hj
      rw [hV'.1 (show OrderDual.toDual N < OrderDual.toDual j from (lt_of_le_of_ne (hlast j) hj : j < N)),
        mul_zero]
    · simp
  · intro i _ hi
    rw [hU'.1 (lt_of_le_of_ne (hlast i) hi), zero_mul]
  · simp

theorem lam_last {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (N : Fin n) (hN : N.val + 1 = n)
    (Z : Matrix (Fin n) (Fin n) K) :
    lamLin R Z (eLast R) = Submodule.Quotient.mk (Z⁻¹ N N) := by
  have hv : coeLin R (eLast R) = Pi.single N (1 : K) := by
    ext j
    simp only [coeLin, eLast, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Algebra.linearMap_apply, Pi.single_apply]
    by_cases h : j = N
    · subst h
      simp [hN]
    · have h' : ¬ (j.val + 1 = n) := fun e => h (Fin.ext (by omega))
      simp [h', h]
  have hlc : ∀ v : Fin n → K, lastCoord R v = v N := by
    intro v
    simp only [lastCoord, LinearMap.sum_apply]
    rw [Finset.sum_eq_single N]
    · simp [hN]
    · intro j _ hj
      have h' : ¬ (j.val + 1 = n) := fun e => hj (Fin.ext (by omega))
      simp [h']
    · simp
  simp only [lamLin, LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply, hv, hlc]
  congr 1
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem a2one_of
    (hW : ∀ (K : Type) [CommRing K] (l : List ℕ) (t : ℕ → Kˣ) (N : Fin (l ++ [1]).sum),
      N.val + 1 = (l ++ [1]).sum → (pt (l ++ [1]) t)⁻¹ N N = (((t l.length)⁻¹ : Kˣ) : K)) :
    Formalism.FourierDecayAlt.A.LevelOneKernelPoint := by
  intro K _ _ _ R l t ψ C _ _ e lam μ₁ μ₂ hB
  obtain ⟨p, hp⟩ : ∃ p, phi R (l ++ [1]) t ψ C e lam p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hB
    unfold BB
    rw [show phi R (l ++ [1]) t ψ C e lam = fun _ => 0 from funext hcon]
    simp
  unfold phi at hp
  have h1 := left_ne_zero_of_mul hp
  split_ifs at h1 with hI
  · have h2 : Nat.card (isoSet R ((((p.1 : GL (Fin (l ++ [1]).sum) K)) :
        Matrix (Fin (l ++ [1]).sum) (Fin (l ++ [1]).sum) K) * pt (l ++ [1]) t *
        ((p.2 : GL (Fin (l ++ [1]).sum) K) : Matrix (Fin (l ++ [1]).sum) (Fin (l ++ [1]).sum) K))
        C e lam) ≠ 0 := by exact_mod_cast h1
    obtain ⟨⟨φ, hφ1, hφ2⟩⟩ := (Nat.card_ne_zero.mp h2).1
    have hN : ((⟨l.sum, by simp⟩ : Fin (l ++ [1]).sum) : ℕ) + 1 = (l ++ [1]).sum := by simp
    rw [← hφ1, eZ, hφ2, lam_last R ⟨l.sum, by simp⟩ hN, entry _ hN _ _ _ p.1.2.1 p.2.2,
      hW K l t _ hN]
  · exact absurd rfl h1

end Formalism.FourierDecayAlt.P.LastBlockReversalIndices

namespace Formalism.FourierDecayAlt.P.ReversedIndexLastBlock

open Formalism.DoubleCosetMeasures

theorem revIn_lt : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s j < s.sum
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [revIn]
    split_ifs with hj
    · simp; omega
    · have := revIn_lt s (j - a) (by simp at h; omega)
      simp; omega

theorem revIn_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s (revIn s j) = j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    by_cases hj : j < a
    · have h2 : a - 1 - j < a := by omega
      simp only [revIn, hj, if_true, h2]; omega
    · have h2 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [revIn, hj, if_false, h2]
      rw [Nat.add_sub_cancel_left, revIn_revIn s (j - a) (by simp at h; omega)]; omega

theorem blk_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    by_cases hj : j < a
    · have h2 : a - 1 - j < a := by omega
      simp only [revIn, blk, hj, if_true, h2]
    · have h2 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [revIn, blk, hj, if_false, h2]
      rw [Nat.add_sub_cancel_left, blk_revIn s (j - a) (by simp at h; omega)]

theorem pt_mul {K : Type} [CommRing K] (s : List ℕ) (t : ℕ → Kˣ) :
    pt s t * pt s (fun b => (t b)⁻¹) = (1 : Matrix (Fin s.sum) (Fin s.sum) K) := by
  ext a c
  simp only [Matrix.mul_apply, pt]
  rw [Finset.sum_eq_single ⟨revIn s a, revIn_lt s a a.2⟩]
  · rw [if_pos rfl]
    simp only [Fin.val_mk]
    rw [revIn_revIn s a a.2, blk_revIn s a a.2, Matrix.one_apply]
    by_cases h : c = a
    · subst h
      simp
    · have h' : (c : ℕ) ≠ a := fun e => h (Fin.ext e)
      simp [h', Ne.symm h]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro e
    exact hb (Fin.ext e)
  · simp

theorem pt_inv_last {K : Type} [CommRing K] (l : List ℕ) (t : ℕ → Kˣ) (N : Fin (l ++ [1]).sum)
    (hN : N.val + 1 = (l ++ [1]).sum) : (pt (l ++ [1]) t)⁻¹ N N = (((t l.length)⁻¹ : Kˣ) : K) := by
  rw [Matrix.inv_eq_right_inv (pt_mul _ t)]
  have hN' : (N : ℕ) = l.sum := by
    simp at hN
    omega
  simp only [pt]
  rw [hN', Formalism.FourierDecayAlt.P.LastBlockReversal.revIn_last, if_pos rfl, Formalism.FourierDecayAlt.P.LastBlockReversal.blk_last]

theorem a2one : Formalism.FourierDecayAlt.A.LevelOneKernelPoint :=
  Formalism.FourierDecayAlt.P.LastBlockReversalIndices.a2one_of (fun _ _ l t N hN => pt_inv_last l t N hN)

theorem a2oneKernel : Formalism.FourierDecayAlt.A.LevelOneKernelPair := by
  intro K _ _ _ R l l' t t' ψ C _ _ e lam m1 m2 m3 m4 h1 h2
  have e1 := a2one K R l t ψ C e lam m1 m2 h1
  have e2 := a2one K R l' t' ψ C e lam m3 m4 h2
  have h3 := e1.symm.trans e2
  rw [Submodule.Quotient.eq] at h3
  obtain ⟨r, hr⟩ := LinearMap.mem_range.mp h3
  rw [← hr]
  exact r.2

end Formalism.FourierDecayAlt.P.ReversedIndexLastBlock

theorem Formalism.FourierDecayAlt.P.second_kernel_property_one : Formalism.FourierDecayAlt.A.LevelOneKernelPoint := Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2one
theorem Formalism.FourierDecayAlt.P.second_kernel_property_kernel : Formalism.FourierDecayAlt.A.LevelOneKernelPair :=
  Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2oneKernel
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothDecayOfWeighted
section
open MeasureTheory Module
open scoped Nat

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def au (j : ℕ) : ℝ := j ! * j ! * 4 ^ j

theorem au_nonneg (j : ℕ) : 0 ≤ au j := by
  unfold au
  positivity

theorem contDiff_u (n : ℕ∞) : ContDiff ℝ n (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).inv (fun y => by positivity)

theorem norm_iteratedFDeriv_w_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * au i * au (n - i)) * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by
  refine (norm_iteratedFDeriv_mul_le (N := (n : ℕ∞)) (contDiff_u n) (contDiff_u n) x le_rfl).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := norm_iteratedFDeriv_u_le (V := V) i x
  have h2 := norm_iteratedFDeriv_u_le (V := V) (n - i) x
  have hq : 0 ≤ (1 + ‖x‖ ^ 2)⁻¹ := by positivity
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x‖
      ≤ (n.choose i : ℝ) * (au i * (1 + ‖x‖ ^ 2)⁻¹) * (au (n - i) * (1 + ‖x‖ ^ 2)⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (au_nonneg i) hq))
    _ = (n.choose i : ℝ) * au i * au (n - i) * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by ring

theorem inv_sq_le (x : V) : (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ ≤ 4 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have ht0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hA : (0 : ℝ) < (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) := by positivity
  have hB : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
  have hr : (1 + ‖x‖) ^ (-(4 : ℝ)) = ((1 + ‖x‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    norm_cast
  have h2 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖x‖)]
  have h3 : ((1 + ‖x‖) ^ 2) ^ 2 ≤ (2 * (1 + ‖x‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  rw [hr, ← mul_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hA hB]
  nlinarith [h3]

theorem decay_of_weight {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ ∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hEb 0 (Nat.zero_le _) 0)
  have hDw : D = fun x => ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) • E x := by
    funext x
    rw [hDE x, smul_smul]
    have hq : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
    field_simp
    simp
  have hwc : ContDiff ℝ m (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) :=
    (contDiff_u m).mul (contDiff_u m)
  refine ⟨hDw ▸ hwc.smul hE, ?_⟩
  set Kw : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * au l * au (i - l) with hKw
  have hKw0 : ∀ i, 0 ≤ Kw i := fun i =>
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (au_nonneg _)) (au_nonneg _)
  set Cn : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Kw i * B with hCn
  have hCn0 : ∀ n, 0 ≤ Cn n := fun n =>
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hKw0 i)) hB
  refine ⟨4 * ∑ n ∈ Finset.range (m + 1), Cn n, fun j hj x => ?_⟩
  have hq0 : 0 ≤ (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ := by positivity
  have hstep : ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by
    rw [hDw]
    refine (norm_iteratedFDeriv_smul_le (N := (j : ℕ∞)) (hwc.of_le (by exact_mod_cast hj))
      (hE.of_le (by exact_mod_cast hj)) x le_rfl).trans ?_
    rw [hCn, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ *
          ‖iteratedFDeriv ℝ (j - i) E x‖
        ≤ (j.choose i : ℝ) * (Kw i * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹)) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_w_le i x) (Nat.cast_nonneg _))
            (hEb (j - i) (by omega) x) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKw0 i) hq0))
      _ = (j.choose i : ℝ) * Kw i * B * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by ring
  have hsum : Cn j ≤ ∑ n ∈ Finset.range (m + 1), Cn n :=
    Finset.single_le_sum (fun n _ => hCn0 n) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  calc ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := hstep
    _ ≤ (∑ n ∈ Finset.range (m + 1), Cn n) * (4 * (1 + ‖x‖) ^ (-(4 : ℝ))) :=
        mul_le_mul hsum (inv_sq_le x) hq0 (Finset.sum_nonneg fun n _ => hCn0 n)
    _ = 4 * (∑ n ∈ Finset.range (m + 1), Cn n) * (1 + ‖x‖) ^ (-(4 : ℝ)) := by ring

theorem smooth_decay_of_weighted [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (hV : finrank ℝ V ≤ 3)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ (∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by
  obtain ⟨hD, C, hC⟩ := decay_of_weight hE B hEb hDE
  refine ⟨hD, ⟨C, hC⟩, fun j hj1 hjm => integral_iteratedFDeriv_eq_zero hD C (fun i hi x => ?_) j hj1 hjm⟩
  refine (hC i hi x).trans ?_
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  gcongr
  · linarith [norm_nonneg x]
  · have : (finrank ℝ V : ℝ) ≤ 3 := by exact_mod_cast hV
    linarith

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDegreePolynomials
section
namespace Formalism.FourierDecayAlt.P.TopDegreePolynomials

open Finset Polynomial Formalism.FourierDecayAlt.F7

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem evR_smul (P : R[X]) (a : ℕ) (ha : P.natDegree ≤ a) (Y : ℝ) (X : M) :
    evR P Y • X = ∑ i ∈ range (a + 1), ((Y : ℂ) ^ i) • (P.coeff i • X) := by
  unfold evR
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le ha), Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow, ← Algebra.commutes, mul_smul, algebraMap_smul]

end

theorem isTop_sub {W W' : ℝ → ℂ} {d : ℕ} {c c' : ℂ} (h : IsTopCoeff W d c)
    (h' : IsTopCoeff W' d c') : IsTopCoeff (fun Y => W Y - W' Y) d (c - c') := by
  obtain ⟨P, hd, hc, hP⟩ := h
  obtain ⟨P', hd', hc', hP'⟩ := h'
  exact ⟨P - P', (natDegree_sub_le_of_le hd hd').trans (by simp), by rw [coeff_sub, hc, hc'],
    fun Y => by simp only [eval_sub, hP, hP']⟩

theorem isTop_const_mul {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (k : ℂ) (h : IsTopCoeff W d c) :
    IsTopCoeff (fun Y => k * W Y) d (k * c) := by
  obtain ⟨P, hd, hc, hP⟩ := h
  exact ⟨C k * P, (natDegree_C_mul_le _ _).trans hd, by rw [coeff_C_mul, hc],
    fun Y => by simp only [eval_mul, eval_C, hP]⟩

theorem natDegree_mono (h : ℂ) (i j : ℕ) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).natDegree = i + j := by
  rw [Monic.natDegree_mul (monic_X_pow i) ((monic_X_add_C h).pow j), natDegree_X_pow,
    Monic.natDegree_pow (monic_X_add_C h), natDegree_X_add_C, mul_one]

theorem coeff_mono (h : ℂ) (a b i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).coeff (a + b) = if i = a ∧ j = b then 1 else 0 := by
  have hm : ((X : ℂ[X]) ^ i * (X + C h) ^ j).Monic := (monic_X_pow i).mul ((monic_X_add_C h).pow j)
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    have := hm.coeff_natDegree
    rwa [natDegree_mono] at this
  · apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_mono]
    omega

end Formalism.FourierDecayAlt.P.TopDegreePolynomials

namespace Formalism.FourierDecayAlt.P

open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.TopDegreePolynomials

theorem pairing_top_degree : Formalism.FourierDecayAlt.F7.PairTop := by
  intro R M _ _ _ _ _ _ Ξ P₁ P₂ a b h X X' ha hb
  refine ⟨∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1),
    C (Ξ (P₁.coeff i • X) (P₂.coeff j • X')) * ((Polynomial.X : ℂ[X]) ^ i *
      (Polynomial.X + C (h : ℂ)) ^ j), ?_, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_mono]
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    omega
  · rw [finsetSum_coeff]
    rw [Finset.sum_eq_single a]
    · rw [finsetSum_coeff, Finset.sum_eq_single b]
      · rw [coeff_C_mul, coeff_mono _ _ _ _ _ le_rfl le_rfl]; simp
      · intro j hj hjb
        rw [coeff_C_mul, coeff_mono _ _ _ _ _ le_rfl (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
        simp [hjb]
      · intro hb'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self b)) hb'
    · intro i hi hia
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [coeff_C_mul, coeff_mono _ _ _ _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
      simp [hia]
    · intro ha'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self a)) ha'
  · intro Y
    simp only []
    rw [evR_smul P₁ a ha, evR_smul P₂ b hb, map_sum Ξ, LinearMap.sum_apply, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul Ξ, LinearMap.smul_apply, map_smulₛₗ]
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, smul_eq_mul, map_pow,
      map_add, Complex.conj_ofReal, Complex.ofReal_add]
    ring

theorem j_pairing_formula : Formalism.FourierDecayAlt.F7.JPairing := by
  intro R M _ _ _ _ _ _ Ξ A B Av Bv s Y Y' X X'
  simp [pair2, act2, vec, Formalism.YangianSpanCharacter.T.J, Formalism.YangianSpanCharacter.T.Uinv, Fin.sum_univ_two, Matrix.mul_apply, add_smul,
    mul_smul, algebraMap_smul]
  ring

theorem plane_wave_top_degree : Formalism.FourierDecayAlt.F7.PlaneWaveTop := by
  intro R M _ _ _ _ _ _ Ξ n A B Av Bv s X X' hS hSv
  obtain ⟨hA, hAn, hB⟩ := hS
  obtain ⟨hAv, hAvn, hBv⟩ := hSv
  have cA : A.coeff n = 1 := by rw [← hAn]; exact hA.coeff_natDegree
  have cAv : Av.coeff n = 1 := by rw [← hAvn]; exact hAv.coeff_natDegree
  have cB : B.coeff n = 0 := coeff_eq_zero_of_degree_lt hB
  have cBv : Bv.coeff n = 0 := coeff_eq_zero_of_degree_lt hBv
  have dB : B.natDegree ≤ n := natDegree_le_of_degree_le hB.le
  have dBv : Bv.natDegree ≤ n := natDegree_le_of_degree_le hBv.le
  have h1 := pairing_top_degree R M Ξ (B + C (algebraMap ℂ R s) * A) Av n n 1 X X'
    (natDegree_add_le_of_degree_le dB ((natDegree_C_mul_le _ _).trans hAn.le)) hAvn.le
  have h2 := pairing_top_degree R M Ξ A Bv n n 1 X X' hAn.le dBv
  have h3 := isTop_sub h1 h2
  rw [two_mul]
  convert h3 using 1
  · funext Y
    rw [j_pairing_formula R M Ξ A B Av Bv s Y (Y + 1) X X']
    simp [evR, eval_add, eval_C_mul]
  · simp [cA, cAv, cB, cBv, algebraMap_smul]

theorem lift_top_degree : Formalism.FourierDecayAlt.F7.LiftTop := by
  intro R M _ _ _ _ _ _ Ξ n s A B Av Bv A₀ A₀v e t t' h X X' _ he ht ht' hA hAn hAv hAvn
    hA₀ hA₀n hA₀v hA₀vn hB hBv
  have cA : A.coeff (n + s) = 1 := by rw [← hAn]; exact hA.coeff_natDegree
  have cAv : Av.coeff (n + s) = 1 := by rw [← hAvn]; exact hAv.coeff_natDegree
  have cA₀ : A₀.coeff n = 1 := by rw [← hA₀n]; exact hA₀.coeff_natDegree
  have cA₀v : A₀v.coeff n = 1 := by rw [← hA₀vn]; exact hA₀v.coeff_natDegree
  have h1 := isTop_const_mul (e * t⁻¹)
    (pairing_top_degree R M Ξ A₀ Av n (n + s) h X X' hA₀n.le hAvn.le)
  have h2 := isTop_const_mul (e * t'⁻¹)
    (pairing_top_degree R M Ξ A A₀v (n + s) n h X X' hAn.le hA₀vn.le)
  have e1 : n + (n + s) = 2 * n + s := by ring
  have e2 : n + s + n = 2 * n + s := by ring
  rw [e1] at h1
  rw [e2] at h2
  have h3 := isTop_sub h1 h2
  have hce : (starRingEnd ℂ) e = e := by
    rcases he with rfl | rfl <;> simp
  convert h3 using 1
  · funext Y
    have := j_pairing_formula R M Ξ A B Av Bv 0 Y (Y + h) X X'
    have hU : Formalism.YangianSpanCharacter.T.Uinv (A := R) (0 : ℂ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.Uinv]
    rw [hU, mul_one] at this
    rw [this, map_zero, zero_mul, add_zero, hB, hBv, map_smul Ξ, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ (Ξ (evR A Y • X))]
    simp [hce]
  · simp [cA, cAv, cA₀, cA₀v]
    ring

end Formalism.FourierDecayAlt.P
end

