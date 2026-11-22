import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGHatIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial

noncomputable section

theorem pderiv_comm_two_variables (i j : Fin 2) (P : MvPolynomial (Fin 2) ℝ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    simp only [pderiv_mul, map_add, hp, pderiv_X, Pi.single_apply]
    split_ifs <;> (try simp) <;> ring

theorem hasDerivAt_eval_fst (P : MvPolynomial (Fin 2) ℝ) (s t : ℝ) :
    HasDerivAt (fun u => eval ![u, t] P) (eval ![s, t] (pderiv 0 P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const s a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasDerivAt (fun u : ℝ => (![u, t] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 0 (X n))) s := by
      fin_cases n
      · simpa using hasDerivAt_id' s
      · simpa using hasDerivAt_const s t
    simp only [map_mul, eval_X, pderiv_mul, map_add]
    exact hp.mul hX

theorem hasDerivAt_eval_snd (P : MvPolynomial (Fin 2) ℝ) (s t : ℝ) :
    HasDerivAt (fun u => eval ![s, u] P) (eval ![s, t] (pderiv 1 P)) t := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasDerivAt (fun u : ℝ => (![s, u] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 1 (X n))) t := by
      fin_cases n
      · simpa using hasDerivAt_const t s
      · simpa using hasDerivAt_id' t
    simp only [map_mul, eval_X, pderiv_mul, map_add]
    exact hp.mul hX

theorem continuous_eval_fst (P : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    Continuous fun u => eval ![u, t] P :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_fst P u t).continuousAt

theorem continuous_eval_snd (P : MvPolynomial (Fin 2) ℝ) (s : ℝ) :
    Continuous fun u => eval ![s, u] P :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_snd P s u).continuousAt

theorem integral_eval_pderiv_fst (P : MvPolynomial (Fin 2) ℝ) (t a b : ℝ) :
    ∫ u in a..b, eval ![u, t] (pderiv 0 P) = eval ![b, t] P - eval ![a, t] P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_fst P u t)
    ((continuous_eval_fst _ t).intervalIntegrable a b)

theorem integral_eval_pderiv_snd (P : MvPolynomial (Fin 2) ℝ) (s a b : ℝ) :
    ∫ u in a..b, eval ![s, u] (pderiv 1 P) = eval ![s, b] P - eval ![s, a] P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_snd P s u)
    ((continuous_eval_snd _ s).intervalIntegrable a b)

theorem gKernel_eval_diag (k : ℕ) (c : ℝ) : eval ![c, c] (gKernel ℝ k) = 0 := by
  unfold gKernel
  simp only [map_sum, map_sub, map_mul, map_pow, eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j < k := Finset.mem_range.1 hj
  have h : 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * j + (2 * k - 2 * j) := by omega
  rw [← pow_add, ← pow_add, h, sub_self]

theorem GHatIdentity.proof (h0 : GKernelIdentity.Statement) : GHatIdentity.Statement := by
  intro k
  obtain ⟨-, -, h11, hmm, h1m, hm1, hc⟩ := h0 ℝ k
  set G := gKernel ℝ k with hGdef
  have hg : gMixed k = pderiv 0 (pderiv 1 G) := rfl
  have hg' : gMixed k = pderiv 1 (pderiv 0 G) := by rw [hg, pderiv_comm_two_variables]
  have hI1 : ∀ t : ℝ, ∫ x in (-1 : ℝ)..1, eval ![x, t] (gMixed k) =
      eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G) := fun t => by
    rw [hg]; exact integral_eval_pderiv_fst _ _ _ _
  have hI2 : ∀ s : ℝ, ∫ y in (-1 : ℝ)..1, eval ![s, y] (gMixed k) =
      eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G) := fun s => by
    rw [hg']; exact integral_eval_pderiv_snd _ _ _ _
  have hsq : squareMean (gMixed k) = k := by
    unfold squareMean
    simp only [hI2]
    rw [intervalIntegral.integral_sub ((continuous_eval_fst _ _).intervalIntegrable _ _)
      ((continuous_eval_fst _ _).intervalIntegrable _ _), integral_eval_pderiv_fst,
      integral_eval_pderiv_fst, h11, hmm, h1m, hm1]
    ring
  refine ⟨hsq, fun c => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := hc c
  have hdiag := gKernel_eval_diag k c
  rw [← hGdef] at hdiag
  unfold doublyCentred
  simp only [hI1, hI2, hsq]
  have hin : ∀ s : ℝ, ∫ t in (-1 : ℝ)..c,
      (eval ![s, t] (gMixed k) - 1 / 2 * (eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G)) -
        1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) + (k : ℝ)) =
      (eval ![s, c] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) -
        1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G)) -
        (c + 1) * (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k) := by
    intro s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => eval ![s, t] (pderiv 0 G) - 1 / 2 * (eval ![1, t] G - eval ![-1, t] G) -
        (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k) * t)]
    · ring
    · intro t _
      have := ((hasDerivAt_eval_snd (pderiv 0 G) s t).sub
        (((hasDerivAt_eval_snd G 1 t).sub (hasDerivAt_eval_snd G (-1) t)).const_mul (1 / 2))).sub
        ((hasDerivAt_id t).const_mul
          (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k))
      convert this using 1
      · funext u; simp only [Pi.sub_apply, id]
      · rw [hg']; ring
    · exact (((continuous_eval_snd _ s).sub (continuous_const.mul
        ((continuous_eval_snd _ 1).sub (continuous_eval_snd _ (-1))))).sub
        continuous_const |>.add continuous_const).intervalIntegrable _ _
  simp only [hin]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => eval ![s, c] G - eval ![s, -1] G -
      1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G)) * s -
      (c + 1) * (1 / 2 * (eval ![s, 1] G - eval ![s, -1] G) - k * s))]
  · linear_combination (1 / 2 : ℝ) * e1 + (1 / 2 : ℝ) * e2 - (1 / 2 : ℝ) * e3 - (1 / 2 : ℝ) * e4 +
      hdiag + (1 + c) / 2 * h1m - c * hmm + (1 + c) / 2 * hm1
  · intro s _
    have := (((hasDerivAt_eval_fst G s c).sub (hasDerivAt_eval_fst G s (-1))).sub
      ((hasDerivAt_id s).const_mul
        (1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G))))).sub
      ((((hasDerivAt_eval_fst G s 1).sub (hasDerivAt_eval_fst G s (-1))).const_mul (1 / 2)).sub
        ((hasDerivAt_id s).const_mul (k : ℝ)) |>.const_mul (c + 1))
    convert this using 1
    · funext u
      simp only [Pi.sub_apply, id]
    · ring
  · exact ((((continuous_eval_fst _ c).sub (continuous_eval_fst _ (-1))).sub continuous_const).sub
      (continuous_const.mul ((continuous_const.mul ((continuous_eval_fst _ 1).sub
        (continuous_eval_fst _ (-1)))).sub continuous_const))).intervalIntegrable _ _

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGKernelIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

def kernelSum {S : Type*} [CommRing S] (a b : S) (k : ℕ) : S :=
  ∑ j ∈ range k, (a ^ (2 * j + 1) * b ^ (2 * k - 1 - 2 * j) - a ^ (2 * j) * b ^ (2 * k - 2 * j))

section kernelSum

variable {S : Type*} [CommRing S]

theorem kernelSum_zero (a b : S) : kernelSum a b 0 = 0 := by
  simp [kernelSum]

theorem kernelSum_succ (a b : S) (k : ℕ) :
    kernelSum a b (k + 1) =
      b ^ 2 * kernelSum a b k + (a ^ (2 * k + 1) * b - a ^ (2 * k) * b ^ 2) := by
  unfold kernelSum
  rw [sum_range_succ, mul_sum]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    have hj : j < k := mem_range.mp hj
    rw [show 2 * (k + 1) - 1 - 2 * j = (2 * k - 1 - 2 * j) + 2 by omega,
      show 2 * (k + 1) - 2 * j = (2 * k - 2 * j) + 2 by omega, pow_add, pow_add]
    ring
  · rw [show 2 * (k + 1) - 1 - 2 * k = 1 by omega, show 2 * (k + 1) - 2 * k = 2 by omega, pow_one]

theorem add_mul_kernelSum (a b : S) (k : ℕ) :
    (a + b) * kernelSum a b k = b * (a ^ (2 * k) - b ^ (2 * k)) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, show 2 * (k + 1) = 2 * k + 2 by ring]
    linear_combination b ^ 2 * ih

theorem map_kernelSum {T : Type*} [CommRing T] (φ : S →+* T) (a b : S) (k : ℕ) :
    φ (kernelSum a b k) = kernelSum (φ a) (φ b) k := by
  simp [kernelSum, map_sum, map_sub, map_mul, map_pow]

theorem kernelSum_one_one (k : ℕ) : kernelSum (1 : S) 1 k = 0 := by
  simp [kernelSum]

theorem neg_one_pow_two_mul (k : ℕ) : (-1 : S) ^ (2 * k) = 1 := by
  rw [pow_mul]
  simp

theorem kernelSum_neg_one_neg_one (k : ℕ) : kernelSum (-1 : S) (-1) k = 0 := by
  induction k with
  | zero => exact kernelSum_zero _ _
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    ring

theorem kernelSum_one_neg_one (k : ℕ) : kernelSum (1 : S) (-1) k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih]
    push_cast
    ring

theorem kernelSum_neg_one_one (k : ℕ) : kernelSum (-1 : S) 1 k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    push_cast
    ring

end kernelSum

theorem gKernel_eq_kernelSum (R : Type*) [CommRing R] (k : ℕ) :
    gKernel R k = kernelSum (X 0 : MvPolynomial (Fin 2) R) (X 1) k := rfl

theorem eval_gKernel {R : Type*} [CommRing R] (k : ℕ) (a b : R) :
    eval ![a, b] (gKernel R k) = kernelSum a b k := by
  rw [gKernel_eq_kernelSum, map_kernelSum]
  simp

theorem gKernel_isHomogeneous (R : Type*) [CommRing R] (k : ℕ) :
    (gKernel R k).IsHomogeneous (2 * k) := by
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj : j < k := mem_range.mp hj
  refine IsHomogeneous.sub ?_ ?_
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j + 1)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 1 - 2 * j))
    rwa [show 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * k by omega] at h
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 2 * j))
    rwa [show 2 * j + (2 * k - 2 * j) = 2 * k by omega] at h

theorem GKernelIdentity.proof : GKernelIdentity.Statement := by
  intro R _ k
  refine ⟨?_, gKernel_isHomogeneous R k, ?_, ?_, ?_, ?_, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [gKernel_eq_kernelSum, add_mul_kernelSum]
  · rw [eval_gKernel, kernelSum_one_one]
  · rw [eval_gKernel, kernelSum_neg_one_neg_one]
  · rw [eval_gKernel, kernelSum_one_neg_one]
  · rw [eval_gKernel, kernelSum_neg_one_one]
  · have h := add_mul_kernelSum c (-1 : R) k
    rw [eval_gKernel, mul_comm]
    rw [neg_pow, pow_mul] at h
    rw [show c + -1 = c - 1 by ring] at h
    rw [h, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (-1 : R) c k
    rw [eval_gKernel, mul_comm, show c - 1 = -1 + c by ring, h, pow_mul, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (1 : R) c k
    rw [eval_gKernel, mul_comm, h]
    simp
  · have h := add_mul_kernelSum c (1 : R) k
    rw [eval_gKernel, mul_comm, h]
    simp

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGramSumOfMinors
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Finset
open scoped ComplexConjugate Matrix

noncomputable section

theorem orderEmbOfFin_map_castLEEmb {l N : ℕ} (hl : l ≤ N)
    (h : ((univ : Finset (Fin l)).map (Fin.castLEEmb hl)).card = l) :
    (((univ : Finset (Fin l)).map (Fin.castLEEmb hl)).orderEmbOfFin h : Fin l → Fin N) =
      Fin.castLE hl := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    exact Finset.mem_map.mpr ⟨x, mem_univ x, rfl⟩
  · intro a b hab
    exact hab

theorem sum_sq_norm_pluckerCoord_eq_det_mul_conjTranspose (h0 : PluckerFrameChange.Statement)
    {l N : ℕ} (V : Matrix (Fin l) (Fin N) ℂ) :
    (((∑ I ∈ powersetCard l (univ : Finset (Fin N)), ‖pluckerCoord V I‖ ^ 2 : ℝ)) : ℂ) =
      (V * Vᴴ).det := by
  by_cases hl : l ≤ N
  · let g : Matrix (Fin N) (Fin N) ℂ :=
      Matrix.of fun k j => if h : j.val < l then star (V ⟨j.val, h⟩ k) else 0
    let I0 : Finset (Fin N) := (univ : Finset (Fin l)).map (Fin.castLEEmb hl)
    have hI0 : I0.card = l := by simp [I0]
    have hemb := orderEmbOfFin_map_castLEEmb hl hI0
    have key := h0 ℂ l N V g I0 hI0
    have lhs : pluckerCoord (V * g) I0 = (V * Vᴴ).det := by
      unfold pluckerCoord
      rw [dif_pos hI0]
      congr 1
      ext i j
      simp [I0, Matrix.mul_apply, hemb, g, Matrix.conjTranspose_apply]
    have rhs : ∀ J ∈ powersetCard l (univ : Finset (Fin N)),
        pluckerCoord V J * minorOn g l J I0 = ((‖pluckerCoord V J‖ ^ 2 : ℝ) : ℂ) := by
      intro J hJ
      have hJc : J.card = l := (mem_powersetCard.mp hJ).2
      have hm : minorOn g l J I0 = star (pluckerCoord V J) := by
        unfold minorOn pluckerCoord
        rw [dif_pos ⟨hJc, hI0⟩, dif_pos hJc, ← Matrix.det_conjTranspose]
        congr 1
        ext i j
        simp [I0, hemb, g, Matrix.conjTranspose_apply]
      rw [hm, Complex.star_def, RCLike.mul_conj]
      push_cast
      rfl
    rw [← lhs, key, Complex.ofReal_sum]
    exact (sum_congr rfl rhs).symm
  · rw [not_le] at hl
    have hE : powersetCard l (univ : Finset (Fin N)) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using hl)
    rw [hE, sum_empty, Complex.ofReal_zero, eq_comm]
    by_contra hd
    have hu : IsUnit (V * Vᴴ) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := (Matrix.rank_mul_le_left V Vᴴ).trans (Matrix.rank_le_width V)
    simp only [Fintype.card_fin] at h1
    omega

theorem GramSumOfMinors.proof (h0 : PluckerFrameChange.Statement) : GramSumOfMinors.Statement := by
  intro l N V
  have hg := sum_sq_norm_pluckerCoord_eq_det_mul_conjTranspose h0 V
  refine ⟨hg, fun hd => ?_⟩
  have hS : (0 : ℝ) ≤ ∑ I ∈ powersetCard l (univ : Finset (Fin N)), ‖pluckerCoord V I‖ ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  rw [← Finset.sum_div, ← hg, Complex.norm_real, Real.norm_of_nonneg hS]
  apply div_self
  intro hz
  apply hd
  rw [← hg, hz, Complex.ofReal_zero]

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PLineQuotientDeterminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped InnerProductSpace ComplexConjugate

theorem LineQuotientDeterminant.proof : LineQuotientDeterminant.Statement := by
  intro E _ _ _ S hS e he he0 f
  have hne : (0 : ℝ) < ‖e‖ := norm_pos_iff.mpr he0

  have hdet : (Matrix.gram ℂ ![e, f]).det.re = ‖e‖ ^ 2 * ‖f‖ ^ 2 - ‖⟪e, f⟫_ℂ‖ ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← inner_conj_symm e f, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      mul_comm (conj _), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp [Complex.sub_re, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    exact norm_inner_symm f e

  have hee : ⟪e, e⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr he0
  set c : ℂ := ⟪e, f⟫_ℂ / ⟪e, e⟫_ℂ with hc
  set h : E := f - c • e with hh
  have hce : c * ⟪e, e⟫_ℂ = ⟪e, f⟫_ℂ := by
    rw [hc]
    field_simp
  have horth : ⟪e, h⟫_ℂ = 0 := by
    rw [hh, inner_sub_right, inner_smul_right, hce, sub_self]
  have hpyth : ∀ d : ℂ, ‖h + d • e‖ ^ 2 = ‖h‖ ^ 2 + ‖d • e‖ ^ 2 := by
    intro d
    have h0 : ⟪h, d • e⟫_ℂ = 0 := by
      rw [inner_smul_right, inner_eq_zero_symm.mp horth, mul_zero]
    simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) h (d • e) h0
  have hf : f = h + c • e := by rw [hh, sub_add_cancel]
  have hnc : ‖c‖ * ‖e‖ ^ 2 = ‖⟪e, f⟫_ℂ‖ := by
    rw [← hce, norm_mul, inner_self_eq_norm_sq_to_K]
    simp
  have hdet' : (Matrix.gram ℂ ![e, f]).det.re = (‖e‖ * ‖h‖) ^ 2 := by
    have hf2 : ‖f‖ ^ 2 = ‖h‖ ^ 2 + (‖c‖ * ‖e‖) ^ 2 := by
      rw [hf, hpyth c, norm_smul]
    rw [hdet, hf2, ← hnc]
    ring

  have hspan : ∀ s ∈ S, ∃ d : ℂ, d • e = s := by
    intro s hs
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : S)
      (by simpa using he0)).mp hS ⟨s, hs⟩
    exact ⟨d, by simpa using congrArg Subtype.val hd⟩

  have hmk : (Submodule.Quotient.mk h : E ⧸ S) = Submodule.Quotient.mk f := by
    rw [Submodule.Quotient.eq, hh, sub_sub_cancel_left]
    exact S.neg_mem (S.smul_mem c he)
  have hq : ‖(Submodule.Quotient.mk f : E ⧸ S)‖ = ‖h‖ := by
    apply le_antisymm
    · rw [← hmk]
      exact Submodule.Quotient.norm_mk_le S h
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨m, hm, hmε⟩ := Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk f : E ⧸ S) hε
      rw [← hmk, Submodule.Quotient.eq] at hm
      obtain ⟨d, hd⟩ := hspan _ hm
      have hm' : m = h + d • e := by rw [hd, add_sub_cancel]
      have : ‖h‖ ^ 2 ≤ ‖m‖ ^ 2 := by
        rw [hm', hpyth d]
        nlinarith [sq_nonneg ‖d • e‖]
      have : ‖h‖ ≤ ‖m‖ := by
        nlinarith [norm_nonneg h, norm_nonneg m]
      linarith
  rw [hdet', hq, Real.sqrt_sq (by positivity)]

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PMixedCoefficient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial

theorem MixedCoefficient.proof : MixedCoefficient.Statement := by
  intro S _ G A₁ A₂ v₁ v₂ h₁ h₂
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add] at hp hq ⊢
    rw [hp, hq]; ring
  | mul_X p i hp =>
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Derivation.leibniz, pderiv_X_self, smul_eq_mul,
        map_add, map_mul, eval_X, Matrix.cons_val_zero, mul_one] at hp ⊢
      have e : pderiv (1 : Fin 2) (X (0 : Fin 2) : MvPolynomial (Fin 2) S) = 0 :=
        pderiv_X_of_ne (by decide)
      rw [e]
      simp only [map_zero, mul_zero, zero_add]
      rw [hp]
      linear_combination (eval ![A₁, A₂] (pderiv 0 p) - v₂ * eval ![A₁, A₂] (pderiv 0 (pderiv 1 p))) * h₁
    · simp only [Fin.mk_one, Fin.isValue, Derivation.leibniz, pderiv_X_self, smul_eq_mul,
        map_add, map_mul, eval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one] at hp ⊢
      have e : pderiv (0 : Fin 2) (X (1 : Fin 2) : MvPolynomial (Fin 2) S) = 0 :=
        pderiv_X_of_ne (by decide)
      rw [e]
      simp only [map_zero, mul_zero, zero_add, add_zero]
      rw [hp]
      linear_combination (eval ![A₁, A₂] (pderiv 1 p) - v₁ * eval ![A₁, A₂] (pderiv 0 (pderiv 1 p))) * h₂

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.POmitStepPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial

theorem OmitStepPolynomial.proof : OmitStepPolynomial.Statement := by
  intro R _ σ _ p
  refine ⟨((renameEquiv R (Equiv.optionSubtypeNe p).symm).trans
      (optionEquivLeft R {q // q ≠ p})).toRingEquiv, ?_, ?_, ?_⟩
  · simp [optionEquivLeft_X_none]
  · intro q
    simp [Equiv.optionSubtypeNe_symm_of_ne q.property, optionEquivLeft_X_some]
  · intro r
    simp [optionEquivLeft_C]

end GroundTheory.Heights₂.Heights.FlagBundles
end

