import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0114
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStD
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseChi
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

theorem VeroneseChi.proof (hB : VeroneseMonoBasis.Statement) (hG : VeroneseGramMono.Statement) :
    VeroneseChi.Statement := by
  classical
  intro D _ n
  obtain ⟨bM, hM, hMv⟩ := hB D n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix (Veronese.Idx D)) ℚ), IsSecBasis (Veronese.x D) n p.2 :=
    ⟨⟨_, bM⟩, hM⟩
  unfold Veronese.chi
  rw [dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r', b'⟩ := p
  have hp' : IsSecBasis (Veronese.x D) n b' := hp
  have hr : r' = (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card := hp'.card_eq.trans hM.card_eq.symm
  subst hr
  have hA : ∀ k, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → ℤ,
      ∑ l, c l • aeval (Veronese.x D) (bM l) = aeval (Veronese.x D) (b' k) := fun k =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (by rw [hM.2.2, ← hp'.2.2]; exact Submodule.subset_span ⟨k, rfl⟩)
  have hB' : ∀ l, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → ℤ,
      ∑ m, c m • aeval (Veronese.x D) (b' m) = aeval (Veronese.x D) (bM l) := fun l =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (by rw [hp'.2.2, ← hM.2.2]; exact Submodule.subset_span ⟨l, rfl⟩)
  choose A hA using hA
  choose B hB' using hB'
  have hAB : Matrix.of A * Matrix.of B = 1 := by
    ext k m
    have h1 : ∑ m, (Matrix.of A * Matrix.of B) k m • aeval (Veronese.x D) (b' m) =
        aeval (Veronese.x D) (b' k) := by
      simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hB']
      exact hA k
    have h2 : ∑ m, (1 : Matrix (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card)
        (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ) k m • aeval (Veronese.x D) (b' m) =
        aeval (Veronese.x D) (b' k) := by
      simp [Matrix.one_apply]
    have hli := Fintype.linearIndependent_iff.mp hp'.2.1
      (fun m => (Matrix.of A * Matrix.of B) k m - (1 : Matrix _ _ ℤ) k m)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]) m
    exact sub_eq_zero.mp hli
  have hdet : (Matrix.of A).det ^ 2 = 1 := by
    have hd := congrArg Matrix.det hAB
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact Int.isUnit_sq (isUnit_iff_exists_inv.mpr ⟨_, hd⟩)
  have hGb := hG D n _ b' (Matrix.of A) fun k => by
    rw [← hA k]
    simp only [hMv, zsmul_eq_mul, Matrix.of_apply]
  rw [hGb]
  have hdA : ((Matrix.of A).map (Int.cast : ℤ → ℝ)).det = ((Matrix.of A).det : ℝ) :=
    ((Int.castRingHom ℝ).map_det (Matrix.of A)).symm
  have hdet' : ((Matrix.of A).det : ℝ) ^ 2 = 1 := by exact_mod_cast hdet
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hdA]
  have hprod : ((Matrix.of A).det : ℝ) * (∏ k, monoNormSq (adtEnum D (2 * n) k)) * ((Matrix.of A).det : ℝ) =
      ∏ k, monoNormSq (adtEnum D (2 * n) k) := by
    linear_combination (∏ k, monoNormSq (adtEnum D (2 * n) k)) * hdet'
  rw [hprod, Real.log_prod (fun k _ => (monoNormSq_pos (adtEnum D (2 * n) k)).ne'), chiP,
    sum_adtEnum D (2 * n) (fun a => Real.log (monoNormSq a))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGramMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory
open GroundTheory.Heights₂.Heights.SectionsLatticeFS.L2MonomialOrthogonality

noncomputable section

namespace VeroneseGramMono

variable {D : ℕ}

theorem sum_wt_mul (a : Fin (D + 1) → ℝ) :
    ∑ q : Ix (Veronese.Idx D), Veronese.wt q * (a q.2.1.1 * a q.2.1.2) = (∑ i, a i) ^ 2 := by
  classical
  have hs : ∀ g : Fin (D + 1) × Fin (D + 1) → ℝ,
      ∑ q : Ix (Veronese.Idx D), g q.2.1 = ∑ p, if p.1 ≤ p.2 then g p else 0 := by
    intro g
    rw [Fintype.sum_sigma, Fintype.sum_unique, ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (fun p => by simp) g).symm
  have hw : ∀ q : Ix (Veronese.Idx D), Veronese.wt q = if q.2.1.1 = q.2.1.2 then 1 else 2 := fun q => rfl
  simp only [hw]
  rw [hs (fun p => (if p.1 = p.2 then 1 else 2) * (a p.1 * a p.2)), sq, Finset.sum_mul_sum,
    ← Fintype.sum_prod_type']
  have hswap : ∑ p : Fin (D + 1) × Fin (D + 1), (if p.2 < p.1 then a p.1 * a p.2 else 0) =
      ∑ p : Fin (D + 1) × Fin (D + 1), (if p.1 < p.2 then a p.1 * a p.2 else 0) := by
    rw [← (Equiv.prodComm _ _).sum_comp]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]
  have hsplit : ∑ p : Fin (D + 1) × Fin (D + 1), a p.1 * a p.2 =
      ∑ p : Fin (D + 1) × Fin (D + 1), ((if p.1 ≤ p.2 then a p.1 * a p.2 else 0) +
        (if p.2 < p.1 then a p.1 * a p.2 else 0)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases le_or_gt p.1 p.2 with h | h
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mpr h]
  rw [hsplit, Finset.sum_add_distrib, hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases lt_trichotomy p.1 p.2 with h | h | h
  · simp [h.le, h.ne, h]
    ring
  · simp [h]
  · simp [not_le.mpr h, not_lt.mpr h.le]

theorem rho_map (w : Fin (D + 1) → ℂ) :
    (Veronese.metric D).ρ (Veronese.map D w) = normSq2 w := by
  change ‖WithLp.toLp 2 (Veronese.scale D (Veronese.map D w))‖ = _
  rw [EuclideanSpace.norm_eq]
  have h : ∀ q : Ix (Veronese.Idx D), ‖Veronese.scale D (Veronese.map D w) q‖ ^ 2 =
      Veronese.wt q * (‖w q.2.1.1‖ ^ 2 * ‖w q.2.1.2‖ ^ 2) := fun q => by
    simp only [Veronese.scale, Veronese.map, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Veronese.wt_pos q).le]
  simp only [h]
  rw [sum_wt_mul (fun i => ‖w i‖ ^ 2)]
  exact Real.sqrt_sq (normSq2_nonneg w)

theorem rho_conj_map (w : Fin (D + 1) → ℂ) :
    (Veronese.metric D).ρ (conjPt (Veronese.map D w)) = normSq2 w := by
  have h : conjPt (Veronese.map D w) = Veronese.map D (fun i => starRingEnd ℂ (w i)) := by
    funext q
    simp [conjPt, Veronese.map, map_mul]
  rw [h, rho_map]
  simp [normSq2]

theorem conjPt_map (w : Fin (D + 1) → ℂ) :
    conjPt (Veronese.map D w) = Veronese.map D (fun i => starRingEnd ℂ (w i)) := by
  funext q
  simp [conjPt, Veronese.map, map_mul]

def phi (D : ℕ) : MvPolynomial (Ix (Veronese.Idx D)) ℚ →ₐ[ℚ] MvPolynomial (Fin (D + 1)) ℚ :=
  bind₁ fun q => X q.2.1.1 * X q.2.1.2

theorem aeval_alt (f : MvPolynomial (Ix (Veronese.Idx D)) ℚ) :
    aeval (Veronese.x D) f = algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D) (phi D f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, phi, bind₁_C_right]
    exact congrArg (fun g : ℚ →+* Veronese.Fld D => g a)
      (Subsingleton.elim _ ((algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp C))
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, hp, aeval_X]
    simp [phi, Veronese.x, Veronese.t]

theorem phi_eq {N : ℕ} (b : MvPolynomial (Ix (Veronese.Idx D)) ℚ)
    (c : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℤ)
    (h : aeval (Veronese.x D) b = ∑ l, (c l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D N l i) :
    phi D b = ∑ l, (c l : MvPolynomial (Fin (D + 1)) ℚ) * ∏ i, X i ^ adtEnum D N l i := by
  apply IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)
  rw [← aeval_alt, h]
  simp [map_sum, map_mul, map_prod, map_pow, Veronese.t]

theorem eval_map_phi (w : Fin (D + 1) → ℂ) (f : MvPolynomial (Ix (Veronese.Idx D)) ℚ) :
    eval (Veronese.map D w) (MvPolynomial.map (algebraMap ℚ ℂ) f) = aeval w (phi D f) := by
  rw [phi, aeval_bind₁, eval_map, aeval_def]
  congr 1
  funext q
  simp [Veronese.map]

theorem eval_b {N : ℕ} (w : Fin (D + 1) → ℂ) (b : MvPolynomial (Ix (Veronese.Idx D)) ℚ)
    (c : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℤ)
    (h : aeval (Veronese.x D) b = ∑ l, (c l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D N l i) :
    eval (Veronese.map D w) (MvPolynomial.map (algebraMap ℚ ℂ) b) =
      ∑ l, (c l : ℂ) * ∏ i, w i ^ adtEnum D N l i := by
  rw [eval_map_phi, phi_eq b c h]
  simp [map_sum, map_mul, map_prod, map_pow]

theorem eval_conj_b {N : ℕ} (w : Fin (D + 1) → ℂ) (b : MvPolynomial (Ix (Veronese.Idx D)) ℚ)
    (c : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℤ)
    (h : aeval (Veronese.x D) b = ∑ l, (c l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D N l i) :
    eval (conjPt (Veronese.map D w)) (MvPolynomial.map (algebraMap ℚ ℂ) b) =
      starRingEnd ℂ (∑ l, (c l : ℂ) * ∏ i, w i ^ adtEnum D N l i) := by
  rw [conjPt_map, eval_b _ b c h]
  simp [map_sum, map_mul, map_prod, map_pow]

def ex (D N : ℕ) (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) : Fin (D + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (adtEnum D N l)

theorem ex_degree {N : ℕ} (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) : (ex D N l).degree = N := by
  rw [Finsupp.degree_eq_sum]
  simpa [ex] using adtEnum_sum D N l

theorem eval_ex {N : ℕ} (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) (w : Fin (D + 1) → ℂ) :
    eval w (monomial (ex D N l) (1 : ℂ)) = ∏ i, w i ^ adtEnum D N l i := by
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp [ex]

theorem veroneseMetric_pow_eq (w : Fin (D + 1) → ℂ) (n : ℕ) :
    (Veronese.metric D).ρ (Veronese.map D w) ^ (2 * n) = norm2 w ^ (2 * (2 * n)) := by
  rw [rho_map, pow_mul (norm2 w), norm2, Real.sq_sqrt (normSq2_nonneg w)]

theorem veroneseMetric_conj_pow_eq (w : Fin (D + 1) → ℂ) (n : ℕ) :
    (Veronese.metric D).ρ (conjPt (Veronese.map D w)) ^ (2 * n) = norm2 w ^ (2 * (2 * n)) := by
  rw [rho_conj_map, pow_mul (norm2 w), norm2, Real.sq_sqrt (normSq2_nonneg w)]

variable {n r : ℕ} (b : Fin r → MvPolynomial (Ix (Veronese.Idx D)) ℚ)
  (A : Matrix (Fin r) (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ)
  (hA : ∀ k, aeval (Veronese.x D) (b k) =
    ∑ l, (A k l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D (2 * n) l i)
include hA

theorem pairVal_map (k l : Fin r) (w : Fin (D + 1) → ℂ) :
    pairVal (Veronese.metric D) n (b k) (b l) (Veronese.map D w) =
      ∑ i, ∑ j, ((A k i : ℂ) * (A l j : ℂ)) * monoInner (2 * n) (ex D (2 * n) j) (ex D (2 * n) i) w := by
  unfold pairVal
  rw [veroneseMetric_pow_eq, eval_b w (b k) _ (hA k), eval_b w (b l) _ (hA l)]
  simp only [monoInner, eval_ex]
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_intCast]
  ring

theorem pairVal_conj_map (k l : Fin r) (w : Fin (D + 1) → ℂ) :
    pairVal (Veronese.metric D) n (b k) (b l) (conjPt (Veronese.map D w)) =
      ∑ i, ∑ j, ((A k i : ℂ) * (A l j : ℂ)) * monoInner (2 * n) (ex D (2 * n) i) (ex D (2 * n) j) w := by
  unfold pairVal
  rw [veroneseMetric_conj_pow_eq, eval_conj_b w (b k) _ (hA k), eval_conj_b w (b l) _ (hA l), Complex.conj_conj]
  simp only [monoInner, eval_ex]
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_intCast, map_prod, map_pow]
  ring

omit hA in
theorem integrable_monoInner_ex (i j : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) :
    Integrable (fun p : CP D => monoInner (2 * n) (ex D (2 * n) i) (ex D (2 * n) j) p.rep) (CP.fsMeasure D) :=
  (continuous_monoInner_rep (ex_degree i) (ex_degree j)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit hA in

theorem integral_monoInner_ex (i j : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) :
    ∫ p : CP D, monoInner (2 * n) (ex D (2 * n) i) (ex D (2 * n) j) p.rep ∂CP.fsMeasure D =
      if i = j then ((monoNormSq (adtEnum D (2 * n) i) : ℝ) : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have e := integral_monoInner_self (N := D) (ex D (2 * n) i)
    rw [ex_degree] at e
    rw [e, monoNormSq, adtEnum_sum]
    push_cast
    simp [ex]
  · have hne : ex D (2 * n) i ≠ ex D (2 * n) j := fun e =>
      h (adtEnum_injective D _ (by simpa [ex] using e))
    have e := integral_monoInner_eq_zero hne ((ex_degree j).trans (ex_degree i).symm)
    rwa [ex_degree] at e

theorem integral_pairVal (k l : Fin r) :
    ∫ p : CP D, pairVal (Veronese.metric D) n (b k) (b l) (Veronese.map D p.rep) ∂CP.fsMeasure D =
      ((∑ i, (A k i : ℝ) * monoNormSq (adtEnum D (2 * n) i) * (A l i : ℝ) : ℝ) : ℂ) := by
  have hi : ∀ i j, Integrable (fun p : CP D => ((A k i : ℂ) * (A l j : ℂ)) *
      monoInner (2 * n) (ex D (2 * n) j) (ex D (2 * n) i) p.rep) (CP.fsMeasure D) := fun i j =>
    (integrable_monoInner_ex j i).const_mul _
  simp_rw [pairVal_map b A hA k l]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hi i j]
  simp only [integral_const_mul, integral_monoInner_ex, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  push_cast
  ring

theorem integral_pairVal_conj (k l : Fin r) :
    ∫ p : CP D, pairVal (Veronese.metric D) n (b k) (b l) (conjPt (Veronese.map D p.rep)) ∂CP.fsMeasure D =
      ((∑ i, (A k i : ℝ) * monoNormSq (adtEnum D (2 * n) i) * (A l i : ℝ) : ℝ) : ℂ) := by
  have hi : ∀ i j, Integrable (fun p : CP D => ((A k i : ℂ) * (A l j : ℂ)) *
      monoInner (2 * n) (ex D (2 * n) i) (ex D (2 * n) j) p.rep) (CP.fsMeasure D) := fun i j =>
    (integrable_monoInner_ex i j).const_mul _
  simp_rw [pairVal_conj_map b A hA k l]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hi i j]
  simp only [integral_const_mul, integral_monoInner_ex, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  push_cast
  ring

end VeroneseGramMono

theorem VeroneseGramMono.proof : VeroneseGramMono.Statement := by
  intro D n r b A hA
  ext k l
  change (1 / 2) * ((∫ p : CP D, pairVal (Veronese.metric D) n (b k) (b l) (Veronese.map D p.rep)
      ∂CP.fsMeasure D).re + (∫ p : CP D, pairVal (Veronese.metric D) n (b k) (b l)
        (conjPt (Veronese.map D p.rep)) ∂CP.fsMeasure D).re) = _
  rw [VeroneseGramMono.integral_pairVal b A hA, VeroneseGramMono.integral_pairVal_conj b A hA,
    Complex.ofReal_re]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

