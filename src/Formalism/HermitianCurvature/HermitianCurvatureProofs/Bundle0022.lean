import Formalism.HermitianCurvature.LatticeHerglotzBound
import Formalism.HermitianCurvature.StatementWd

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RootPushforwardDensity
section
open MeasureTheory Set Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.NthRootMeasurability

open Formalism.FourierDecayAlt.crystallineComparison

theorem detC (d : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ).det = ‖d‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

def zeta (s : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / s)

def R (s k : ℕ) (w : ℂ) : ℂ := zeta s ^ k * w ^ ((s : ℂ)⁻¹)

def A (s k : ℕ) : Set ℂ := {z | z ≠ 0 ∧ R s k (z ^ s) = z}

theorem measurable_R (s k : ℕ) : Measurable (R s k) := by
  unfold R; fun_prop

theorem measurableSet_A (s k : ℕ) : MeasurableSet (A s k) := by
  have h1 : MeasurableSet {z : ℂ | z ≠ 0} := (measurableSet_singleton (0 : ℂ)).compl
  have h2 : MeasurableSet {z : ℂ | R s k (z ^ s) = z} :=
    measurableSet_eq_fun ((measurable_R s k).comp (by fun_prop)) measurable_id
  exact h1.inter h2

theorem R_pow (s k : ℕ) (hs : s ≠ 0) (w : ℂ) : R s k w ^ s = w := by
  unfold R zeta
  rw [mul_pow, ← pow_mul, mul_comm k s, pow_mul, (Complex.isPrimitiveRoot_exp s hs).pow_eq_one,
    one_pow, one_mul, Complex.cpow_nat_inv_pow w hs]

theorem nthRoots_eq_R (s : ℕ) (hs : s ≠ 0) (w : ℂ) :
    nthRoots s w = (Multiset.range s).map (fun k => R s k w) :=
  (Complex.isPrimitiveRoot_exp s hs).nthRoots_eq (Complex.cpow_nat_inv_pow w hs)

theorem sum_roots (s : ℕ) (hs : s ≠ 0) (H : ℂ → ENNReal) (w : ℂ) :
    ((nthRoots s w).map H).sum = ∑ k ∈ Finset.range s, H (R s k w) := by
  rw [nthRoots_eq_R s hs, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

theorem A_disjoint (s : ℕ) (hs : s ≠ 0) :
    Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ) (A s) := by
  intro j hj k hk hjk
  rw [Function.onFun, Set.disjoint_left]
  intro z hzj hzk
  apply hjk
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  have e : zeta s ^ j * (z ^ s) ^ ((s : ℂ)⁻¹) = zeta s ^ k * (z ^ s) ^ ((s : ℂ)⁻¹) := by
    have := hzj.2.trans hzk.2.symm
    simpa [R] using this
  have hα : (z ^ s) ^ ((s : ℂ)⁻¹) ≠ 0 := by
    intro h0
    have := hzj.2
    simp only [R, h0, mul_zero] at this
    exact hzj.1 this.symm
  exact (Complex.isPrimitiveRoot_exp s hs).pow_inj hj hk (mul_right_cancel₀ hα e)

theorem A_union (s : ℕ) (hs : s ≠ 0) : (⋃ k ∈ Finset.range s, A s k) = {0}ᶜ := by
  ext z
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff, A,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, _, hz, _⟩; exact hz
  · intro hz
    have hmem : z ∈ nthRoots s (z ^ s) := (mem_nthRoots (Nat.pos_of_ne_zero hs)).mpr rfl
    rw [nthRoots_eq_R s hs, Multiset.mem_map] at hmem
    obtain ⟨k, hk, hkz⟩ := hmem
    exact ⟨k, Multiset.mem_range.mp hk, hz, hkz⟩

theorem image_A (s k : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) :
    (fun z => u⁻¹ * z ^ s) '' A s k = {0}ᶜ := by
  ext c
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, A, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨hz, _⟩, rfl⟩
    exact mul_ne_zero (inv_ne_zero hu) (pow_ne_zero _ hz)
  · intro hc
    refine ⟨R s k (u * c), ⟨?_, ?_⟩, ?_⟩
    · intro h0
      have := R_pow s k hs (u * c)
      rw [h0, zero_pow hs] at this
      exact mul_ne_zero hu hc this.symm
    · rw [R_pow s k hs]
    · rw [R_pow s k hs, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

theorem injOn_A (s k : ℕ) (u : ℂ) (hu : u ≠ 0) : InjOn (fun z => u⁻¹ * z ^ s) (A s k) := by
  intro z hz z' hz' e
  have e' : z ^ s = z' ^ s := mul_left_cancel₀ (inv_ne_zero hu) e
  rw [← hz.2, ← hz'.2, e']

theorem core (s : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (H : ℂ → ENNReal) (hH : Measurable H) :
    ∫⁻ c, ((nthRoots s (u * c)).map H).sum =
      ∫⁻ z, ENNReal.ofReal (‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2) * H z := by
  simp_rw [sum_roots s hs H]
  rw [lintegral_finsetSum (Finset.range s) (f := fun k c => H (R s k (u * c)))
    (fun k _ => hH.comp ((measurable_R s k).comp (measurable_const_mul u)))]
  have step : ∀ k, ∫⁻ c, H (R s k (u * c)) =
      ∫⁻ z in A s k, ENNReal.ofReal (‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2) * H z := by
    intro k
    calc ∫⁻ c, H (R s k (u * c)) = ∫⁻ c in {0}ᶜ, H (R s k (u * c)) := by
          rw [MeasureTheory.restrict_compl_singleton]
      _ = ∫⁻ c in (fun z => u⁻¹ * z ^ s) '' A s k, H (R s k (u * c)) := by
          rw [image_A s k hs u hu]
      _ = ∫⁻ z in A s k, ENNReal.ofReal |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
            (u⁻¹ * (s * z ^ (s - 1)))).restrictScalars ℝ).det| *
            H (R s k (u * (u⁻¹ * z ^ s))) :=
          lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_A s k)
            (fun z _ => (((hasDerivAt_pow s z).const_mul u⁻¹).hasFDerivAt.restrictScalars
              ℝ).hasFDerivWithinAt) (injOn_A s k u hu) _
      _ = _ := by
          refine setLIntegral_congr_fun (measurableSet_A s k) (fun z hz => ?_)
          rw [detC, abs_of_nonneg (sq_nonneg _), ← mul_assoc (u) u⁻¹, mul_inv_cancel₀ hu, one_mul,
            hz.2]
  simp_rw [step]
  rw [← lintegral_biUnion_finset (A_disjoint s hs) (fun k _ => measurableSet_A s k), A_union s hs,
    MeasureTheory.restrict_compl_singleton]

theorem real_id (s M : ℕ) (hs : 1 ≤ s) (hM : 2 ≤ M) (t z : ℂ) (ht : t ≠ 0) (hz : z ≠ 0) :
    ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 *
      (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
        ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
          (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) * ‖z‖ ^ (2 * (s - 1) ^ 2) =
      ‖z‖ ^ (2 * s * (M + s - 3)) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
  rw [show s' + 1 - 1 = s' by omega, show M' + 2 + (s' + 1) - 2 = M' + s' + 1 by omega,
    show M' + 2 - 2 = M' by omega, show M' + 2 + (s' + 1) - 3 = M' + s' by omega]
  simp only [norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hR : 0 < ‖z‖ := norm_pos_iff.mpr hz
  generalize ‖t‖ = T at hT ⊢
  generalize ‖z‖ = ρ at hR ⊢
  push_cast
  simp only [inv_pow, mul_pow, ← pow_mul]
  field_simp
  ring

theorem densityChange_ok : DensityChange := by
  intro s M t g hs hM ht hg
  have hs0 : s ≠ 0 := by omega
  have hu : ((-1 : ℂ) ^ (s + 1) * t ^ (s - 1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ht)
  calc _ = ∫⁻ c, ((nthRoots s (((-1 : ℂ) ^ (s + 1) * t ^ (s - 1)) * c)).map
            (fun z => ENNReal.ofReal (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
              ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
                (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) *
              (ENNReal.ofReal (‖z‖ ^ (2 * (s - 1) ^ 2)) * g z))).sum := by
        refine lintegral_congr (fun c => ?_)
        rw [show (-1 : ℂ) ^ (s + 1) * (c * t ^ (s - 1)) = ((-1 : ℂ) ^ (s + 1) * t ^ (s - 1)) * c by
          ring, ← Multiset.sum_map_mul_left]
        congr 1
        refine Multiset.map_congr rfl (fun z hz => ?_)
        rw [mem_nthRoots (by omega)] at hz
        rw [hz, inv_mul_cancel_left₀ hu]
    _ = ∫⁻ z, ENNReal.ofReal (‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * (s * z ^ (s - 1))‖ ^ 2) *
            (ENNReal.ofReal (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
              ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
                (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) *
              (ENNReal.ofReal (‖z‖ ^ (2 * (s - 1) ^ 2)) * g z)) :=
        core s hs0 _ hu _ (by
          refine (Measurable.ennreal_ofReal (by fun_prop)).mul
            ((Measurable.ennreal_ofReal (by fun_prop)).mul hg))
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), real_id s M hs hM t z ht hz]

end Formalism.FourierDecayAlt.P.NthRootMeasurability

theorem Formalism.FourierDecayAlt.P.rootPushforwardDensity : Formalism.FourierDecayAlt.crystallineComparison.DensityChange :=
  Formalism.FourierDecayAlt.P.NthRootMeasurability.densityChange_ok
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondEmbedMulFirstEmbedApply
section
namespace Formalism.FourierDecayAlt.P.Wd3

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]

theorem eU_mul (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x a j)]
  · by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      simp only [eU, Matrix.of_apply]
      by_cases hx : x a = i <;> by_cases hy : y a = l <;> by_cases hxy : ∀ b, b ≠ a → x b = y b <;>
        simp (config := {contextual := true}) [Function.update_apply, hx, hy, hxy]
    · rw [if_neg hjk]
      simp [eU, Function.update_apply, hjk]
  · intro z _ hz
    simp only [eU, Matrix.of_apply]
    rw [if_neg, zero_mul]
    rintro ⟨_, h2, h3⟩
    apply hz
    funext b
    by_cases hb : b = a
    · subst hb
      simp [h2]
    · rw [Function.update_of_ne hb]
      exact (h3 b hb).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_ins (a : S) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m) :
    m * ins a N = ∑ r, ∑ s, eU a r s * (m * N r s) := by
  have hm' : ∀ i j, Commute (eU a i j) m := hm
  rw [ins, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, ← (hm' r s).eq, mul_assoc]

theorem ins_mul (a : S) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) :
    ins a N * m = ∑ r, ∑ s, eU a r s * (N r s * m) := by
  rw [ins, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_assoc]

theorem eU_mul_ins (a : S) (k i : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m) :
    eU a k i * m * ins a N = ∑ s, eU a k s * (m * N i s) := by
  rw [mul_assoc, mul_ins a m N hm, Finset.mul_sum, Finset.sum_eq_single i]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, eU_mul, if_pos rfl]
  · intro r _ hr
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← mul_assoc, eU_mul, if_neg (Ne.symm hr), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ins_mul_eU (a : S) (j k : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m)
    (hN : FreeOf2 a N) :
    ins a N * (m * eU a j k) = ∑ r, eU a r k * (N r j * m) := by
  have hm' : ∀ i j, Commute (eU a i j) m := hm
  have h1 : ∀ r s, FreeOf a (N r s) := hN
  have hN' : ∀ r s i j, Commute (eU a i j) (N r s) := fun r s => h1 r s
  rw [← mul_assoc, ins_mul a m N, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · have hc : Commute (eU a j k) (N r j * m) := (hN' r j j k).mul_right (hm' j k)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, eU_mul, if_pos rfl]
  · intro s _ hs
    have hc : Commute (eU a j k) (N r s * m) := (hN' r s j k).mul_right (hm' j k)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, eU_mul, if_neg hs, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem firstEmbed_mul_secondEmbed_apply {B : Type} [Ring B] (M N : M2 B) (i r j s : Fin 2) :
    (E1 M * E2 N) (i, r) (j, s) = M i j * N r s := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem secondEmbed_mul_firstEmbed_apply {B : Type} [Ring B] (M N : M2 B) (i r j s : Fin 2) :
    (E2 N * E1 M) (i, r) (j, s) = N r s * M i j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem Pf_mul {B : Type} [Ring B] (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i r : Fin 2)
    (y : Fin 2 × Fin 2) : (Pf B * X) (i, r) y = X (r, i) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Pf, ite_and, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem mul_Pf {B : Type} [Ring B] (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (j s : Fin 2)
    (x : Fin 2 × Fin 2) : (X * Pf B) x (j, s) = X x (s, j) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Pf, ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem rtt_entry {B : Type} [Ring B] [Algebra K B] (M N : M2 B) (D : K)
    (h : (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 M * E2 N =
      E2 N * E1 M * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B))
    (i r j s : Fin 2) :
    D • (M i j * N r s) - M r j * N i s = D • (N r s * M i j) - N r j * M i s := by
  have h' := congrFun (congrFun h (i, r)) (j, s)
  rw [mul_assoc, sub_mul, Matrix.smul_mul, Matrix.one_mul, mul_sub, Matrix.mul_smul, Matrix.mul_one] at h'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Pf_mul, mul_Pf, firstEmbed_mul_secondEmbed_apply, secondEmbed_mul_firstEmbed_apply] at h'
  exact h'

theorem plus_core (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (D : K) (hM : FreeOf2 a M) (hN : FreeOf2 a N)
    (h : ∀ i r j s, D • (M i j * N r s) - M r j * N i s = D • (N r s * M i j) - N r j * M i s) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) =
      d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by
  have hM' : ∀ i j, FreeOf a (M i j) := hM
  refine Matrix.ext fun i j => ?_
  have key : ∀ r s, D • (eU a r s * (M i j * N r s)) - eU a r s * (M r j * N i s) =
      D • (eU a r s * (N r s * M i j)) - eU a r s * (N r j * M i s) := fun r s => by
    have := congrArg (eU a r s * ·) (h i r j s)
    simp only [mul_sub, mul_smul_comm] at this
    exact this
  have hL : (((D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) : M2 (SlopeTestRemainingChoices S A))) i j =
      D • (M i j * ins a N) - ∑ k, eU a k i * M k j * ins a N := by
    rw [sub_mul, sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    rfl
  have hR : ((d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) : M2 (SlopeTestRemainingChoices S A))) i j =
      D • (ins a N * M i j) - ∑ k, ins a N * (M i k * eU a j k) := by
    rw [mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_apply, Matrix.smul_apply, d0,
      Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.diagonal_mul, mul_assoc]
    rfl
  rw [hL, hR, mul_ins a _ N (hM' i j), ins_mul,
    Finset.sum_congr rfl fun k _ => eU_mul_ins a k i (M k j) N (hM' k j),
    Finset.sum_congr rfl fun k _ => ins_mul_eU a j k (M i k) N (hM' i k) hN,
    Finset.sum_comm (f := fun k r => eU a r k * (N r j * M i k)),
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => key r s

theorem minus_core (b : S) (M N : M2 (SlopeTestRemainingChoices S A)) (d : K) (hM : FreeOf2 b M) (hN : FreeOf2 b N)
    (h : ∀ i r j s, d • (N i j * M r s) - N r j * M i s = d • (M r s * N i j) - M r j * N i s) :
    d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M =
      M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) := by
  have hM' : ∀ i j, FreeOf b (M i j) := hM
  have hC : ∀ i j k l, Commute (eU b k l) (M i j) := fun i j => hM' i j
  have h1 : ∀ r s, FreeOf b (N r s) := hN
  have hT : FreeOf2 b Nᵀ := fun r s => h1 s r
  refine Matrix.ext fun i j => ?_
  have key : ∀ r s, d • (eU b r s * (N s r * M i j)) - eU b r s * (N i r * M s j) =
      d • (eU b r s * (M i j * N s r)) - eU b r s * (M i r * N s j) := fun r s => by
    have := congrArg (eU b r s * ·) (h s i r j)
    simp only [mul_sub, mul_smul_comm] at this
    exact this
  have hL : ((d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M : M2 (SlopeTestRemainingChoices S A))) i j =
      d • (ins b Nᵀ * M i j) - ∑ k, ins b Nᵀ * (M k j * eU b i k) := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.diagonal_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]
    exact congrArg (ins b Nᵀ * ·) (hC k j i k).eq
  have hR : ((M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) : M2 (SlopeTestRemainingChoices S A))) i j =
      d • (M i j * ins b Nᵀ) - ∑ k, eU b k j * M i k * ins b Nᵀ := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hC i k k j).eq]
    rfl
  rw [hL, hR, ins_mul, mul_ins b _ _ (hM' i j),
    Finset.sum_congr rfl fun k _ => ins_mul_eU b i k (M k j) Nᵀ (hM' k j) hT,
    Finset.sum_congr rfl fun k _ => eU_mul_ins b k j (M i k) Nᵀ (hM' i k),
    Finset.sum_comm (f := fun k r => eU b r k * (Nᵀ r i * M k j)),
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => key r s

end

end Formalism.FourierDecayAlt.P.Wd3

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

theorem exchange_relation_plus : Formalism.FourierDecayAlt.Wd.ExchPlus := by
  unfold Formalism.FourierDecayAlt.Wd.ExchPlus
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Y Ya hmod hfree hY hYa
  obtain ⟨_, _, hrtt, _, _⟩ := hmod
  have hr : RTTat TT Ya Y := hrtt Ya hYa Y hY
  have hc := Wd3.plus_core a (TT Y) (TT Ya) (Y - Ya) (hfree Y) (hfree Ya)
    (Wd3.rtt_entry (TT Y) (TT Ya) (Y - Ya) hr)
  rw [Rh0, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hc]

theorem exchange_relation_minus : Formalism.FourierDecayAlt.Wd.ExchMinus := by
  unfold Formalism.FourierDecayAlt.Wd.ExchMinus
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q b Y Yb hmod hfree hY hYb
  obtain ⟨_, _, hrtt, _, _⟩ := hmod
  have hr : RTTat TT Y Yb := hrtt Y hY Yb hYb
  have hc := Wd3.minus_core b (TT Y) (TT Yb) (Yb - Y) (hfree Y) (hfree Yb)
    (Wd3.rtt_entry (TT Yb) (TT Y) (Yb - Y) hr)
  simp only [Rht0, Matrix.mul_smul, Matrix.smul_mul, hc]

end Formalism.FourierDecayAlt.P
end

