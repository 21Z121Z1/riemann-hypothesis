import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PContinuousRootHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter
open scoped Topology

theorem hasDerivAt_eval_cons {k : ℕ} (y : Fin k → ℂ) (P : MvPolynomial (Fin (k + 1)) ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) P)
      (eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 P)) s := by
  apply P.induction_on (fun a => ?_) (fun p q hp hq => ?_) fun p i hp => ?_
  · simpa using hasDerivAt_const s a
  · simp only [map_add]
    exact hp.add hq
  · cases i using Fin.cases with
    | zero =>
      have h0 := hp.mul (hasDerivAt_id s)
      have e1 : (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) (p * X 0)) =
          fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) p * id s := by
        funext x; simp
      have e2 : eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 (p * X 0)) =
          eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 p) * id s +
            eval (Fin.cons s y : Fin (k + 1) → ℂ) p * 1 := by
        simp [Derivation.leibniz]; ring
      rw [e1, e2]; exact h0
    | succ j =>
      have h0 := hp.mul (hasDerivAt_const s (y j))
      have e1 : (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) (p * X j.succ)) =
          fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) p * y j := by
        funext x; simp
      have e2 : eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 (p * X j.succ)) =
          eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 p) * y j +
            eval (Fin.cons s y : Fin (k + 1) → ℂ) p * 0 := by
        simp [Derivation.leibniz, pderiv_X_of_ne (Fin.succ_ne_zero j)]; ring
      rw [e1, e2]; exact h0

theorem ContinuousRootHolomorphic.proof : ContinuousRootHolomorphic.Statement := by
  intro k Q O h hO hh hQ y hy hd
  set c := eval (Fin.cons (h y) y : Fin (k + 1) → ℂ) (pderiv 0 Q) with hc
  let f : (Fin k → ℂ) × ℂ → ℂ := fun v => eval (Fin.cons v.2 v.1 : Fin (k + 1) → ℂ) Q
  have hfa : AnalyticAt ℂ f (y, h y) := by
    have hi : ∀ i : Fin (k + 1),
        AnalyticAt ℂ (fun v : (Fin k → ℂ) × ℂ => (Fin.cons v.2 v.1 : Fin (k + 1) → ℂ) i) (y, h y) := by
      intro i
      cases i using Fin.cases with
      | zero => simpa using analyticAt_snd
      | succ j =>
        have e : (fun v : (Fin k → ℂ) × ℂ => (Fin.cons v.2 v.1 : Fin (k + 1) → ℂ) j.succ) =
            ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) j).comp
              (ContinuousLinearMap.fst ℂ (Fin k → ℂ) ℂ)) := by
          funext v; simp
        rw [e]; exact ContinuousLinearMap.analyticAt _ _
    simpa [f, MvPolynomial.coe_aeval_eq_eval] using AnalyticAt.aeval_mvPolynomial hi Q
  have hf := hfa.hasStrictFDerivAt
  have hderiv : HasDerivAt (fun s => f (y, s)) c (h y) := hasDerivAt_eval_cons y Q (h y)
  have hcomp : HasFDerivAt (fun s => f (y, s))
      (fderiv ℂ f (y, h y) ∘L ContinuousLinearMap.inr ℂ (Fin k → ℂ) ℂ) (h y) :=
    hf.hasFDerivAt.comp (h y) (hasFDerivAt_prodMk_right y (h y))
  set D := fderiv ℂ f (y, h y) ∘L ContinuousLinearMap.inr ℂ (Fin k → ℂ) ℂ with hDdef
  have hD1 : D 1 = c := by
    rw [hcomp.unique hderiv.hasFDerivAt]; simp
  have hDx : ∀ x : ℂ, D x = x * c := fun x => by
    rw [← hD1, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have hinv : D.IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℂ ℂ) ?_ ?_ <;>
      refine ContinuousLinearMap.ext_ring ?_ <;> simp [hDx, hd]
  have hφ := hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  have hev := hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  refine hφ.differentiableAt.congr_of_eventuallyEq ?_
  have ht : Tendsto (fun t => (t, h t)) (𝓝 y) (𝓝 (y, h y)) :=
    (continuousAt_id.prodMk (hh.continuousAt (hO.mem_nhds hy))).tendsto
  filter_upwards [ht.eventually hev, hO.mem_nhds hy] with t ht1 ht2
  exact (ht1.mp (by simp only [f]; rw [hQ t ht2, hQ y hy])).symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

noncomputable section

section Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shrinkAlong (i0 : ι) (k : ι → ℝ) (δ : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.id - (1 - δ) • (LinearMap.proj i0 : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight k

omit [Fintype ι] [DecidableEq ι] in
theorem shrinkAlong_apply (i0 : ι) (k : ι → ℝ) (δ : ℝ) (z : ι → ℝ) :
    shrinkAlong i0 k δ z = z - ((1 - δ) * z i0) • k := by
  simp [shrinkAlong, smul_smul]

theorem det_shrinkAlong (i0 : ι) (k : ι → ℝ) (δ : ℝ) :
    LinearMap.det (shrinkAlong i0 k δ) = 1 - (1 - δ) * k i0 := by
  rw [← LinearMap.det_toMatrix']
  have hM : LinearMap.toMatrix' (shrinkAlong i0 k δ) =
      1 + Matrix.replicateCol Unit (-(1 - δ) • k) * Matrix.replicateRow Unit (Pi.single i0 (1 : ℝ)) := by
    ext i j
    simp only [LinearMap.toMatrix'_apply, shrinkAlong_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, Pi.single_apply]
    by_cases hij : i = j <;> by_cases hj : j = i0 <;> simp [hij, hj, eq_comm (a := i0)] <;> ring
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Pi.single_apply]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker {f : (ι → ℝ) → F}
    {A : (ι → ℝ) →L[ℝ] F} {k : ι → ℝ} {i0 : ι} (hk : A k = 0) (hki : k i0 = 1) {δ : ℝ≥0}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t : Set (ι → ℝ)} (ht : ApproximatesLinearOn f A t δ) :
    μH[Fintype.card ι] (f '' t) ≤
      ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ *
        volume t := by
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  set T := shrinkAlong i0 k (δ : ℝ) with hTdef
  have hT : ∀ z, T z = z - ((1 - (δ : ℝ)) * z i0) • k := shrinkAlong_apply i0 k _
  have hTi : ∀ z, T z i0 = δ * z i0 := by
    intro z; rw [hT]; simp [hki]; ring
  let S : (ι → ℝ) → (ι → ℝ) := fun w => w + (((δ : ℝ)⁻¹ - 1) * w i0) • k
  have hST : ∀ x, S (T x) = x := by
    intro x
    simp only [S, hTi]
    have hδne : (δ : ℝ) ≠ 0 := hδ0'.ne'
    have : ((δ : ℝ)⁻¹ - 1) * (δ * x i0) = (1 - δ) * x i0 := by field_simp
    rw [this, hT, sub_add_cancel]
  have himg : f '' t = (f ∘ S) '' (T '' t) := by
    rw [image_image]; simp [hST]
  have hlip : LipschitzOnWith (Real.toNNReal (‖A‖ + 1 + ‖k‖)) (f ∘ S) (T '' t) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hST, dist_eq_norm]
    rw [← map_sub]
    set v := x - y with hv
    have hAv : A v = A (T v) := by
      rw [hT, map_sub A v, map_smul, hk, smul_zero, sub_zero]
    have hsplit : (δ : ℝ) • v = (δ : ℝ) • T v + ((1 - δ) * T v i0) • k := by
      rw [hTi, hT]; ext j; simp; ring
    have hδv : (δ : ℝ) * ‖v‖ ≤ ‖T v‖ + ‖T v‖ * ‖k‖ := by
      have h1 : ‖(δ : ℝ) • T v‖ ≤ ‖T v‖ := by
        rw [norm_smul, Real.norm_of_nonneg hδ0'.le]
        exact mul_le_of_le_one_left (norm_nonneg _) hδ1'
      have h2 : ‖((1 - (δ : ℝ)) * T v i0) • k‖ ≤ ‖T v‖ * ‖k‖ := by
        rw [norm_smul, norm_mul, Real.norm_of_nonneg (by linarith)]
        have h3 : ‖T v i0‖ ≤ ‖T v‖ := norm_le_pi_norm _ _
        have h4 : (1 - (δ : ℝ)) * ‖T v i0‖ ≤ ‖T v‖ := by
          calc (1 - (δ : ℝ)) * ‖T v i0‖ ≤ 1 * ‖T v‖ :=
                mul_le_mul (by linarith) h3 (norm_nonneg _) zero_le_one
            _ = ‖T v‖ := one_mul _
        exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      calc (δ : ℝ) * ‖v‖ = ‖(δ : ℝ) • v‖ := by rw [norm_smul, Real.norm_of_nonneg hδ0'.le]
        _ ≤ ‖(δ : ℝ) • T v‖ + ‖((1 - (δ : ℝ)) * T v i0) • k‖ := by
          rw [hsplit]; exact norm_add_le _ _
        _ ≤ ‖T v‖ + ‖T v‖ * ‖k‖ := add_le_add h1 h2
    have happ := ht x hx y hy
    have hAT : ‖A (T v)‖ ≤ ‖A‖ * ‖T v‖ := A.le_opNorm _
    calc ‖f x - f y‖ = ‖(f x - f y - A v) + A v‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - f y - A v‖ + ‖A v‖ := norm_add_le _ _
      _ ≤ (δ : ℝ) * ‖v‖ + ‖A‖ * ‖T v‖ := by rw [hAv] at happ ⊢; exact add_le_add happ hAT
      _ ≤ (‖A‖ + 1 + ‖k‖) * ‖T v‖ := by nlinarith [hδv]
  rw [himg]
  calc μH[Fintype.card ι] ((f ∘ S) '' (T '' t))
      ≤ ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) *
          μH[Fintype.card ι] (T '' t) := hlip.hausdorffMeasure_image_le (by positivity)
    _ = ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) *
          (ENNReal.ofReal δ * volume t) := by
      rw [hausdorffMeasure_pi_real, Measure.addHaar_image_linearMap, hTdef, det_shrinkAlong, hki]
      congr 3
      rw [abs_of_pos (by linarith)]
      ring
    _ = _ := by rw [mul_assoc]

end Real

section Global

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem exists_pos_hausdorffMeasure_image_le_of_not_injective (f : (ι → ℝ) → F)
    (A : (ι → ℝ) →L[ℝ] F) (hA : ¬ Function.Injective A) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ →
      μH[Fintype.card ι] (f '' t) ≤ ε * volume t := by
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, A a = A b ∧ a ≠ b := by
    simpa [Function.Injective, not_forall] using hA
  have hk0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i0, hi0⟩ : ∃ i0, (a - b) i0 ≠ 0 := by
    simpa using Function.ne_iff.mp hk0
  set k : ι → ℝ := ((a - b) i0)⁻¹ • (a - b) with hkdef
  have hk : A k = 0 := by rw [hkdef, map_smul, map_sub, hab, sub_self, smul_zero]
  have hki : k i0 = 1 := by
    rw [hkdef, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hi0
  set K : ℝ≥0 := Real.toNNReal (‖A‖ + 1 + ‖k‖)
  set δ : ℝ≥0 := min 1 (ε / (K ^ Fintype.card ι + 1))
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
  refine ⟨δ, hδ0, fun t ht => ?_⟩
  have key :=
    hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker hk hki hδ0 (min_le_left _ _) ht
  refine key.trans ?_
  have hKδ : K ^ Fintype.card ι * δ ≤ ε := by
    calc K ^ Fintype.card ι * δ ≤ (K ^ Fintype.card ι + 1) * (ε / (K ^ Fintype.card ι + 1)) := by
          gcongr
          · exact le_self_add
          · exact min_le_right _ _
      _ = ε := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ ε (by positivity)
  have hcoe : (K : ℝ≥0∞) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ =
      ((K ^ Fintype.card ι * δ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.rpow_natCast, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, ENNReal.coe_pow]
  rw [hcoe]
  gcongr

variable [SecondCountableTopology F]

theorem hausdorffMeasure_image_le_of_not_injective_ball {f : (ι → ℝ) → F} {s : Set (ι → ℝ)}
    {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, ¬ Function.Injective (f' x)) (R : ℝ) (hs : s ⊆ closedBall 0 R)
    (ε : ℝ≥0) (εpos : 0 < ε) :
    μH[Fintype.card ι] (f '' s) ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by
  rcases eq_empty_or_nonempty s with (rfl | h's)
  · simp
  have : ∀ A : (ι → ℝ) →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (¬ Function.Injective A →
      ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ →
        μH[Fintype.card ι] (f '' t) ≤ ε * volume t) := by
    intro A
    by_cases hA : Function.Injective A
    · exact ⟨1, one_pos, fun h => absurd hA h⟩
    · obtain ⟨δ, hδ, h⟩ := exists_pos_hausdorffMeasure_image_le_of_not_injective f A hA εpos
      exact ⟨δ, hδ, fun _ => h⟩
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ
      fun A => (hδ A).1.ne'
  calc
    μH[Fintype.card ι] (f '' s) ≤ μH[Fintype.card ι] (⋃ n, f '' (s ∩ t n)) := by
      rw [← image_iUnion, ← inter_iUnion]
      gcongr
      exact subset_inter Subset.rfl t_cover
    _ ≤ ∑' n, μH[Fintype.card ι] (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (ε : ℝ≥0∞) * volume (s ∩ t n) := by
      gcongr with n
      obtain ⟨y, ys, hy⟩ := Af' h's n
      exact (hδ (A n)).2 (by rw [hy]; exact hinj y ys) _ (ht n)
    _ ≤ ε * ∑' n, volume (closedBall (0 : ι → ℝ) R ∩ t n) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = ε * volume (⋃ n, closedBall (0 : ι → ℝ) R ∩ t n) := by
      rw [measure_iUnion]
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      · intro n
        exact measurableSet_closedBall.inter (t_meas n)
    _ ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by grw [← inter_iUnion, inter_subset_left]

theorem hausdorffMeasure_image_eq_zero_of_not_injective {f : (ι → ℝ) → F} {s : Set (ι → ℝ)}
    {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, ¬ Function.Injective (f' x)) :
    μH[Fintype.card ι] (f '' s) = 0 := by
  suffices H : ∀ R, μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) = 0 by
    rw [← nonpos_iff_eq_zero, ← iUnion_inter_closedBall_nat s 0]
    calc
      μH[Fintype.card ι] (f '' ⋃ n : ℕ, s ∩ closedBall 0 n)
          ≤ ∑' n : ℕ, μH[Fintype.card ι] (f '' (s ∩ closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_le _
      _ ≤ 0 := by simp only [H, tsum_zero, le_refl]
  intro R
  have hA : ∀ ε : ℝ≥0, 0 < ε →
      μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) ≤ ε * volume (closedBall (0 : ι → ℝ) R) :=
    fun ε εpos => hausdorffMeasure_image_le_of_not_injective_ball
      (fun x hx => (hf' x hx.1).mono inter_subset_left) (fun x hx => hinj x hx.1) R
      inter_subset_right ε εpos
  have hB : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝[>] 0)
      (𝓝 0) := by
    have : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝 0)
        (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R))) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr measure_closedBall_lt_top.ne)
    simp only [zero_mul, ENNReal.coe_zero] at this
    exact Tendsto.mono_left this nhdsWithin_le_nhds
  rw [← nonpos_iff_eq_zero]
  apply ge_of_tendsto hB
  filter_upwards [self_mem_nhdsWithin]
  exact hA

end Global

theorem CriticalImageNull.proof : CriticalImageNull.Statement := by
  intro d n U f hU hf
  let b := Pi.basis (fun _ : Fin d => Complex.basisOneI)
  let e : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
    b.equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d := by
    simp [Fintype.card_sigma, mul_comm]
  set C := {s | s ∈ U ∧ ¬ Function.Injective (fderiv ℂ f s)} with hC
  have himg : f '' C = (f ∘ e) '' (e ⁻¹' C) := by
    rw [image_comp, image_preimage_eq _ e.surjective]
  have key := hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e) (s := e ⁻¹' C)
    (f' := fun x => ((fderiv ℂ f (e x)).restrictScalars ℝ).comp (e : _ →L[ℝ] _)) ?_ ?_
  · rw [himg, ← hcard]
    exact key
  · intro x hx
    have hU' : U ∈ 𝓝 (e x) := hU.mem_nhds hx.1
    have h1 : HasFDerivAt f (fderiv ℂ f (e x)) (e x) := (hf.differentiableAt hU').hasFDerivAt
    exact ((h1.restrictScalars ℝ).comp x e.hasFDerivAt).hasFDerivWithinAt
  · intro x hx hinj
    apply hx.2
    intro a c hac
    have h2 := @hinj (e.symm a) (e.symm c) (by simpa using hac)
    simpa using congrArg e h2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PExtensionQuotientLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ExtensionQuotientLength.proof : ExtensionQuotientLength.Statement := by
  intro R B _ _ _ r hinj hr hfin
  set a := Algebra.linearMap R B
  set P : Submodule R B := LinearMap.range a
  set rP : Submodule R B := Submodule.map a (Ideal.span {r})
  set rB : Submodule R B := (Ideal.span {algebraMap R B r}).restrictScalars R
  have hrPP : rP ≤ P := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hrPrB : rP ≤ rB := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact Ideal.mem_span_singleton'.2 ⟨algebraMap R B c, by simp [a]⟩
  have hPr : P ≤ rP.comap (r • LinearMap.id) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨r * x, Ideal.mem_span_singleton'.2 ⟨x, mul_comm _ _⟩, by simp [a, Algebra.smul_def]⟩

  let f₁ := (Ideal.span {r}).mapQ rP a (Submodule.le_comap_map _ _)
  let g₁ := rP.mapQ P LinearMap.id hrPP
  have hf₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    simp only [f₁, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨y, hy, hyx⟩ := hq
    rwa [← hinj hyx]
  have hg₁ : Function.Surjective g₁ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₁ : Function.Exact f₁ g₁ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₁, f₁, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ x => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      simpa using P.sub_mem (hrPP hq) ⟨x, rfl⟩

  let f₂ := P.mapQ rP (r • LinearMap.id) hPr
  let g₂ := rP.mapQ rB LinearMap.id hrPrB
  have hf₂ : Function.Injective f₂ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [f₂, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply,
      LinearMap.id_apply] at hq ⊢
    obtain ⟨y, hy, hyb⟩ := hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine ⟨c, (mul_cancel_left_mem_nonZeroDivisors hr).1 ?_⟩
    simpa [a, Algebra.smul_def, mul_comm] using hyb
  have hg₂ : Function.Surjective g₂ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₂ : Function.Exact f₂ g₂ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₂, f₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (show b ∈ Ideal.span {algebraMap R B r} from hb)
      exact ⟨Submodule.Quotient.mk c, by simp [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ c => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      have hc : r • c ∈ rB := Ideal.mem_span_singleton'.2 ⟨c, by simp [Algebra.smul_def, mul_comm]⟩
      simpa using rB.sub_mem hc (hrPrB hq)
  have h₁ := Module.length_eq_add_of_exact f₁ g₁ hf₁ hg₁ he₁
  have h₂ := Module.length_eq_add_of_exact f₂ g₂ hf₂ hg₂ he₂
  rw [← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R B r})).length_eq]
  rw [h₁, add_comm] at h₂
  exact (WithTop.add_left_inj hfin).1 h₂

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGeneralProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Matrix MvPolynomial

noncomputable section

def genericMatrix (d n : ℕ) : Matrix (Fin d) (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) :=
  Matrix.of fun i k => X (i, k)

def detPoly {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) : MvPolynomial (Fin d × Fin n) ℂ :=
  Matrix.det (Matrix.of fun i j => ∑ k, genericMatrix d n i k * C (M k j))

theorem eval_detPoly {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) (x : Fin d × Fin n → ℂ) :
    eval x (detPoly M) = (Matrix.of (fun i k => x (i, k)) * M).det := by
  unfold detPoly
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp [genericMatrix, Matrix.mul_apply]

theorem GeneralProjection.proof : GeneralProjection.Statement := by
  intro n d m L hL
  classical
  set M : Fin m → Matrix (Fin n) (Fin d) ℂ := fun b => LinearMap.toMatrix' (L b) with hM
  have hne : ∀ b, detPoly (M b) ≠ 0 := by
    intro b h
    obtain ⟨g, hg⟩ := (L b).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hL b))
    have h1 : LinearMap.toMatrix' g * M b = 1 := by
      rw [hM]; dsimp only
      rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
    have := congrArg (eval (fun p : Fin d × Fin n => LinearMap.toMatrix' g p.1 p.2)) h
    rw [eval_detPoly, map_zero] at this
    have h2 : Matrix.of (fun i k => LinearMap.toMatrix' g i k) = LinearMap.toMatrix' g := by
      ext i k; rfl
    rw [h2, h1, det_one] at this
    exact one_ne_zero this
  have hprod : (∏ b, detPoly (M b)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ => hne b
  obtain ⟨x, hx⟩ : ∃ x : Fin d × Fin n → ℂ, eval x (∏ b, detPoly (M b)) ≠ 0 := by
    by_contra hcon
    refine hprod (MvPolynomial.funext fun x => ?_)
    rw [map_zero]
    by_contra hx
    exact hcon ⟨x, hx⟩
  refine ⟨Matrix.of fun i k => x (i, k), fun b v w hvw => ?_⟩
  rw [map_prod] at hx
  have hb : (Matrix.of (fun i k => x (i, k)) * M b).det ≠ 0 := by
    rw [← eval_detPoly]
    exact (Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)
  have key : ∀ u, (Matrix.of fun i k => x (i, k)) *ᵥ L b u = (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ u := by
    intro u
    rw [← Matrix.mulVec_mulVec, hM]
    dsimp only
    rw [LinearMap.toMatrix'_mulVec]
  simp only [key] at hvw
  have h0 : (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hb h0)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolyKaehlerFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open KaehlerDifferential TensorProduct

theorem PolyKaehlerFree.proof : PolyKaehlerFree.Statement := by
  intro R k _ _ _ n
  set B := MvPolynomial (Fin n) k

  have hinj : Function.Injective (mapBaseChange R k B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R k B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hex := exact_mapBaseChange_map R k B

  obtain ⟨l, hl⟩ := Module.projective_lifting_property ((map R k B B).restrictScalars B)
    LinearMap.id (map_surjective R k B)
  let e := ((hex.splitSurjectiveEquiv hinj) ⟨l, hl⟩).1
  have : Module.Free B Ω[B⁄k] := Module.Free.of_basis (mvPolynomialBasis k (Fin n))
  exact Module.Free.of_equiv e.symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

