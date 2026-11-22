import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0001

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.LocalExtensionEqMulJacobian
section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem weightFunction_nonneg {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) :
    0 ≤ ev n g ph r x := by
  unfold ev; positivity

theorem mem_zeroSet_of_weight_nonpos {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ)
    (hr : r ≠ 0) (x : M) (h : ev n g ph r x ≤ 0) : x ∈ zeroSet n g := by
  have h0 : ev n g ph r x = 0 := le_antisymm h (weightFunction_nonneg n g ph r x)
  unfold ev at h0
  have hs : (∑ i, ‖g i x‖ ^ 2) = 0 := by
    rcases div_eq_zero_iff.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact absurd h2 (Real.exp_pos _).ne'
    · exact absurd h1 (pow_ne_zero 2 hr)
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖g i x‖)).1 hs i (Finset.mem_univ i)
  simpa using this

theorem continuous_weightFunction {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ)
    (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) : Continuous (ev n g ph r) := by
  have hgc : ∀ i, Continuous (g i) := fun i => Smooth.continuous n z hz _ (Holo.smooth n z _ (hg i))
  have hpc : Continuous ph := by
    have := Smooth.continuous n z hz _ hph
    exact Complex.continuous_re.comp this |>.congr (fun x => by simp)
  unfold ev
  fun_prop

theorem volume_singleton_eq_zero {M : Type*} [TopologicalSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] (n : ℕ) (hn : 1 ≤ n) (z : M → V n)
    (hz : IsLocalHomeomorph z) (p : M) : vol n z {p} = 0 := by
  obtain ⟨e, he, hp⟩ := exists_chart n z hz p
  rw [vol_image n z hz e.source e.open_source (injOn_source_of_chart n z e he) {p}
    (measurableSet_singleton p) (Set.singleton_subset_iff.2 hp), Set.image_singleton]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact measure_singleton _

theorem not_mem_neighborhood_of_ne {M : Type*} [TopologicalSpace M] (n : ℕ) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (W : M → Set M) (m : ℝ) (hL : IsLocalData n g ph r W m)
    {p q x : M} (hp : p ∈ zeroSet n g) (hq : q ∈ zeroSet n g) (hpq : q ≠ p) (hx : x ∈ W p) :
    x ∉ W q := fun hxq =>
  Set.disjoint_left.1 ((hL.2 p hp).2.2.2.2 q hq hpq) (subset_closure hx) (subset_closure hxq)

theorem localExtension_eq_mul_jacobian {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ)
    (hL : IsLocalData n g ph r W m) (hfin : (zeroSet n g).Finite)
    {p x : M} (hp : p ∈ zeroSet n g) (hx : x ∈ W p) :
    gt n z g c W x = c p * jac n z g x := by
  unfold gt
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_eq_single p (fun q hq hqp => Set.indicator_of_notMem
      (not_mem_neighborhood_of_ne n g ph r W m hL hp ((hfin.mem_toFinset).1 hq) hqp hx) _)
      (fun h => absurd ((hfin.mem_toFinset).2 hp) h), Set.indicator_of_mem hx]

theorem localExtension_eq_zero_off {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (c : M → ℂ) (W : M → Set M) {x : M}
    (hx : ∀ p ∈ zeroSet n g, x ∉ W p) : gt n z g c W x = 0 := by
  unfold gt
  exact finsum_mem_eq_zero_of_forall_eq_zero (fun p hp => Set.indicator_of_notMem (hx p hp) _)

theorem lintegral_le_sum_setLIntegral {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (U : ι → Set α) (hU : ∀ i ∈ s, MeasurableSet (U i)) (f : α → ℝ≥0∞) (h : ι → α → ℝ≥0∞)
    (hsupp : ∀ x, f x ≠ 0 → ∃ i ∈ s, x ∈ U i) (hle : ∀ i ∈ s, ∀ x ∈ U i, f x ≤ h i x) :
    ∫⁻ x, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in U i, h i x ∂μ := by
  have hsub : Function.support f ⊆ ⋃ i : s, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hsupp x hx
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  rw [← setLIntegral_eq_of_support_subset hsub]
  calc ∫⁻ x in ⋃ i : s, U i, f x ∂μ ≤ ∑' i : s, ∫⁻ x in U i, f x ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i ∈ s, ∫⁻ x in U i, f x ∂μ := Finset.tsum_subtype s (fun i => ∫⁻ x in U i, f x ∂μ)
    _ ≤ ∑ i ∈ s, ∫⁻ x in U i, h i x ∂μ :=
        Finset.sum_le_sum fun i hi => setLIntegral_mono' (hU i hi) (hle i hi)

theorem sqrt_add_sq_le_weighted (x y : ℝ≥0∞) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hx : x ≤ ENNReal.ofReal X) (hy : y ≤ ENNReal.ofReal Y) :
    (x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ≤
      ENNReal.ofReal ((101 / 100) * X + 101 * Y) := by
  have h1 : x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt X) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hX (by norm_num)]
    exact ENNReal.rpow_le_rpow hx (by norm_num)
  have h2 : y ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt Y) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hY (by norm_num)]
    exact ENNReal.rpow_le_rpow hy (by norm_num)
  have h3 : x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt X + Real.sqrt Y) := by
    rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
    exact add_le_add h1 h2
  calc (x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt X + Real.sqrt Y) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
    _ = ENNReal.ofReal ((Real.sqrt X + Real.sqrt Y) ^ (2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ ≤ ENNReal.ofReal ((101 / 100) * X + 101 * Y) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Real.rpow_two]
        nlinarith [sq_nonneg (Real.sqrt X / 10 - 10 * Real.sqrt Y), Real.sq_sqrt hX, Real.sq_sqrt hY]

theorem lintegral_dyadic_shell_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (e : α → ℝ) (he : Measurable e)
    (he0 : ∀ x, 0 ≤ e x) (U : Set α) (hU : MeasurableSet U) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (n : ℕ) (hn : 1 ≤ n) (ε B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B)
    (hZ : μ (U ∩ {x | e x ≤ 0}) = 0)
    (hsh : ∀ t : ℝ, 0 < t → t ≤ ε →
      ∫⁻ x in U ∩ {x | t ^ 2 / 2 ≤ e x ∧ e x ≤ t ^ 2},
        ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ ≤ ENNReal.ofReal B) :
    ∫⁻ x in U ∩ {x | e x < ε ^ 2}, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (2 * B * ε ^ 2) := by
  set t : ℕ → ℝ := fun k => Real.sqrt (ε ^ 2 / 2 ^ k) with ht
  have ht2 : ∀ k, t k ^ 2 = ε ^ 2 / 2 ^ k := fun k => Real.sq_sqrt (by positivity)
  have htpos : ∀ k, 0 < t k := fun k => Real.sqrt_pos.2 (by positivity)
  have htle : ∀ k, t k ≤ ε := fun k => by
    calc t k ≤ Real.sqrt (ε ^ 2) :=
          Real.sqrt_le_sqrt (div_le_self (sq_nonneg _) (one_le_pow₀ one_le_two))
      _ = ε := Real.sqrt_sq hε.le
  set A : ℕ → Set α := fun k => U ∩ {x | t k ^ 2 / 2 ≤ e x ∧ e x ≤ t k ^ 2} with hAdef
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    hU.inter ((measurableSet_le measurable_const he).inter (measurableSet_le he measurable_const))
  have hcover : U ∩ {x | e x < ε ^ 2} ⊆ (U ∩ {x | e x ≤ 0}) ∪ ⋃ k, A k := by
    rintro x ⟨hxU, hx⟩
    simp only [Set.mem_setOf_eq] at hx
    by_cases h0 : e x ≤ 0
    · exact Or.inl ⟨hxU, h0⟩
    · push_neg at h0
      obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := ε ^ 2 / e x) (y := (2 : ℝ))
        ((one_le_div h0).2 hx.le) (by norm_num)
      refine Or.inr (Set.mem_iUnion.2 ⟨k, hxU, ?_⟩)
      have h1 := (le_div_iff₀ h0).1 hk1
      have h2 := (div_lt_iff₀ h0).1 hk2
      have hp : (0 : ℝ) < 2 ^ k := by positivity
      rw [ht2 k]
      constructor
      · rw [div_div, div_le_iff₀ (by positivity)]
        have h3 : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        rw [h3] at h2
        linarith
      · rw [le_div_iff₀ hp]; nlinarith
  have hk : ∀ k, ∫⁻ x in A k, ENNReal.ofReal (f x) ∂μ ≤
      ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B := by
    intro k
    calc ∫⁻ x in A k, ENNReal.ofReal (f x) ∂μ
        ≤ ∫⁻ x in A k, ENNReal.ofReal (ε ^ 2 / 2 ^ k) *
            ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ := by
          refine setLIntegral_mono' (hA k) (fun x hx => ?_)
          obtain ⟨_, hx1, hx2⟩ := hx
          have hex : 0 < e x := lt_of_lt_of_le (by have := htpos k; positivity) hx1
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [Real.rpow_neg (he0 x), Real.rpow_natCast]
          have hpn : 0 < e x ^ n := pow_pos hex n
          have hle1 : e x ≤ 1 := by
            have : t k ^ 2 ≤ 1 := by
              rw [ht2 k]
              calc ε ^ 2 / 2 ^ k ≤ ε ^ 2 := div_le_self (sq_nonneg _) (one_le_pow₀ one_le_two)
                _ ≤ 1 := by nlinarith
            linarith
          have hen : e x ^ n ≤ ε ^ 2 / 2 ^ k := by
            calc e x ^ n ≤ e x := pow_le_of_le_one (he0 x) hle1 (by omega)
              _ ≤ t k ^ 2 := hx2
              _ = ε ^ 2 / 2 ^ k := ht2 k
          rw [show ε ^ 2 / 2 ^ k * (f x * (e x ^ n)⁻¹) = f x * ((ε ^ 2 / 2 ^ k) / e x ^ n) by
            field_simp]
          exact le_mul_of_one_le_right (hf x) ((one_le_div hpn).2 hen)
      _ = ENNReal.ofReal (ε ^ 2 / 2 ^ k) *
            ∫⁻ x in A k, ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B :=
          by gcongr; exact hsh (t k) (htpos k) (htle k)
  have hgeo : ∀ k : ℕ, ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B =
      ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal B * 2⁻¹ ^ k := by
    intro k
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2) k,
      ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
    ring
  calc ∫⁻ x in U ∩ {x | e x < ε ^ 2}, ENNReal.ofReal (f x) ∂μ
      ≤ ∫⁻ x in (U ∩ {x | e x ≤ 0}) ∪ ⋃ k, A k, ENNReal.ofReal (f x) ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∫⁻ x in U ∩ {x | e x ≤ 0}, ENNReal.ofReal (f x) ∂μ +
          ∫⁻ x in ⋃ k, A k, ENNReal.ofReal (f x) ∂μ := lintegral_union_le _ _ _
    _ ≤ 0 + ∑' k, ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B :=
        add_le_add (le_of_eq (setLIntegral_measure_zero _ _ hZ))
          ((lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hk))
    _ = ENNReal.ofReal (2 * B * ε ^ 2) := by
        simp_rw [hgeo]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          zero_add, show 2 * B * ε ^ 2 = ε ^ 2 * B * 2 by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_ofNat]

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.ShellA
section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

def shG {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) : V n :=
  WithLp.toLp 2 (fun i => g i (s y))

theorem shG_apply {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) (i : Fin n) :
    shG n g s y i = g i (s y) := rfl

theorem shG_norm_sq {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) :
    ‖shG n g s y‖ ^ 2 = ∑ i, ‖g i (s y)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rfl

theorem shG_contDiffOn {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) : ContDiffOn ℂ ∞ (shG n g e.symm) e.target := by
  rw [contDiffOn_euclidean]
  intro i
  exact contDiffOn_of_differentiableOn n _ _ e.open_target (hg i e he)

theorem sh_wd_eq (n : ℕ) (j : Fin n) (f : V n → ℂ) (y : V n) (hf : DifferentiableAt ℂ f y) :
    wd n j f y = fderiv ℂ f y (bas n j) := by
  have h := (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  rw [wd, h]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem sh_jac {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (y : V n) (hy : y ∈ e.target) :
    jac n z g (e.symm y) = LinearMap.det (fderiv ℂ (shG n g e.symm) y : V n →ₗ[ℂ] V n) := by
  have hd : DifferentiableAt ℂ (shG n g e.symm) y :=
    ((shG_contDiffOn n z g hg e he).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt
      (by simp)
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  unfold jac
  congr 1
  ext i k
  rw [Matrix.of_apply, d_comp_symm n z e he k (g i) y hy, LinearMap.toMatrix_apply]
  have hdi : DifferentiableAt ℂ (g i ∘ e.symm) y :=
    (hg i e he).differentiableAt (e.open_target.mem_nhds hy)
  rw [sh_wd_eq n k _ y hdi]
  have hcomp : HasFDerivAt (g i ∘ e.symm)
      ((EuclideanSpace.proj i : V n →L[ℂ] ℂ).comp (fderiv ℂ (shG n g e.symm) y)) y :=
    (EuclideanSpace.proj i : V n →L[ℂ] ℂ).hasFDerivAt.comp y hd.hasFDerivAt
  rw [hcomp.fderiv]
  simp [bas]

theorem sh_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (p : M) (hp : p ∈ zeroSet n g)
    (hJ : jac n z g p ≠ 0) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (hpe : p ∈ e.source) :
    ∃ ρ > 0, ball (e p) ρ ⊆ e.target ∧ InjOn (shG n g e.symm) (ball (e p) ρ) ∧
      ∀ ρ' > 0, ∃ κ > 0, ∀ y ∈ ball (e p) ρ, ‖shG n g e.symm y‖ < κ → y ∈ ball (e p) ρ' := by
  have hy0 : e p ∈ e.target := e.map_source hpe
  have hcd : ContDiffAt ℂ ∞ (shG n g e.symm) (e p) :=
    (shG_contDiffOn n z g hg e he).contDiffAt (e.open_target.mem_nhds hy0)
  have hdet : (fderiv ℂ (shG n g e.symm) (e p)).det ≠ 0 := by
    have h := sh_jac n z g hg e he (e p) hy0
    rw [e.left_inv hpe] at h
    rw [ContinuousLinearMap.det, ← h]
    exact hJ
  set f' := (fderiv ℂ (shG n g e.symm) (e p)).toContinuousLinearEquivOfDetNeZero hdet
  have hf' : HasFDerivAt (shG n g e.symm) (f' : V n →L[ℂ] V n) (e p) := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hcd.differentiableAt (by simp)).hasFDerivAt
  have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set Φ := hcd.toOpenPartialHomeomorph (shG n g e.symm) hf' hn0
  have hΦ : (Φ : V n → V n) = shG n g e.symm := rfl
  have hsrc : e p ∈ Φ.source := hcd.mem_toOpenPartialHomeomorph_source hf' hn0
  have htgt : shG n g e.symm (e p) ∈ Φ.target :=
    hcd.image_mem_toOpenPartialHomeomorph_target hf' hn0
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (e.open_target.inter Φ.open_source) (e p)
    ⟨hy0, hsrc⟩
  refine ⟨ρ, hρ, fun y hy => (hball hy).1, ?_, ?_⟩
  · rw [← hΦ]
    exact Φ.injOn.mono fun y hy => (hball hy).2
  intro ρ' hρ'
  have hG0 : shG n g e.symm (e p) = 0 := by
    ext i
    rw [shG_apply, e.left_inv hpe]
    exact hp i
  have hsymm : Φ.symm (shG n g e.symm (e p)) = e p := by
    rw [← hΦ]
    exact Φ.left_inv hsrc
  have hc : ContinuousAt Φ.symm (shG n g e.symm (e p)) := Φ.continuousAt_symm htgt
  have hmem : Φ.symm ⁻¹' ball (e p) ρ' ∈ 𝓝 (shG n g e.symm (e p)) :=
    hc.preimage_mem_nhds (by rw [hsymm]; exact ball_mem_nhds _ hρ')
  obtain ⟨κ, hκ, hκb⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨κ, hκ, fun y hy hGy => ?_⟩
  have h1 : shG n g e.symm y ∈ ball (shG n g e.symm (e p)) κ := by
    rw [hG0, mem_ball_zero_iff]
    exact hGy
  have h2 := hκb h1
  simp only [mem_preimage] at h2
  rwa [← hΦ, Φ.left_inv (hball hy).2] at h2

theorem sh_num (τ : ℝ) (hτ : 0 < τ) :
    Real.exp (min (τ / 10) (1 / 4)) * (Real.log 2 + 2 * min (τ / 10) (1 / 4)) ≤
      (1 + τ) * Real.log 2 := by
  set θ := min (τ / 10) (1 / 4) with hθ
  have h0 : 0 < θ := lt_min (by positivity) (by norm_num)
  have h1 : θ ≤ τ / 10 := min_le_left _ _
  have h2 : θ ≤ 1 / 4 := min_le_right _ _
  have hexp : Real.exp θ ≤ 1 + 2 * θ := by
    have := Real.exp_bound_div_one_sub_of_interval' h0 (by linarith)
    have h3 : 1 / (1 - θ) ≤ 1 + 2 * θ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hpos : 0 ≤ Real.log 2 + 2 * θ := by linarith
  calc Real.exp θ * (Real.log 2 + 2 * θ) ≤ (1 + 2 * θ) * (Real.log 2 + 2 * θ) :=
        mul_le_mul_of_nonneg_right hexp hpos
    _ ≤ (1 + τ) * Real.log 2 := by nlinarith

theorem sh_val (n j : ℕ) (S r a b : ℝ) (hS : 0 < S) (hr : 0 < r) :
    Real.exp (-b - ((n : ℝ) + j) * a) * (S * Real.exp (-a) / r ^ 2) ^ (-(n : ℝ)) =
      r ^ (2 * n) * Real.exp (-b - (j : ℝ) * a) * S ^ (-(n : ℝ)) := by
  have hX : 0 < Real.exp (-a) / r ^ 2 := by positivity
  rw [mul_div_assoc, Real.mul_rpow hS.le hX.le, Real.rpow_neg hX.le, Real.rpow_natCast,
    div_pow, ← Real.exp_nat_mul, pow_mul]
  have hE : Real.exp (-b - ((n : ℝ) + j) * a) =
      Real.exp (-b - (j : ℝ) * a) * Real.exp (↑n * -a) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hE]
  have h1 : 0 < Real.exp (↑n * -a) := Real.exp_pos _
  have h2 : 0 < (r ^ 2) ^ n := by positivity
  field_simp

end

end ReciprocityTheory.L2DbarEstimates.I
end

