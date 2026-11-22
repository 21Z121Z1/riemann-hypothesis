import Mathlib
import GroundTheory.AutomorphicForms.Bundle0003
import GroundTheory.AutomorphicForms.Bundle0002

-- bundled from GroundTheory.AutomorphicForms.HilbertSchmidtKernel
section
namespace GroundTheory.Automorphic.L2Kernel

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

section SlopeTestRemainingChoices

theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

theorem eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (μ : Measure α)
    (g : α → E) : eLpNorm g 2 μ ^ 2 = ∫⁻ a, ‖g a‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num [ENNReal.rpow_two]

theorem lt_top_of_sq_lt_top {a : ℝ≥0∞} (h : a ^ 2 < ∞) : a < ∞ := by
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_pow two_ne_zero] at h
  exact lt_irrefl _ h

end SlopeTestRemainingChoices

variable {𝕜 : Type*} [RCLike 𝕜]
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [SFinite μ] [SFinite ν]

section Kernel

def kernelFun (k : X × Y → 𝕜) (f : Y → 𝕜) (x : X) : 𝕜 := ∫ y, k (x, y) * f y ∂ν

variable (k : Lp 𝕜 2 (μ.prod ν))

theorem measurable_rowSq :
    Measurable fun x => ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν :=
  ((Lp.stronglyMeasurable k).measurable.enorm.pow_const 2).lintegral_prod_right'

theorem lintegral_rowSq : ∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∂μ = ‖k‖ₑ ^ 2 := by
  rw [← lintegral_prod _ ((Lp.stronglyMeasurable k).measurable.enorm.pow_const 2).aemeasurable,
    Lp.enorm_def, eLpNorm_two_sq]

theorem ae_rowSq_lt_top : ∀ᵐ x ∂μ, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν < ∞ := by
  refine ae_lt_top (measurable_rowSq k) ?_
  rw [lintegral_rowSq]
  exact (ENNReal.pow_lt_top enorm_lt_top).ne

theorem enorm_Lp_sq (f : Lp 𝕜 2 ν) : ‖f‖ₑ ^ 2 = ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν := by
  rw [Lp.enorm_def, eLpNorm_two_sq]

theorem measurable_row (x : X) : Measurable fun y => k (x, y) :=
  (Lp.stronglyMeasurable k).measurable.comp measurable_prodMk_left

theorem lintegral_row_mul_sq_le (x : X) (f : Lp 𝕜 2 ν) :
    (∫⁻ y, ‖k (x, y) * f y‖ₑ ∂ν) ^ 2 ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν) * ‖f‖ₑ ^ 2 := by
  simp only [enorm_mul]
  rw [enorm_Lp_sq]
  exact lintegral_mul_sq_le ν (measurable_row k x).enorm.aemeasurable
    (Lp.aestronglyMeasurable f).enorm

theorem enorm_kernelFun_sq_le (x : X) (f : Lp 𝕜 2 ν) :
    ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν) * ‖f‖ₑ ^ 2 :=
  (pow_le_pow_left₀ (by positivity) (enorm_integral_le_lintegral_enorm _) 2).trans
    (lintegral_row_mul_sq_le k x f)

theorem aestronglyMeasurable_kernelFun (f : Lp 𝕜 2 ν) :
    AEStronglyMeasurable (kernelFun (ν := ν) k f) μ :=
  ((Lp.aestronglyMeasurable k).mul (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'

theorem lintegral_kernelFun_sq_le (f : Lp 𝕜 2 ν) :
    ∫⁻ x, ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ∂μ ≤ ‖k‖ₑ ^ 2 * ‖f‖ₑ ^ 2 := by
  calc ∫⁻ x, ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν) * ‖f‖ₑ ^ 2 ∂μ :=
        lintegral_mono fun x => enorm_kernelFun_sq_le k x f
    _ = ‖k‖ₑ ^ 2 * ‖f‖ₑ ^ 2 := by
        rw [lintegral_mul_const _ (measurable_rowSq k), lintegral_rowSq]

theorem memLp_kernelFun (f : Lp 𝕜 2 ν) : MemLp (kernelFun (ν := ν) k f) 2 μ := by
  refine ⟨aestronglyMeasurable_kernelFun k f, lt_top_of_sq_lt_top ?_⟩
  rw [eLpNorm_two_sq]
  exact (lintegral_kernelFun_sq_le k f).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top enorm_lt_top) (ENNReal.pow_lt_top enorm_lt_top))

theorem ae_integrable_row_mul :
    ∀ᵐ x ∂μ, ∀ f : Lp 𝕜 2 ν, Integrable (fun y => k (x, y) * f y) ν := by
  filter_upwards [ae_rowSq_lt_top k] with x hx f
  refine ⟨(measurable_row k x).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f), ?_⟩
  refine lt_top_of_sq_lt_top ((lintegral_row_mul_sq_le k x f).trans_lt ?_)
  exact ENNReal.mul_lt_top hx (ENNReal.pow_lt_top enorm_lt_top)

def kernelOpₗ : Lp 𝕜 2 ν →ₗ[𝕜] Lp 𝕜 2 μ where
  toFun f := (memLp_kernelFun k f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_kernelFun k (f + g)).coeFn_toLp, (memLp_kernelFun k f).coeFn_toLp,
      (memLp_kernelFun k g).coeFn_toLp,
      Lp.coeFn_add ((memLp_kernelFun k f).toLp _) ((memLp_kernelFun k g).toLp _),
      ae_integrable_row_mul k] with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, kernelFun, kernelFun, kernelFun,
      ← integral_add (h5 f) (h5 g)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_kernelFun k (c • f)).coeFn_toLp, (memLp_kernelFun k f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_kernelFun k f).toLp _)] with x h1 h2 h3
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, kernelFun, kernelFun, smul_eq_mul,
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul, mul_left_comm]

theorem kernelOpₗ_apply_ae (f : Lp 𝕜 2 ν) :
    kernelOpₗ k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν :=
  (memLp_kernelFun k f).coeFn_toLp

theorem enorm_kernelOpₗ_sq (f : Lp 𝕜 2 ν) :
    ‖kernelOpₗ k f‖ₑ ^ 2 = ∫⁻ x, ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ∂μ := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (kernelOpₗ_apply_ae k f), eLpNorm_two_sq]
  rfl

theorem norm_kernelOpₗ_le (f : Lp 𝕜 2 ν) : ‖kernelOpₗ k f‖ ≤ ‖k‖ * ‖f‖ := by
  have h : ‖kernelOpₗ k f‖ₑ ^ 2 ≤ (‖k‖ₑ * ‖f‖ₑ) ^ 2 := by
    rw [enorm_kernelOpₗ_sq, mul_pow]
    exact lintegral_kernelFun_sq_le k f
  rw [ENNReal.pow_le_pow_left_iff two_ne_zero, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

def kernelOp : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ :=
  (kernelOpₗ k).mkContinuous ‖k‖ (norm_kernelOpₗ_le k)

theorem kernelOp_apply_ae (f : Lp 𝕜 2 ν) :
    kernelOp k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν :=
  kernelOpₗ_apply_ae k f

theorem exists_row {x : X} (hx : ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν < ∞) :
    ∃ h : Lp 𝕜 2 ν, ‖h‖ₑ ^ 2 = ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∧
      ∀ f : Lp 𝕜 2 ν, kernelFun (ν := ν) k f x = ⟪h, f⟫_𝕜 := by
  have hconj : ∀ y, ‖conj (k (x, y))‖ₑ = ‖k (x, y)‖ₑ := fun y => by
    rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]
  have hm : MemLp (fun y => conj (k (x, y))) 2 ν := by
    refine ⟨(RCLike.continuous_conj.comp_aestronglyMeasurable
      (measurable_row k x).aestronglyMeasurable), lt_top_of_sq_lt_top ?_⟩
    rw [eLpNorm_two_sq]
    simpa only [hconj] using hx
  refine ⟨hm.toLp _, ?_, fun f => ?_⟩
  · rw [Lp.enorm_def, eLpNorm_congr_ae hm.coeFn_toLp, eLpNorm_two_sq]
    simp only [hconj]
  · rw [MeasureTheory.L2.inner_def, kernelFun]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with y hy
    rw [RCLike.inner_apply, hy, RCLike.conj_conj, mul_comm]

theorem hsNormSq_kernelOp_le : hsNormSq (kernelOp k) ≤ ‖k‖ₑ ^ 2 := by
  let b := stdHilbertBasis 𝕜 (Lp 𝕜 2 ν)
  rw [hsNormSq]
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  calc ∑ i ∈ s, ‖kernelOp k (b i)‖ₑ ^ 2
      = ∑ i ∈ s, ∫⁻ x, ‖kernelFun (ν := ν) k (b i) x‖ₑ ^ 2 ∂μ :=
        Finset.sum_congr rfl fun i _ => enorm_kernelOpₗ_sq k (b i)
    _ = ∫⁻ x, ∑ i ∈ s, ‖kernelFun (ν := ν) k (b i) x‖ₑ ^ 2 ∂μ :=
        (lintegral_finsetSum' s fun i _ =>
          ((aestronglyMeasurable_kernelFun k (b i)).enorm.pow_const 2)).symm
    _ ≤ ∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_rowSq_lt_top k] with x hx
        obtain ⟨h, hh, hK⟩ := exists_row k hx
        calc ∑ i ∈ s, ‖kernelFun (ν := ν) k (b i) x‖ₑ ^ 2
            = ∑ i ∈ s, ‖⟪b i, h⟫_𝕜‖ₑ ^ 2 :=
              Finset.sum_congr rfl fun i _ => by rw [hK, enorm_inner_comm]
          _ ≤ ∑' i, ‖⟪b i, h⟫_𝕜‖ₑ ^ 2 := ENNReal.sum_le_tsum s
          _ = ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν := by rw [← enorm_sq_eq_tsum b, hh]
    _ = ‖k‖ₑ ^ 2 := lintegral_rowSq k

theorem kernelOp_isHilbertSchmidt : IsHilbertSchmidt (kernelOp k) :=
  (hsNormSq_kernelOp_le k).trans_lt (ENNReal.pow_lt_top enorm_lt_top)

end Kernel

theorem kernelOp_toLp_apply_ae {k : X × Y → 𝕜} (hk : MemLp k 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    kernelOp (hk.toLp k) f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν := by
  filter_upwards [kernelOp_apply_ae (hk.toLp k) f, Measure.ae_ae_of_ae_prod hk.coeFn_toLp] with x h1 h2
  rw [h1]
  refine integral_congr_ae ?_
  filter_upwards [h2] with y hy
  rw [hy]

end

end GroundTheory.Automorphic.L2Kernel
end

-- bundled from GroundTheory.AutomorphicForms.LocallyConstantCompact
section
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology
open scoped Pointwise

section Space

variable (X : Type*) [TopologicalSpace X] (R E : Type*) [Semiring R] [AddCommMonoid E]
  [Module R E]

def locallyConstantCompactSupport : Submodule R (X → E) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' {f g} hf hg := ⟨hf.1.comp₂ hg.1 (· + ·), hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c f hf := ⟨hf.1.comp (c • ·), hf.2.mono fun x hx => by
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])⟩

variable {X R E}

theorem mem_locallyConstantCompactSupport {f : X → E} :
    f ∈ locallyConstantCompactSupport X R E ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

theorem indicator_mem_locallyConstantCompactSupport [T2Space X] {U : Set X} (hc : IsCompact U)
    (ho : IsOpen U) (e : E) :
    U.indicator (fun _ => e) ∈ locallyConstantCompactSupport X R E := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const X e) ⟨hc.isClosed, ho⟩).isLocallyConstant

theorem range_finite_of_mem_locallyConstantCompactSupport {f : X → E}
    (hf : f ∈ locallyConstantCompactSupport X R E) : (range f).Finite := by
  have : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2
  have h1 : (range fun x : tsupport f => f x).Finite :=
    (hf.1.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport f
  · exact mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact mem_insert _ _

theorem isCompact_isOpen_fiber {f : X → E} (hf : f ∈ locallyConstantCompactSupport X R E)
    {v : E} (hv : v ≠ 0) : IsCompact {x | f x = v} ∧ IsOpen {x | f x = v} := by
  refine ⟨hf.2.of_isClosed_subset (hf.1.isClosed_fiber v) fun x hx => ?_, hf.1.isOpen_fiber v⟩
  refine subset_tsupport f ?_
  have hx : f x = v := hx
  simp [Function.mem_support, hx, hv]

end Space

section Group

variable {G : Type*} [Group G] {E : Type*}

theorem mk_eq_iff_mem_out_smul (K : Subgroup G) (x : G ⧸ K) (y : G) :
    (y : G ⧸ K) = x ↔ y ∈ x.out • (K : Set G) := by
  conv_lhs => rw [← QuotientGroup.out_eq' x]
  rw [eq_comm, QuotientGroup.eq, mem_leftCoset_iff, SetLike.mem_coe]

theorem apply_eq_of_mem_smul {K : Subgroup G} {f : G → E}
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) {g y : G} (hy : y ∈ g • (K : Set G)) : f y = f g := by
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hy
  exact hK g k hk

variable [TopologicalSpace G] [IsTopologicalGroup G] {R : Type*} [Semiring R] [AddCommMonoid E]
  [Module R E]

theorem mem_locallyConstantCompactSupport_of_forall_mul_right (K : OpenSubgroup G)
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f ∈ locallyConstantCompactSupport G R E := by
  refine ⟨(IsLocallyConstant.iff_exists_open f).2 fun g => ?_, hf⟩
  refine ⟨g • (K : Set G), K.isOpen.smul g, ?_, fun y hy => apply_eq_of_mem_smul hK hy⟩
  exact Set.mem_smul_set.2 ⟨1, K.one_mem, mul_one g⟩

theorem finite_image_mk_tsupport (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f) :
    (QuotientGroup.mk '' tsupport f : Set (G ⧸ (K : Subgroup G))).Finite :=
  (hf.image QuotientGroup.continuous_mk).finite_of_discrete

theorem eq_sum_indicator_coset (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f)
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f = ∑ x ∈ (finite_image_mk_tsupport K hf).toFinset,
      (x.out • (K : Set G)).indicator (fun _ => f x.out) := by
  classical
  funext y
  rw [Finset.sum_apply]
  by_cases hy : (y : G ⧸ (K : Subgroup G)) ∈ (finite_image_mk_tsupport K hf).toFinset
  · rw [Finset.sum_eq_single (y : G ⧸ (K : Subgroup G))]
    · have hmem : y ∈ (y : G ⧸ (K : Subgroup G)).out • (K : Set G) :=
        (mk_eq_iff_mem_out_smul (K : Subgroup G) _ y).1 rfl
      rw [Set.indicator_of_mem hmem]
      exact apply_eq_of_mem_smul hK hmem
    · intro b _ hb
      exact Set.indicator_of_notMem
        (fun h => hb ((mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h).symm) _
    · intro h
      exact absurd hy h
  · rw [Finset.sum_eq_zero]
    · by_contra h
      exact hy ((Set.Finite.mem_toFinset _).2 ⟨y, subset_tsupport f h, rfl⟩)
    · intro b hb
      refine Set.indicator_of_notMem (fun h => hy ?_) _
      rwa [(mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h]

variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem exists_forall_mul_right {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ g, ∀ k ∈ K, f (g * k) = f g := by
  let W : Set (G × G) := {p | f (p.1 * p.2) = f p.1}
  have hW : IsOpen W := by
    have hF : IsLocallyConstant fun p : G × G => (f (p.1 * p.2), f p.1) :=
      (hf.1.comp_continuous continuous_mul).prodMk (hf.1.comp_continuous continuous_fst)
    exact hF {q | q.1 = q.2}
  have hsub : tsupport f ×ˢ ({1} : Set G) ⊆ W := by
    rintro ⟨g, k⟩ ⟨-, hk⟩
    simp only [mem_singleton_iff] at hk
    simp [W, hk]
  obtain ⟨u, v, -, hv, hSu, h1v, huv⟩ := generalized_tube_lemma hf.2 isCompact_singleton hW hsub
  obtain ⟨K, hKc, hKv⟩ := exists_openSubgroup_isCompact_subset (hv.mem_nhds (h1v rfl))
  have key : ∀ s ∈ tsupport f, ∀ k ∈ K, f (s * k) = f s := fun s hs k hk =>
    huv (show (s, k) ∈ u ×ˢ v from ⟨hSu hs, hKv hk⟩)
  refine ⟨K, hKc, fun g k hk => ?_⟩
  by_cases hg : g ∈ tsupport f
  · exact key g hg k hk
  · rw [image_eq_zero_of_notMem_tsupport hg]
    by_contra h
    have := key (g * k) (subset_tsupport f h) k⁻¹ (inv_mem hk)
    rw [mul_inv_cancel_right, image_eq_zero_of_notMem_tsupport hg] at this
    exact h this.symm

theorem exists_forall_mul_left {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, ∀ g, f (k * g) = f g := by
  have hf' : (fun g => f g⁻¹) ∈ locallyConstantCompactSupport G R E :=
    ⟨hf.1.comp_continuous continuous_inv, hf.2.comp_homeomorph (Homeomorph.inv G)⟩
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_right hf'
  refine ⟨K, hKc, fun k hk g => ?_⟩
  have := hK g⁻¹ k⁻¹ (inv_mem hk)
  simpa [mul_inv_rev] using this

theorem exists_forall_mul_left_mul_right {f : G → E}
    (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      ∀ k ∈ K, ∀ g, ∀ k' ∈ K, f (k * g * k') = f g := by
  obtain ⟨K₁, h₁, hK₁⟩ := exists_forall_mul_right hf
  obtain ⟨K₂, -, hK₂⟩ := exists_forall_mul_left hf
  refine ⟨K₁ ⊓ K₂, isCompact_inf_left h₁, fun k hk g k' hk' => ?_⟩
  rw [mul_assoc, hK₂ k (OpenSubgroup.mem_inf.1 hk).2, hK₁ g k' (OpenSubgroup.mem_inf.1 hk').1]

end Group

end GroundTheory.Automorphic
end
end

