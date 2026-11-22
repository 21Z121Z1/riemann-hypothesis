import Mathlib
import GroundTheory.AutomorphicForms.QuotientKernel
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
import GroundTheory.AutomorphicForms.Bundle0011
import GroundTheory.AutomorphicForms.DixmierMalliavinLine
import GroundTheory.AutomorphicForms.Bundle0012
import GroundTheory.AutomorphicForms.HeckeAlgebra
import GroundTheory.AutomorphicForms.KernelTrace

-- bundled from GroundTheory.AutomorphicForms.DiscreteDecomposition
section
open MeasureTheory

namespace GroundTheory.Automorphic

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isCompactOperator_integrated (f : CompactlySupportedContinuousMap G ℂ) :
    IsCompactOperator ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) :=
  isCompactOperator_integrated_rightRegularRep Γ μ f

theorem exists_isHilbertSum_isIrreducible_finite :
    ∃ s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))),
      ∃ _ : ∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))),
      ∃ hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V,
      IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
        (fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ) ∧
      (∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible) ∧
      ∀ {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        (σ : UnitaryRep G K), σ.IsIrreducible →
          {V : s | ((rightRegularRep Γ μ).restrict V (hinv V)).IsEquivalent σ}.Finite := by
  have hcpt := isCompactOperator_integrated Γ μ
  obtain ⟨s, hcomp, hinv, hsum, hirr⟩ := UnitaryRep.exists_isHilbertSum_isIrreducible hcpt
  exact ⟨s, hcomp, hinv, hsum, hirr, fun σ hσ =>
    UnitaryRep.finite_setOf_isEquivalent hcpt hinv hsum.OrthogonalFamily hσ⟩

theorem finiteDimensional_intertwiners {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {σ : UnitaryRep G K} (hσ : σ.IsIrreducible) :
    FiniteDimensional ℂ (σ.intertwiners (rightRegularRep Γ μ)) :=
  UnitaryRep.finiteDimensional_intertwiners (isCompactOperator_integrated Γ μ) hσ

end RightCosetSpace

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavin
section
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_decomp_direction {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f₁ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f₁) ∧
      HasCompactSupport f₁ ∧
      ∃ g k : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ k ∧ tsupport g ⊆ Icc (-ε) ε ∧
        tsupport k ⊆ Icc (-ε) ε ∧
        ∀ x, f x = (∫ t, g t * f₁ (h.expG (t • X) * x)) + ∫ t, k t * f (h.expG (t • X) * x) := by
  obtain ⟨M, hM, hser⟩ := h.exists_bound_dirDeriv hf hfc X
  obtain ⟨c, g, k, hg, hk, hgs, hks, hc, hid⟩ := exists_dixmierMalliavin_line M hε
  obtain ⟨hf₁, hf₁c⟩ := hser c hc
  refine ⟨_, hf₁, hf₁c, g, k, hg, hk, hgs, hks, fun x => ?_⟩
  set F : ℝ → ℂ := fun t => f (h.expG (t • X) * x) with hFdef
  have hF : ContDiff ℝ ∞ F := h.contDiff_comp_expG_smul_mul hf X x
  have hD : ∀ p t, iteratedDeriv p F t = h.dirDeriv X p f (h.expG (t • X) * x) :=
    fun p t => h.iteratedDeriv_comp_expG_mul X p f x t
  have key := hid F hF (fun p t _ => by rw [hD]; exact hM p _)
  have hF0 : F 0 = f x := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero, one_mul]
  rw [hF0] at key
  rw [key]
  congr 1
  · have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    have hcont : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * g t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcont p).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * ‖g t‖ := by
      intro p t
      simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_assoc (|c p|)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (c p))
      have : ‖iteratedDeriv p F t‖ ≤ M p := by rw [hD]; exact hM p _
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hgi : Integrable (fun t => ‖g t‖) :=
      (hg.continuous.integrable_of_hasCompactSupport hgc).norm
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, ‖g t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e1 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e1]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    simp only [T, hD]
    rw [← tsum_mul_left]
    congr 1
    funext p
    ring
  · congr 1; funext t; rw [mul_comm]

theorem exists_decomp_iter {ε : ℝ} (hε : 0 < ε) : ∀ {d : ℕ} (X : Fin d → 𝔤) (f : G → ℂ),
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) → HasCompactSupport f →
    ∃ (m : ℕ) (F : Fin m → G → ℂ) (K : Fin m → (Fin d → ℝ) → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (F i)) ∧
        HasCompactSupport (F i)) ∧
      (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ x, f x = ∑ i, ∫ t, K i t * F i (h.revProdExp X t * x)
  | 0, X, f, hf, hfc => by
    refine ⟨1, fun _ => f, fun _ _ => 1, fun _ => ⟨hf, hfc⟩, fun _ => ⟨contDiff_const, ?_⟩,
      fun x => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [h.revProdExp_zero, hv]
  | d + 1, X, f, hf, hfc => by
    let := h.chartedSpace
    obtain ⟨f₁, hf₁, hf₁c, g, k, hg, hk, hgs, hks, hdec⟩ :=
      h.exists_decomp_direction hf hfc (X 0) hε
    obtain ⟨m₁, F₁, K₁, hF₁, hK₁, hd₁⟩ := exists_decomp_iter hε (Fin.tail X) f₁ hf₁ hf₁c
    obtain ⟨m₂, F₂, K₂, hF₂, hK₂, hd₂⟩ := exists_decomp_iter hε (Fin.tail X) f hf hfc
    refine ⟨m₁ + m₂, Fin.append F₁ F₂,
      Fin.append (fun i t => g (t 0) * K₁ i (Fin.tail t)) (fun i t => k (t 0) * K₂ i (Fin.tail t)),
      ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hF₁ i
      · simpa only [Fin.append_right] using hF₂ i
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨contDiff_cons_kernel hg (hK₁ i).1, tsupport_cons_kernel hε.le hgs (hK₁ i).2⟩
      · simp only [Fin.append_right]
        exact ⟨contDiff_cons_kernel hk (hK₂ i).1, tsupport_cons_kernel hε.le hks (hK₂ i).2⟩
    · intro x
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec x]
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le hg.continuous hgs (fun i => (hK₁ i).1.continuous)
          (fun i => (hK₁ i).2) (fun i => (hF₁ i).1.continuous) hd₁ x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hk.continuous hks (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => (hF₂ i).1.continuous) hd₂ x).symm

end IsExpLieAlgebra

theorem dixmierMalliavin (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ)
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (hfc : HasCompactSupport f) :
    ∃ (n : ℕ) (φ ψ : Fin n → G → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (φ i)) ∧
        HasCompactSupport (φ i) ∧
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧ HasCompactSupport (ψ i)) ∧
      f = ∑ i, groupConv μ (φ i) (ψ i) := by
  let := h.chartedSpace
  let b := Module.finBasis ℝ 𝔤
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp μ b
  obtain ⟨m, F, K, hF, hK, hd⟩ := h.exists_decomp_iter hε (⇑b) f hf hfc
  have hK' : ∀ i, ContDiff ℝ ∞ (fun t => K i (-t)) ∧
      tsupport (fun t => K i (-t)) ⊆ Metric.closedBall 0 ε := by
    intro i
    refine ⟨(hK i).1.comp contDiff_neg, ?_⟩
    intro t ht
    have : -t ∈ tsupport (K i) := by
      have := tsupport_comp_subset_preimage (K i) (f := fun t : Fin _ → ℝ => -t) continuous_neg ht
      simpa using this
    have := (hK i).2 this
    simpa [mem_closedBall_zero_iff, norm_neg] using this
  choose κ hκs hκc hκ using fun i => hdens (fun t => K i (-t)) (hK' i).1 (hK' i).2
  refine ⟨m, κ, F, fun i => ⟨hκs i, hκc i, (hF i).1, (hF i).2⟩, ?_⟩
  funext x
  rw [hd x, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [groupConv, hκ i (fun y => F i (y⁻¹ * x))
    ((hF i).1.continuous.comp (continuous_inv.mul continuous_const))]
  have e : ∀ t : Fin (Module.finrank ℝ 𝔤) → ℝ, K i (-t) * F i ((h.prodExp (⇑b) t)⁻¹ * x) =
      (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) (-t) := by
    intro t
    have := h.revProdExp_inv (⇑b) (-t)
    rw [neg_neg] at this
    simp only [← this, inv_inv]
  simp_rw [e]
  exact (integral_neg_eq_self (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) volume).symm

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.KernelTraceComp
section
namespace GroundTheory.Automorphic

open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal

noncomputable section

section Uniform

variable {X : Type*} [UniformSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem continuous_integral_mul_of_uniformSpace (a b : C(X × X, ℂ)) :
    Continuous fun z : X × X => ∫ y, a (z.1, y) * b (y, z.2) ∂μ := by
  refine UniformContinuous.continuous ?_
  refine (Metric.uniformity_basis_dist.tendsto_right_iff).2 fun ε hε => ?_
  set A := ‖a‖
  set B := ‖b‖
  set M := μ.real univ
  set δ : ℝ := ε / ((A + B) * M + 1)
  have hδ : 0 < δ := by positivity
  obtain ⟨u₁, hu₁, v₁, hv₁, h₁⟩ := entourageProd_subset
    (CompactSpace.uniformContinuous_of_continuous a.continuous (Metric.dist_mem_uniformity hδ))
  obtain ⟨u₂, hu₂, v₂, hv₂, h₂⟩ := entourageProd_subset
    (CompactSpace.uniformContinuous_of_continuous b.continuous (Metric.dist_mem_uniformity hδ))
  filter_upwards [entourageProd_mem_uniformity hu₁ hv₂] with w hw
  obtain ⟨⟨x, z⟩, ⟨x', z'⟩⟩ := w
  obtain ⟨hx, hz⟩ := hw
  change dist (∫ y, a (x, y) * b (y, z) ∂μ) (∫ y, a (x', y) * b (y, z') ∂μ) < ε
  have hrowa : ∀ x, Continuous fun y => a (x, y) := fun x =>
    a.continuous.comp (continuous_const.prodMk continuous_id)
  have hcolb : ∀ z, Continuous fun y => b (y, z) := fun z =>
    b.continuous.comp (continuous_id.prodMk continuous_const)
  have hint : ∀ x z, Integrable (fun y => a (x, y) * b (y, z)) μ := fun x z =>
    integrable_of_continuous_compact ((hrowa x).mul (hcolb z)) μ
  rw [dist_eq_norm, ← integral_sub (hint x z) (hint x' z')]
  have hpt : ∀ y, ‖a (x, y) * b (y, z) - a (x', y) * b (y, z')‖ ≤ δ * B + A * δ := by
    intro y
    have ha : ‖a (x, y) - a (x', y)‖ < δ := by
      rw [← dist_eq_norm]
      exact h₁ (show ((x, y), (x', y)) ∈ entourageProd u₁ v₁ from ⟨hx, refl_mem_uniformity hv₁⟩)
    have hb : ‖b (y, z) - b (y, z')‖ < δ := by
      rw [← dist_eq_norm]
      exact h₂ (show ((y, z), (y, z')) ∈ entourageProd u₂ v₂ from ⟨refl_mem_uniformity hu₂, hz⟩)
    have e : a (x, y) * b (y, z) - a (x', y) * b (y, z') =
        (a (x, y) - a (x', y)) * b (y, z) + a (x', y) * (b (y, z) - b (y, z')) := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul ha.le (b.norm_coe_le_norm _) (norm_nonneg _) hδ.le
    · rw [norm_mul]
      exact mul_le_mul (a.norm_coe_le_norm _) hb.le (norm_nonneg _) (norm_nonneg _)
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ hpt)).trans_lt ?_
  have hM : 0 ≤ M := measureReal_nonneg
  have hAB : 0 ≤ A + B := by positivity
  have e : (δ * B + A * δ) * M = ε * ((A + B) * M / ((A + B) * M + 1)) := by
    simp only [δ]; field_simp; ring
  rw [e]
  have : (A + B) * M / ((A + B) * M + 1) < 1 := (div_lt_one (by positivity)).2 (lt_add_one _)
  nlinarith

end Uniform

section Comp

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def compKernel (a b : C(X × X, ℂ)) : C(X × X, ℂ) where
  toFun z := ∫ y, a (z.1, y) * b (y, z.2) ∂μ
  continuous_toFun := by
    let _ : UniformSpace X := uniformSpaceOfCompactR1
    exact continuous_integral_mul_of_uniformSpace μ a b

theorem compKernel_apply (a b : C(X × X, ℂ)) (z : X × X) :
    compKernel μ a b z = ∫ y, a (z.1, y) * b (y, z.2) ∂μ := rfl

theorem contKernelOp_comp (a b : C(X × X, ℂ)) :
    (contKernelOp μ a).comp (contKernelOp μ b) = contKernelOp μ (compKernel μ a b) := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [contKernelOp_apply_ae μ a (contKernelOp μ b f),
    contKernelOp_apply_ae μ (compKernel μ a b) f] with x h1 h2
  rw [ContinuousLinearMap.comp_apply, h1, h2]
  have h3 : (fun y => a (x, y) * contKernelOp μ b f y) =ᵐ[μ]
      fun y => ∫ z, a (x, y) * (b (y, z) * f z) ∂μ := by
    filter_upwards [contKernelOp_apply_ae μ b f] with y hy
    rw [hy, integral_const_mul]
  rw [integral_congr_ae h3]
  have hf : Integrable (fun z => f z) μ := (Lp.memLp f).integrable one_le_two
  have hab : Continuous fun p : X × X => a (x, p.1) * b (p.1, p.2) :=
    (a.continuous.comp (continuous_const.prodMk continuous_fst)).mul b.continuous
  have hint : Integrable (Function.uncurry fun y z => a (x, y) * (b (y, z) * f z)) (μ.prod μ) := by
    have h1 : Integrable (fun p : X × X => (1 : ℂ) * f p.2) (μ.prod μ) :=
      (integrable_const (1 : ℂ)).mul_prod hf
    have h2 := h1.bdd_mul (c := ‖a‖ * ‖b‖)
      (measurable_of_continuous_compactProd hab).aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [norm_mul]
        exact mul_le_mul (a.norm_coe_le_norm _) (b.norm_coe_le_norm _) (norm_nonneg _)
          (norm_nonneg _))
    refine h2.congr (ae_of_all _ fun p => ?_)
    obtain ⟨y, z⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [compKernel_apply]
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  ring

end Comp

end

end GroundTheory.Automorphic
end

