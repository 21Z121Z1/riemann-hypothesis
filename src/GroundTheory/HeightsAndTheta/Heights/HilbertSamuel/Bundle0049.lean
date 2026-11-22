import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageHilb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageHilb

section Subst

variable {σ τ M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']

theorem isWeightedHomogeneous_aeval {w : σ → M} {w' : τ → M'} (ψ : M →+ M') (φ : σ → MvPolynomial τ ℚ)
    (hφ : ∀ i, IsWeightedHomogeneous w' (φ i) (ψ (w i))) {f : MvPolynomial σ ℚ} {m : M}
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w' (aeval φ f) (ψ m) := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero ℚ w' (ψ m)
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial d r hr =>
    rw [aeval_monomial, algebraMap_eq, ← hr, Finsupp.weight_apply, map_finsuppSum]
    refine IsWeightedHomogeneous.C_mul ?_ r
    simp only [map_nsmul]
    exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (hφ i).pow (d i)

end Subst

section Cone

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]

def mConeMapQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1

def valSpan {σ M : Type*} [AddCommMonoid M] (w : σ → M) (y : σ → Ω) (m : M) : Submodule ℚ Ω :=
  (weightedHomogeneousSubmodule ℚ w m).map (aeval y : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toLinearMap

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem map_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = RingHom.ker (mConeMapQ y) := by
  have hring : ((mConeMapQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMapQ, mConeMap]
    · intro i
      simp [mConeMapQ, mConeMap]
  have hker : mCoordIdeal y = (RingHom.ker (mConeMapQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [mCoordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))
    (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (mConeMapQ y))
  rw [e] at h
  rw [hker]
  exact h

theorem weight_blockWeight_apply (μ : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) μ k = ∑ i : ι k, μ ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem mConeMapQ_eq (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    mConeMapQ y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hf (mem_support_iff.mp hμ)]
  simp only [mConeMapQ, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem hilbFn_eq_finrank (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => (a k : ℤ)) =
      Module.finrank ℚ (valSpan (NumbersDVR.blockWeight ι) y a) := by
  rw [map_mCoordIdeal]
  set W := weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a
  set P := RingHom.ker (mConeMapQ y)
  let φ₁ : W →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P := (Ideal.Quotient.mkₐ ℚ P).toLinearMap ∘ₗ W.subtype
  let φ₂ : W →ₗ[ℚ] Ω := (aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap ∘ₗ W.subtype
  have hk : LinearMap.ker φ₁ = LinearMap.ker φ₂ := by
    ext ⟨f, hf⟩
    simp only [LinearMap.mem_ker, φ₁, φ₂, LinearMap.comp_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, P, RingHom.mem_ker]
    rw [mConeMapQ_eq y hf, mul_eq_zero, C_eq_zero,
      or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))]
  have h₁ : LinearMap.range φ₁ = NumbersDVR.gradedPiece P a := by
    simp only [φ₁, LinearMap.range_comp, Submodule.range_subtype, NumbersDVR.gradedPiece, W]
  have h₂ : LinearMap.range φ₂ = valSpan (NumbersDVR.blockWeight ι) y a := by
    simp only [φ₂, LinearMap.range_comp, Submodule.range_subtype, valSpan, W]
  have h := LinearEquiv.finrank_eq
    ((φ₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans φ₂.quotKerEquivRange)
  rw [h₁, h₂] at h
  unfold NumbersDVR.hilbFn
  rw [if_pos (fun k => Nat.cast_nonneg _)]
  show ((Module.finrank ℚ (NumbersDVR.gradedPiece P a) : ℕ) : ℤ) = _
  rw [h]

end Cone

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω] {κ : Type} [Fintype κ]

def fwdSubst (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (j : Ix κ) : MvPolynomial (Σ k, ι k) ℚ :=
  ∑ i, MvPolynomial.C ((M j i : ℤ) : ℚ) * MvPolynomial.X ⟨k₀, i⟩

def backSubst (k₀ : K) (N : Matrix (ι k₀) (Ix κ) ℤ) : (Σ k, ι k) → MvPolynomial (Ix κ) ℚ
  | ⟨k, i⟩ => if h : k = k₀ then ∑ j, MvPolynomial.C ((N (h ▸ i) j : ℤ) : ℚ) * MvPolynomial.X j else 0

theorem valSpan_eq {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ} {N : Matrix (ι k₀) (Ix κ) ℤ}
    {x : Ix κ → Ω} (hxy : IsBlockImage y k₀ M N x) (n : ℕ) :
    valSpan (NumbersDVR.blockWeight (GlobalTheory κ)) x (fun _ => n) = valSpan (NumbersDVR.blockWeight ι) y (Pi.single k₀ n) := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    let ψ : (Unit → ℕ) →+ (K → ℕ) :=
      { toFun := fun a => Pi.single k₀ (a ()), map_zero' := by simp, map_add' := fun a b => by simp [Pi.single_add] }
    have hφ : ∀ j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (fwdSubst k₀ M j)
        (ψ (NumbersDVR.blockWeight (GlobalTheory κ) j)) := fun j => by
      have e : ψ (NumbersDVR.blockWeight (GlobalTheory κ) j) = Pi.single k₀ 1 := by
        simp [ψ, NumbersDVR.blockWeight]
      rw [e]
      exact IsWeightedHomogeneous.sum _ _ _ fun i _ =>
        (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight ι) ⟨k₀, i⟩).C_mul _
    refine ⟨aeval (fwdSubst k₀ M) f, ?_, ?_⟩
    · simpa [ψ] using isWeightedHomogeneous_aeval ψ _ hφ hf
    · simp only [AlgHom.toLinearMap_apply]
      have e : (fun j => aeval y (fwdSubst k₀ M j)) = x := by
        funext j
        simp [fwdSubst, hxy.1 j]
      rw [← AlgHom.comp_apply, comp_aeval, e]
  · rintro _ ⟨g, hg, rfl⟩
    let ψ : (K → ℕ) →+ (Unit → ℕ) :=
      { toFun := fun a _ => ∑ k, a k, map_zero' := by ext; simp,
        map_add' := fun a b => by ext; simp [Finset.sum_add_distrib] }
    have hφ : ∀ p, IsWeightedHomogeneous (NumbersDVR.blockWeight (GlobalTheory κ)) (backSubst k₀ N p)
        (ψ (NumbersDVR.blockWeight ι p)) := by
      rintro ⟨k, i⟩
      have e : ψ (NumbersDVR.blockWeight ι ⟨k, i⟩) = fun _ => 1 := by
        funext u
        simp [ψ, NumbersDVR.blockWeight]
      rw [e]
      by_cases h : k = k₀
      · subst h
        simp only [backSubst, dite_true]
        refine IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_
        convert (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight (GlobalTheory κ)) j).C_mul _ using 1
        funext u
        simp [NumbersDVR.blockWeight]
      · simp only [backSubst, h, dite_false]
        exact isWeightedHomogeneous_zero ℚ _ _
    refine ⟨aeval (backSubst k₀ N) g, ?_, ?_⟩
    · simpa [ψ] using isWeightedHomogeneous_aeval ψ _ hφ hg
    · simp only [AlgHom.toLinearMap_apply]
      rw [← AlgHom.comp_apply, comp_aeval]
      refine hom_congr_vars (Subsingleton.elim _ _) (fun p hp _ => ?_) rfl
      obtain ⟨k, i⟩ := p
      obtain ⟨μ, hμ, hp⟩ := (mem_vars_iff_mem_support _).mp hp
      by_cases h : k = k₀
      · subst h
        simp [backSubst, hxy.2 i]
      · exfalso
        have hw := congrFun (hg (mem_support_iff.mp hμ)) k
        rw [weight_blockWeight_apply, Pi.single_eq_of_ne h] at hw
        have := Finset.single_le_sum (fun i' _ => Nat.zero_le (μ ⟨k, i'⟩)) (Finset.mem_univ i)
        rw [hw] at this
        exact (Finsupp.mem_support_iff.mp hp) (Nat.le_zero.mp this)

end Block

end BlockImageHilb

open BlockImageHilb in

theorem BlockImageHilb.proof : BlockImageHilb.Statement := by
  intro K _ _ ι _ Ω _ _ κ _ y k₀ M N x hxy n
  rw [coordIdeal_eq_mCoordIdeal]
  have e : (fun k => if k = k₀ then (n : ℤ) else 0) = fun k => ((Pi.single k₀ n : K → ℕ) k : ℤ) := by
    funext k
    by_cases h : k = k₀
    · subst h; simp
    · simp [h]
  rw [e, hilbFn_eq_finrank y (Pi.single k₀ n), ← valSpan_eq hxy n]
  exact hilbFn_eq_finrank (ι := GlobalTheory κ) x (fun _ => n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionImageSup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Set Filter Topology

noncomputable section

namespace BlockResolutionImageSup

theorem analyticOnNhd_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*} {V : Set E}
    {g : E → σ → ℂ} (hg : ∀ i, AnalyticOnNhd ℂ (fun w => g w i) V) (f : MvPolynomial σ ℂ) :
    AnalyticOnNhd ℂ (fun w => eval (g w) f) V := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : E => a) V)
  | add p q hp hq => exact fun w hw => by simpa using (hp w hw).fun_add (hq w hw)
  | mul_X p i hp => exact fun w hw => by simpa using (hp w hw).fun_mul (hg i w hw)

theorem sq_div_pow_eq {a r : ℝ} (hr : 0 < r) (n : ℕ) :
    (a / r ^ n) ^ 2 = a ^ 2 * Real.exp (-(n : ℝ) * (2 * Real.log r)) := by
  have h : Real.exp (-(n : ℝ) * (2 * Real.log r)) = ((r ^ n) ^ 2)⁻¹ := by
    rw [show -(n : ℝ) * (2 * Real.log r) = -Real.log ((r ^ n) ^ 2) by
      rw [Real.log_pow, Real.log_pow]; push_cast; ring, Real.exp_neg, Real.exp_log (by positivity)]
  rw [h, div_pow, div_eq_mul_inv]

theorem lintegral_chart_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {e : ℕ}
    (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (μ : Measure X) {ν : (Fin e → ℂ) → ℝ}
    (hν : ContinuousOn ν φ.target)
    (hμ : ∀ S : Set X, MeasurableSet S → S ⊆ φ.source →
      μ S = ∫⁻ y in φ.target ∩ φ.symm ⁻¹' S, ENNReal.ofReal (ν y))
    {g : X → ENNReal} (hg : Measurable g) :
    ∫⁻ z in φ.target, ENNReal.ofReal (ν z) * g (φ.symm z) ≤ ∫⁻ y, g y ∂μ := by
  have hT : MeasurableSet φ.target := φ.open_target.measurableSet
  have hs : AEMeasurable φ.symm (volume.restrict φ.target) := φ.continuousOn_symm.aemeasurable hT
  have hνm : AEMeasurable (fun z => ENNReal.ofReal (ν z)) (volume.restrict φ.target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hν.aemeasurable hT)
  have hs' : AEMeasurable φ.symm
      ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) :=
    hs.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmap : Measure.map φ.symm ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) =
      μ.restrict φ.source := by
    ext S hS
    have hset : φ.symm ⁻¹' S ∩ φ.target = φ.target ∩ φ.symm ⁻¹' (S ∩ φ.source) := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, φ.map_target h2⟩
      · rintro ⟨h2, h1, -⟩
        exact ⟨h1, h2⟩
    rw [Measure.map_apply_of_aemeasurable hs' hS, withDensity_apply' _ _, Measure.restrict_restrict' hT,
      Measure.restrict_apply hS, hμ _ (hS.inter φ.open_source.measurableSet) inter_subset_right, hset]
  calc ∫⁻ z in φ.target, ENNReal.ofReal (ν z) * g (φ.symm z)
      = ∫⁻ z, g (φ.symm z) ∂((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) :=
        (lintegral_withDensity_eq_lintegral_mul₀ hνm (hg.comp_aemeasurable hs)).symm
    _ = ∫⁻ y, g y ∂(Measure.map φ.symm
          ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z))) :=
        (lintegral_map' hg.aemeasurable hs').symm
    _ = ∫⁻ y in φ.source, g y ∂μ := by rw [hmap]
    _ ≤ ∫⁻ y, g y ∂μ := setLIntegral_le_lintegral _ _

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem eval_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) f = c k₀ ^ n * eval z f := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m hm
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem normRatio_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (A : HermLine ι) (hA : A.a = unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z f‖ / A.h z ^ n = ‖eval z' f‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_torus hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
    simp [unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]

theorem lift_blockNonzero (d : HSMBlockDatum D K ι Ω) {x y : d.R.X} (hy : y ∈ d.R.U x) :
    ∀ k, ∃ i, d.R.lift x y ⟨k, i⟩ ≠ 0 :=
  (d.R.mem x y hy).1

theorem ratio_blockPt_eq (d : HSMBlockDatum D K ι Ω) {n : ℕ} {f : MRingOver ℂ ι}
    (hf : IsMultiHomog f (blockDeg d.k₀ n)) {x y : d.R.X} (hy : y ∈ d.R.U x) :
    ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n =
      ‖eval (d.R.lift x y) f‖ / d.A.h (d.R.lift x y) ^ n :=
  normRatio_torus hf d.A d.deg (d.R.compat y x y ⟨d.R.mem_U y, hy⟩)

theorem continuous_ratio (d : HSMBlockDatum D K ι Ω) {n : ℕ} {f : MRingOver ℂ ι}
    (hf : IsMultiHomog f (blockDeg d.k₀ n)) :
    Continuous fun y => ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n := by
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨j, hj⟩ := d.R.A.cover y₀
  set e := d.R.A.chart j with he
  have hL : ContinuousAt (d.R.lift y₀) y₀ := by
    rw [continuousAt_pi]
    intro p
    have ha : AnalyticAt ℂ ((fun y => d.R.lift y₀ y p) ∘ e.symm) (e y₀) :=
      d.R.holo y₀ p j (e y₀) ⟨e.map_source hj, by rw [mem_preimage, e.left_inv hj]; exact d.R.mem_U y₀⟩
    refine (ha.continuousAt.comp (e.continuousAt hj)).congr ?_
    filter_upwards [e.open_source.mem_nhds hj] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hne := lift_blockNonzero d (d.R.mem_U y₀)
  have hh : ContinuousAt d.A.h (d.R.lift y₀ y₀) :=
    d.semipos.1.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hne)
  have hcont : ContinuousAt (fun y => ‖eval (d.R.lift y₀ y) f‖ / d.A.h (d.R.lift y₀ y) ^ n) y₀ :=
    (((MvPolynomial.continuous_eval f).continuousAt.comp hL).norm).div ((hh.comp hL).pow n)
      (pow_pos (d.A.pos _ hne) n).ne'
  refine hcont.congr ?_
  filter_upwards [(d.R.isOpen_U y₀).mem_nhds (d.R.mem_U y₀)] with y hy
  exact (ratio_blockPt_eq d hf hy).symm

theorem local_bound (hC : ChartSupBound.Statement) (d : HSMBlockDatum D K ι Ω) (x₀ : d.R.X) :
    ∃ N : Set d.R.X, IsOpen N ∧ x₀ ∈ N ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ f : MRingOver ℂ ι, IsMultiHomog f (blockDeg d.k₀ n) → ∀ y ∈ N,
        (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ≤
          C * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2 := by
  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨j, hj⟩ := d.R.A.cover x₀
  set e := d.R.A.chart j with he
  obtain ⟨ν, hνs, hνpos, hνV⟩ := d.vol.2 j
  have hVo : IsOpen (e.target ∩ e.symm ⁻¹' d.R.U x₀) := e.isOpen_inter_preimage_symm (d.R.isOpen_U x₀)
  have hx₀V : e x₀ ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀ :=
    ⟨e.map_source hj, by rw [mem_preimage, e.left_inv hj]; exact d.R.mem_U x₀⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hVo _ hx₀V
  have hKV : Metric.closedBall (e x₀) (δ / 2) ⊆ e.target ∩ e.symm ⁻¹' d.R.U x₀ :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hδV
  have hLa : ∀ p, AnalyticOnNhd ℂ (fun w => d.R.lift x₀ (e.symm w) p) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
    fun p => d.R.holo x₀ p j
  have hLne : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀, ∀ k, ∃ i, d.R.lift x₀ (e.symm w) ⟨k, i⟩ ≠ 0 :=
    fun w hw => lift_blockNonzero d hw.2
  have hψ : ContDiffOn ℝ 2 (fun w => 2 * Real.log (d.A.h (d.R.lift x₀ (e.symm w))))
      (e.target ∩ e.symm ⁻¹' d.R.U x₀) := by
    have hL2 : ContDiffOn ℝ 2 (fun w => d.R.lift x₀ (e.symm w)) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      contDiffOn_pi.2 fun p => ((hLa p).contDiffOn_of_completeSpace).restrict_scalars ℝ
    have hh : ContDiffOn ℝ 2 (fun w => d.A.h (d.R.lift x₀ (e.symm w))) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      (d.semipos.1.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp hL2 fun w hw => hLne w hw
    exact contDiffOn_const.mul (hh.log fun w hw => (d.A.pos _ (hLne w hw)).ne')
  obtain ⟨C₀, hC₀⟩ := hC D (e.target ∩ e.symm ⁻¹' d.R.U x₀) (Metric.closedBall (e x₀) (δ / 2)) _ ν hVo
    (isCompact_closedBall _ _) hKV hψ (hνs.continuousOn.mono inter_subset_left) fun z hz => hνpos z hz.1
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x₀) (δ / 2), e.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hj, Metric.mem_ball_self (half_pos hδ)⟩, max C₀ 0, le_max_right _ _, fun n hn f hf y hy => ?_⟩
  have hgc := (continuous_ratio d hf).pow 2
  have hgm : Measurable fun y => ENNReal.ofReal ((‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) :=
    ENNReal.measurable_ofReal.comp hgc.measurable
  have hgi : Integrable (fun y => (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) d.dV :=
    hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI0 : 0 ≤ ∫ y, (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ∂d.dV :=
    integral_nonneg fun y => sq_nonneg _
  have hres : blockL2NormComplex d n f ^ 2 = ∫ y, (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ∂d.dV := by
    rw [blockL2NormComplex, Real.sq_sqrt hI0]
  have hid : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ‖eval (d.R.lift x₀ (e.symm w)) f‖ ^ 2 *
          Real.exp (-(n : ℝ) * (2 * Real.log (d.A.h (d.R.lift x₀ (e.symm w))))) =
        (‖eval (blockPt d (e.symm w)) f‖ / d.A.h (blockPt d (e.symm w)) ^ n) ^ 2 := by
    intro w hw
    rw [ratio_blockPt_eq d hf hw.2]
    exact (sq_div_pow_eq (d.A.pos _ (hLne w hw)) n).symm
  have key := hC₀ n hn _ (analyticOnNhd_eval hLa f) (e y) (Metric.ball_subset_closedBall hy.2)
  have hyV : e y ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀ := hKV (Metric.ball_subset_closedBall hy.2)
  rw [hid _ hyV, e.left_inv hy.1] at key
  have hint : ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ENNReal.ofReal (‖eval (d.R.lift x₀ (e.symm z)) f‖ ^ 2 *
        Real.exp (-(n : ℝ) * (2 * Real.log (d.A.h (d.R.lift x₀ (e.symm z))))) * ν z) ≤
      ENNReal.ofReal (blockL2NormComplex d n f ^ 2) := by
    rw [hres, ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun y => sq_nonneg _)]
    calc _ = ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀, ENNReal.ofReal (ν z) *
            ENNReal.ofReal ((‖eval (blockPt d (e.symm z)) f‖ / d.A.h (blockPt d (e.symm z)) ^ n) ^ 2) := by
          refine setLIntegral_congr_fun hVo.measurableSet fun z hz => ?_
          rw [hid z hz, mul_comm, ENNReal.ofReal_mul (hνpos z hz.1).le]
      _ ≤ ∫⁻ z in e.target, ENNReal.ofReal (ν z) *
            ENNReal.ofReal ((‖eval (blockPt d (e.symm z)) f‖ / d.A.h (blockPt d (e.symm z)) ^ n) ^ 2) :=
          lintegral_mono_set inter_subset_left
      _ ≤ _ := lintegral_chart_le e d.dV hνs.continuousOn hνV hgm
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : ENNReal.ofReal ((‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) ≤
      ENNReal.ofReal (max C₀ 0 * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    exact key.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)) hint)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end BlockResolutionImageSup

open BlockResolutionImageSup in

theorem BlockResolutionImageSup.proof (hC : ChartSupBound.Statement) : BlockResolutionImageSup.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  choose N hNo hxN C hC0 hCb using fun x => local_bound hC d x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo fun x _ => mem_iUnion.2 ⟨x, hxN x⟩
  refine ⟨Real.sqrt (∑ x ∈ t, C x), fun n hn f hf y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  have hS : C x ≤ ∑ x ∈ t, C x := Finset.single_le_sum (fun i _ => hC0 i) hxt
  have hS0 : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg fun i _ => hC0 i
  have hr0 : 0 ≤ blockL2NormComplex d n f := Real.sqrt_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ≤
      (∑ x ∈ t, C x) * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2 :=
    (hCb x n hn f hf y hyx).trans (by gcongr)
  have hp : 0 ≤ ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n :=
    div_nonneg (norm_nonneg _) (pow_nonneg (d.A.pos _ (lift_blockNonzero d (d.R.mem_U y))).le n)
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf
  calc ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n
      = Real.sqrt ((‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) := (Real.sqrt_sq hp).symm
    _ ≤ Real.sqrt ((∑ x ∈ t, C x) * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (∑ x ∈ t, C x) * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f := by
      rw [Real.sqrt_mul (mul_nonneg hS0 hn0), Real.sqrt_mul hS0, Real.sqrt_sq hr0, hpow]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsRegular
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

theorem ConstantsRegular.proof (hD : ConstantsDescend.Statement)
    (hC : ChartConstantsDetermined.Statement) : ConstantsRegular.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hy
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hfin : Module.Finite ℤ (intsIn F Ω) :=
    Module.Finite.of_surjective
      ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict.toLinearMap
      (AlgHom.rangeRestrict_surjective _)
  have key : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ intsIn F Ω, (m : Ω) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · have hfg : (chartRingZ y c).FG :=
        ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩, by
          simp [chartRingZ, Set.image_univ]⟩
      obtain ⟨m, hm, h⟩ := hD Ω (chartRingZ y c) (intsIn F Ω) hfg hfin (hC K ι Ω F y hy c hc)
      exact ⟨m, hm, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose m hm hmem using key
  refine ⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
    fun c _ => Nat.one_le_iff_ne_zero.mp (hm c)), ?_⟩
  intro θ c hc
  have ht : algebraMap F Ω (θ : F) ∈ intsIn F Ω := (AlgHom.mem_range _).mpr ⟨θ, rfl⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), Nat.cast_mul, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem c hc _ ht)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

