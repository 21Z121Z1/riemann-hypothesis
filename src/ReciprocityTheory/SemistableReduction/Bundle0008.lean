import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import ReciprocityTheory.SemistableReduction.Bundle0003

-- bundled from ReciprocityTheory.SemistableReduction.GaussValExists
section
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable def gaussRed {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    MvPolynomial σ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) :=
  ∑ α ∈ p.support, monomial α (IsLocalRing.residue _ ⟨p.coeff α, hc α⟩)

theorem gaussRed_coeff {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) (α : σ →₀ ℕ) :
    (gaussRed V p hc).coeff α = IsLocalRing.residue _ ⟨p.coeff α, hc α⟩ := by
  classical
  unfold gaussRed
  rw [MvPolynomial.coeff_sum]
  by_cases h : α ∈ p.support
  · rw [Finset.sum_eq_single α]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg hb]
    · intro h'
      exact absurd h h'
  · have h0 : p.coeff α = 0 := by simpa [MvPolynomial.mem_support_iff] using h
    have hz : (⟨p.coeff α, hc α⟩ : V.comap (algebraMap Ω U)) = 0 := Subtype.ext h0
    rw [Finset.sum_eq_zero, hz, map_zero]
    intro b hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact h hb

theorem gaussRed_eval {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    letI := residueAlgebra V (algebraMap Ω U)
    ∃ h : aeval t p ∈ V, IsLocalRing.residue V ⟨aeval t p, h⟩ =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V p hc) := by
  try dsimp only
  letI := residueAlgebra V (algebraMap Ω U)
  classical
  obtain ⟨y, hydef⟩ : ∃ y : V, y = ∑ α ∈ p.support,
      comapInclusion V (algebraMap Ω U) ⟨p.coeff α, hc α⟩ *
        ∏ s ∈ α.support, (⟨t s, ht s⟩ : V) ^ α s := ⟨_, rfl⟩
  have hy : (y : U) = aeval t p := by
    change V.subtype y = _
    rw [hydef, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    simp only [map_sum, map_mul, map_prod, map_pow]
    rfl
  have hmem : aeval t p ∈ V := by
    rw [← hy]
    exact y.2
  refine ⟨hmem, ?_⟩
  have hyy : (⟨aeval t p, hmem⟩ : V) = y := Subtype.ext hy.symm
  rw [hyy, hydef, map_sum]
  unfold gaussRed
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.aeval_monomial]
  simp only [map_mul, map_prod, map_pow]
  congr 1

private theorem residue_ne_zero_of_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {x : R}
    (hx : IsUnit x) : IsLocalRing.residue R x ≠ 0 := by
  intro h
  have hm : x ∈ IsLocalRing.maximalIdeal R := by
    exact (IsLocalRing.residue_eq_zero_iff x).1 h
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal x).1 hm) hx

private theorem isUnit_of_residue_ne_zero' {R : Type*} [CommRing R] [IsLocalRing R] {x : R}
    (h : IsLocalRing.residue R x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  have hm : x ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 hx)
  exact (IsLocalRing.residue_eq_zero_iff x).2 hm

private theorem eq_zero_of_aeval_eq_zero_of_algebraicIndependent {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {x : ι → A} (hx : AlgebraicIndependent R x) {q : MvPolynomial ι R}
    (h : MvPolynomial.aeval x q = 0) : q = 0 := by
  exact (algebraicIndependent_iff.1 hx) q h

theorem gauss_unit {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U))
    (α₀ : σ →₀ ℕ) (hα₀ : (p.coeff α₀)⁻¹ ∈ V.comap (algebraMap Ω U)) (h0 : p.coeff α₀ ≠ 0) :
    V.valuation (aeval t p) = 1 := by
  letI := residueAlgebra V (algebraMap Ω U)
  have hind' : AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
      (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := hind
  obtain ⟨hmem, hres⟩ := gaussRed_eval t V ht p hc
  have hu0 : IsUnit (⟨p.coeff α₀, hc α₀⟩ : V.comap (algebraMap Ω U)) :=
    isUnit_iff_exists_inv.mpr ⟨⟨(p.coeff α₀)⁻¹, hα₀⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hq : gaussRed V p hc ≠ 0 := by
    intro h
    have h1 := gaussRed_coeff V p hc α₀
    rw [h, MvPolynomial.coeff_zero] at h1
    exact residue_ne_zero_of_isUnit hu0 h1.symm
  have hne : IsLocalRing.residue V ⟨aeval t p, hmem⟩ ≠ 0 := by
    rw [hres]
    intro h
    exact hq (eq_zero_of_aeval_eq_zero_of_algebraicIndependent hind' h)
  have hunit := isUnit_of_residue_ne_zero' hne
  exact (V.valuation_eq_one_iff _).1 hunit

private theorem gaussValuation_of_mem_valuationSubring {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) (hp : p ≠ 0) :
    ∃ α₀ ∈ p.support, (∀ α ∈ p.support, V.valuation (algebraMap Ω U (p.coeff α)) ≤
        V.valuation (algebraMap Ω U (p.coeff α₀))) ∧
      V.valuation (aeval t p) = V.valuation (algebraMap Ω U (p.coeff α₀)) := by
  have hne : p.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h => hp (MvPolynomial.support_eq_empty.1 h)
  obtain ⟨α₀, hα₀, hmax⟩ := Finset.exists_max_image p.support
    (fun α => V.valuation (algebraMap Ω U (p.coeff α))) hne
  refine ⟨α₀, hα₀, hmax, ?_⟩
  have hc0 : p.coeff α₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hα₀
  have hv0 : V.valuation (algebraMap Ω U (p.coeff α₀)) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact (map_ne_zero _).2 hc0
  obtain ⟨q, hqdef⟩ : ∃ q : MvPolynomial σ Ω, q = MvPolynomial.C (p.coeff α₀)⁻¹ * p := ⟨_, rfl⟩
  have hqcoeff : ∀ α, q.coeff α = (p.coeff α₀)⁻¹ * p.coeff α := by
    intro α
    rw [hqdef]
    exact MvPolynomial.coeff_C_mul _ _ _
  have hqc : ∀ α, q.coeff α ∈ V.comap (algebraMap Ω U) := by
    intro α
    rw [hqcoeff, ValuationSubring.mem_comap]
    apply (V.valuation_le_one_iff _).1
    simp only [map_mul, map_inv₀]
    by_cases hα : α ∈ p.support
    · have hle : V.valuation (algebraMap Ω U (p.coeff α)) ≤
          V.valuation (algebraMap Ω U (p.coeff α₀)) := hmax α hα
      calc (V.valuation (algebraMap Ω U (p.coeff α₀)))⁻¹ * V.valuation (algebraMap Ω U (p.coeff α))
          ≤ (V.valuation (algebraMap Ω U (p.coeff α₀)))⁻¹ *
              V.valuation (algebraMap Ω U (p.coeff α₀)) := by
            exact mul_le_mul_of_nonneg_left hle zero_le'
        _ = 1 := inv_mul_cancel₀ hv0
    · have h0 : p.coeff α = 0 := by simpa [MvPolynomial.mem_support_iff] using hα
      rw [h0]
      simp
  have hα₀' : (q.coeff α₀)⁻¹ ∈ V.comap (algebraMap Ω U) := by
    rw [hqcoeff, inv_mul_cancel₀ hc0, inv_one]
    exact one_mem _
  have h0' : q.coeff α₀ ≠ 0 := by
    rw [hqcoeff, inv_mul_cancel₀ hc0]
    exact one_ne_zero
  have h1 := gauss_unit t V ht hind q hqc α₀ hα₀' h0'
  have hq : aeval t q = algebraMap Ω U (p.coeff α₀)⁻¹ * aeval t p := by
    rw [hqdef, map_mul, MvPolynomial.aeval_C]
  rw [hq] at h1
  simp only [map_mul, map_inv₀] at h1
  calc V.valuation (aeval t p)
      = V.valuation (algebraMap Ω U (p.coeff α₀)) *
          ((V.valuation (algebraMap Ω U (p.coeff α₀)))⁻¹ * V.valuation (aeval t p)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]
    _ = V.valuation (algebraMap Ω U (p.coeff α₀)) := by rw [h1, mul_one]

theorem gauss_val {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) :
    V.valuation (aeval t p) = p.support.sup fun α => V.valuation (algebraMap Ω U (p.coeff α)) := by
  by_cases hp : p = 0
  · subst hp
    rw [map_zero, MvPolynomial.support_zero, Finset.sup_empty]
    exact V.valuation.map_zero
  · obtain ⟨α₀, hα₀, hmax, hv⟩ := gaussValuation_of_mem_valuationSubring t V ht hind p hp
    rw [hv]
    exact le_antisymm
      (Finset.le_sup (f := fun α => V.valuation (algebraMap Ω U (p.coeff α))) hα₀)
      (Finset.sup_le hmax)

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.IntCoresA
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

theorem continuous_spherePoint (n : ℕ) : Continuous (spherePoint : UnitSphereC n → Fin n → ℂ) := by
  unfold spherePoint
  fun_prop

theorem sphere_zero_null (hSJ : SJStatement) {n a : ℕ} (g : MvPolynomial (Fin n) ℂ)
    (hg : g.IsHomogeneous a) (u : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1)
    (hgu : MvPolynomial.eval (WithLp.ofLp u) g ≠ 0) :
    sphereProb n {z | MvPolynomial.eval (spherePoint z) g = 0} = 0 := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [EuclideanSpace.norm_eq] at hu
    · exact h
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [hn])
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'
    exact_mod_cast Module.finrank_pos.ne'
  have htop : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  haveI : IsProbabilityMeasure (sphereProb n) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite h0 htop
  set μ := sphereProb n with hμ
  set Z := {z : UnitSphereC n | MvPolynomial.eval (spherePoint z) g = 0} with hZdef
  have hZ : MeasurableSet Z :=
    (isClosed_eq ((MvPolynomial.continuous_eval g).comp (continuous_spherePoint n))
      continuous_const).measurableSet
  obtain ⟨hint, -⟩ := hSJ n a g u hg hu hgu
  have key : ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤
      (∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ) -
        Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ + (a : ℝ) / 2 * (harmonic (n - 1) : ℝ) := by
    intro c hc
    have hgc : (MvPolynomial.C c * g).IsHomogeneous a := by
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) c).mul hg
    obtain ⟨-, hle⟩ := hSJ n a (MvPolynomial.C c * g) u hgc hu (by simp [hc, hgu])
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hle
    have hpt : ∀ z : UnitSphereC n, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ =
        Zᶜ.indicator (fun _ ↦ Real.log ‖c‖) z + Real.log ‖MvPolynomial.eval (spherePoint z) g‖ := by
      intro z
      by_cases hz : MvPolynomial.eval (spherePoint z) g = 0
      · have hzZ : z ∈ Z := hz
        simp [Set.indicator_apply, hzZ, hz]
      · have hzZ : z ∈ Zᶜ := hz
        rw [Set.indicator_of_mem hzZ, norm_mul,
          Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz)]
    have hI : ∫ z, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ ∂μ =
        (μ Zᶜ).toReal * Real.log ‖c‖ + ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ := by
      simp_rw [hpt]
      rw [integral_add ((integrable_const _).indicator hZ.compl) hint,
        integral_indicator_const _ hZ.compl, smul_eq_mul]
      try rfl
    have hcomp : (μ Zᶜ).toReal = 1 - (μ Z).toReal := by
      rw [prob_compl_eq_one_sub hZ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one]
    have hL : Real.log ‖c * MvPolynomial.eval (WithLp.ofLp u) g‖ =
        Real.log ‖c‖ + Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ := by
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hgu)]
    rw [hI, hcomp, hL] at hle
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤ K := ⟨_, key⟩
  by_contra hne
  have hp : 0 < (μ Z).toReal := ENNReal.toReal_pos hne (measure_ne_top _ _)
  have h1 := hK ((Real.exp ((|K| + 1) / (μ Z).toReal) : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.log_exp] at h1
  have h2 : (μ Z).toReal * ((|K| + 1) / (μ Z).toReal) = |K| + 1 := by
    field_simp
  linarith [le_abs_self K]

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.IntegralClosureRankAndResidueTrdegLe
section
namespace ReciprocityTheory.MultiplicativeHeights

theorem integralClosureRank (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L] :
    IsDedekindDomain (integralClosure O L) ∧ Module.Finite O (integralClosure O L) ∧
      Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank F L ∧
      {Q : Ideal (integralClosure O L) | Q.IsMaximal}.Finite ∧
      ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
          Q.1.ramificationIdx O * Q.1.inertiaDeg O = Module.finrank F L := by
  set C := integralClosure O L
  haveI hD : IsDedekindDomain C := integralClosure.isDedekindDomain O F L
  haveI hFin : Module.Finite O C := IsIntegralClosure.finite O F L C
  haveI : Module.IsTorsionFree O L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  haveI : Module.IsTorsionFree O C := inferInstance
  haveI hFr : Module.Free O C := Module.free_of_finite_type_torsion_free'
  haveI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension O F L C
  set m := IsLocalRing.maximalIdeal O
  have hm : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have key : ∀ Q : Ideal C, Q.IsMaximal ↔ Q ∈ IsDedekindDomain.primesOverFinset m C := by
    intro Q
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C]
    constructor
    · intro hQ
      have hu : (Q.under O).IsMaximal := Ideal.IsMaximal.under O Q
      refine ⟨hQ.isPrime, ⟨?_⟩⟩
      exact (IsLocalRing.eq_maximalIdeal hu).symm
    · rintro ⟨hP, hl⟩
      refine hP.isMaximal ?_
      rintro rfl
      apply hm
      rw [hl.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O C)
  refine ⟨hD, hFin, hFr, IsIntegralClosure.rank O F L C, ?_, ?_⟩
  · exact (IsDedekindDomain.primesOverFinset m C).finite_toSet.subset fun Q hQ => (key Q).1 hQ
  · rw [← Ideal.sum_ramification_inertia C F L hm]
    rw [← finsum_comp_equiv (Equiv.subtypeEquivRight key).symm, finsum_eq_sum_of_fintype,
      ← Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset m C)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.2
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C] at hP
    haveI := hP.1
    haveI := hP.2
    haveI : P.1.IsMaximal := ((key P.1).2 P.2)
    simp only [Equiv.subtypeEquivRight_symm_apply_coe]
    rw [Ideal.ramificationIdx_eq_ramificationIdx' m P.1 hm, Ideal.inertiaDeg_eq_inertiaDeg' m P.1]

open MvPolynomial

theorem algebraicIndependent_of_residue_lift {F₁ F₂ : Type} [Field F₁] [Field F₂] [Algebra F₁ F₂]
    (V : ValuationSubring F₂) {ι : Type*} (y : ι → V)
    (hx : letI := residueAlgebra V (algebraMap F₁ F₂)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (fun i => IsLocalRing.residue V (y i))) :
    AlgebraicIndependent F₁ (fun i => ((y i : V) : F₂)) := by
  classical
  letI := residueAlgebra V (algebraMap F₁ F₂)
  rw [algebraicIndependent_iff] at hx ⊢
  intro p hp
  by_contra hne
  have hS : p.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m₀, hm₀, hmax⟩ := p.support.exists_max_image
    (fun m => (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)) hS
  have hc : p.coeff m₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hm₀
  have hvc : (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hc

  have hle : ∀ m, (p.coeff m₀)⁻¹ * p.coeff m ∈ V.comap (algebraMap F₁ F₂) := by
    intro m
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hm : m ∈ p.support
    · calc ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)
          ≤ ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) := by
            gcongr
            exact hmax m hm
        _ = 1 := inv_mul_cancel₀ hvc
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      simp
  have hpp : MvPolynomial.C (p.coeff m₀)⁻¹ * p ∈
      Set.range (MvPolynomial.map (V.comap (algebraMap F₁ F₂)).subtype) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 ha
    exact ⟨⟨_, hle m⟩, by simp [MvPolynomial.coeff_C_mul]⟩
  obtain ⟨qV, hqV⟩ := hpp
  have hcoeff : qV.coeff m₀ = 1 := by
    have e := congrArg (MvPolynomial.coeff m₀) hqV
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc] at e
    exact Subtype.ext e
  have h0 : MvPolynomial.eval₂ (comapInclusion V (algebraMap F₁ F₂)) y qV = 0 := by
    apply Subtype.ext
    have e1 : MvPolynomial.aeval (fun i => ((y i : V) : F₂))
        (MvPolynomial.C (p.coeff m₀)⁻¹ * p) = 0 := by
      rw [map_mul, hp, mul_zero]
    rw [MvPolynomial.aeval_def, ← hqV, MvPolynomial.eval₂_map] at e1
    have e2 := MvPolynomial.eval₂_comp_left V.subtype (comapInclusion V (algebraMap F₁ F₂)) y qV
    have e3 : V.subtype.comp (comapInclusion V (algebraMap F₁ F₂)) =
        (algebraMap F₁ F₂).comp (V.comap (algebraMap F₁ F₂)).subtype := RingHom.ext fun _ => rfl
    rw [e3] at e2
    exact e2.trans e1

  have h1 : MvPolynomial.aeval (fun i => IsLocalRing.residue V (y i))
      (MvPolynomial.map (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) qV) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e4 := MvPolynomial.eval₂_comp_left (IsLocalRing.residue V)
      (comapInclusion V (algebraMap F₁ F₂)) y qV
    rw [h0, map_zero] at e4
    have e5 : (algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) =
        (IsLocalRing.residue V).comp (comapInclusion V (algebraMap F₁ F₂)) :=
      RingHom.ext fun r => IsLocalRing.ResidueField.map_residue _ r
    rw [e5]
    exact e4.symm
  have e6 := congrArg (MvPolynomial.coeff m₀) (hx _ h1)
  rw [MvPolynomial.coeff_map, hcoeff, map_one, MvPolynomial.coeff_zero] at e6
  exact one_ne_zero e6

theorem residueTrdegLe : TRStatement := by
  intro F₁ F₂ _ _ _ V
  letI := residueAlgebra V (algebraMap F₁ F₂)
  unfold Algebra.trdeg
  refine ciSup_le' fun s => ?_
  have hy : ∀ a : s.1, ∃ v : V, IsLocalRing.residue V v = a :=
    fun a => IsLocalRing.residue_surjective (a : IsLocalRing.ResidueField V)
  choose y hy using hy
  have hs : AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
      (fun a => IsLocalRing.residue V (y a)) := by
    have : (fun a => IsLocalRing.residue V (y a)) = ((↑) : s.1 → IsLocalRing.ResidueField V) :=
      funext hy
    rw [this]
    exact s.2
  exact (algebraicIndependent_of_residue_lift V y hs).cardinalMk_le_trdeg

theorem integralClosureRank_and_residueTrdegLe : DedekindRankStatement ∧ TRStatement :=
  ⟨by intro O F L; intros; exact integralClosureRank O F L, residueTrdegLe⟩

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.LatSemiSt
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def UnipotentStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r g : ℕ) (γ : Matrix (Fin r) (Fin r) K)
    (Q : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
    (∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 K, (γ ^ n).trace - r = (g : K) * z) →
    (Real.exp (1 / 3) + 1) * r < g → (∀ σ, (Q σ).det ≠ 0) →
    (∀ σ (u : Fin r → ℂ), normSq ((Q σ * γ.map σ * (Q σ)⁻¹) *ᵥ u) ≤
      Real.exp (2 / (3 * (r : ℝ))) * normSq u) →
    (γ - 1) ^ r = 0 ∧ ∀ σ, ∑ a, ∑ b, ‖(Q σ * (γ.map σ - 1) * (Q σ)⁻¹) a b‖ ^ 2 < 1

def hq {r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) : ℝ := (star u ⬝ᵥ (H *ᵥ u)).re

structure Majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) where

  H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ
  posDef : ∀ σ, (H σ).PosDef
  major : ∀ σ, H σ * (S.G.map σ)⁻¹ * H σ = S.G.map σ
  conj_compat : ∀ σ, H ((starRingEnd ℂ).comp σ) = (H σ).map (starRingEnd ℂ)

def gramC {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (b j))

def IsKBasisIn {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) : Prop :=
  (∀ i, b i ∈ B) ∧ LinearIndependent K b ∧ ∀ x ∈ B, x ∈ Submodule.span K (Set.range b)

def latDeg {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℝ :=
  Real.log ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re

def IsSemistableZero {K : Type} [Field K] [NumberField K] {r : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  (∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn L b → latDeg H L b = 0) ∧
  ∀ B : Submodule (𝓞 K) (Fin r → K), B ≤ L →
    ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg H B b ≤ 0

def gramX {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin k) (Fin m) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (c j))

def quotGramC {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin m) (Fin m) ℂ :=
  gramC H σ c - gramX H σ c b * (gramC H σ b)⁻¹ * gramX H σ b c

def satSub {K : Type} [Field K] [NumberField K] {r k : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin r → K) :=
  L ⊓ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)

def quotDeg {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : ℝ :=
  Real.log ((satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re

def DegAddStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k m : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K),
    (∀ σ, (H σ).PosDef) → L.FG → (∀ i, b i ∈ L) → (∀ j, c j ∈ L) →
    LinearIndependent K (Fin.append b c) →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range (Fin.append b c))) →
    latDeg H L (Fin.append b c) = latDeg H (satSub L b) b + quotDeg H L b c

def SemiPointStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L

def SemistableStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L ∧
      ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
        (∀ σ (u : Fin r → ℂ), u ≠ 0 → hq (M.H σ) (N.map σ *ᵥ u) < hq (M.H σ) u) → N = 0

end ReciprocityTheory.MultiplicativeHeights
end
end

