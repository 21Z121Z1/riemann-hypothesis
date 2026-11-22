import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open Module

noncomputable section

section NormLength

variable {R B : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B]

theorem ord_prod {ι : Type*} (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Ring.ord_mul, ih fun i hi => ha i (by simp [hi])]
    exact mem_nonZeroDivisors_of_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun i hi => ha i (by simp [hi]))

theorem ord_norm_eq_length {b : B} (hb : Function.Injective (fun x : B => b * x)) :
    Ring.ord R (Algebra.norm R b) = Module.length R (B ⧸ Ideal.span {b}) := by
  classical
  let bs := Module.Free.chooseBasis R B
  let ι := Module.Free.ChooseBasisIndex R B
  let N : Submodule R B := (Ideal.span {b}).restrictScalars R
  let m : B →ₗ[R] B := Algebra.lmul R B b
  have hm : Function.Injective m := hb
  have hrange : LinearMap.range m = N := by
    ext x
    simp only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton', N, m]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm y b⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm b y⟩
  let φ : B ≃ₗ[R] N := (LinearEquiv.ofInjective m hm).trans (LinearEquiv.ofEq _ _ hrange)
  have h : Module.finrank R N = Module.finrank R B := φ.finrank_eq.symm
  let a := Submodule.smithNormalFormCoeffs bs h
  let b' := Submodule.smithNormalFormTopBasis bs h
  let ab := Submodule.smithNormalFormBotBasis bs h
  have ab_eq : ∀ i, (ab i : B) = a i • b' i := Submodule.smithNormalFormBotBasis_def bs h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero bs h

  have hlen : Module.length R (B ⧸ Ideal.span {b}) = ∑ i, Ring.ord R (a i) := by
    rw [← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {b})).length_eq,
      (Submodule.quotientEquivPiSpan N bs h).length_eq, Module.length_pi_of_fintype]
    rfl

  let E : B ≃ₗ[R] N := b'.equiv ab (Equiv.refl ι)
  let D : B →ₗ[R] B := N.subtype ∘ₗ E.toLinearMap
  let u : B ≃ₗ[R] B := φ.trans E.symm
  have hmDu : m = D ∘ₗ u.toLinearMap := by
    ext x
    simp [D, u, φ]
  have hDb : ∀ j, D (b' j) = a j • b' j := fun j => by
    simp only [D, E, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, Basis.equiv_apply]
    exact ab_eq j
  have hD : LinearMap.toMatrix b' b' D = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, hDb, map_smul, Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hdet : Algebra.norm R b = (∏ i, a i) * LinearMap.det (u : B →ₗ[R] B) := by
    rw [Algebra.norm_apply, show Algebra.lmul R B b = m from rfl, hmDu, LinearMap.det_comp,
      ← LinearMap.det_toMatrix b' D, hD, Matrix.det_diagonal]
  rw [hdet, Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' u), ord_prod _ _ fun i _ => ha i,
    hlen]

end NormLength

theorem NormLength.proof : NormLength.Statement := by
  intro R B _ _ _ _ _ _ _ b hb
  exact ord_norm_eq_length hb

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PPrimitiveUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem not_unit_of_pow_succ {R : Type*} [CommRing R] [IsDomain R] {ϖ : R} (hϖ : Irreducible ϖ)
    (u₁ u₂ : Rˣ) (i d : ℕ) {x y : R} (hy : IsUnit y)
    (h : (u₂ : R) * ϖ ^ (i + d + 1) * x = u₁ * ϖ ^ i * y) : False := by
  have hpow : ϖ ^ i ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have h' : (u₂ : R) * ϖ ^ (d + 1) * x = u₁ * y := by
    apply mul_left_cancel₀ hpow
    calc ϖ ^ i * ((u₂ : R) * ϖ ^ (d + 1) * x) = (u₂ * ϖ ^ (i + d + 1)) * x := by ring
      _ = (u₁ * ϖ ^ i) * y := h
      _ = ϖ ^ i * (u₁ * y) := by ring
  have hu : IsUnit ((u₁ : R) * y) := u₁.isUnit.mul hy
  rw [← h'] at hu
  exact hϖ.not_isUnit (isUnit_of_dvd_unit (Dvd.intro ((u₂ : R) * ϖ ^ d * x) (by ring)) hu)

theorem PrimitiveUnit.proof : PrimitiveUnit.Statement := by
  intro R F _ _ _ _ _ _ σ p q c ⟨m0, hm0⟩ ⟨m1, hm1⟩ hpq
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsF : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have key : ∀ m, s * p.coeff m = a * q.coeff m := by
    intro m
    have h := congrArg (coeff m) hpq
    rw [coeff_map, coeff_C_mul, coeff_map] at h
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul, h]
    field_simp
  have ha0 : a ≠ 0 := by
    intro ha
    have h := key m0
    rw [ha, zero_mul] at h
    exact hm0.ne_zero ((mul_eq_zero.mp h).resolve_left hs0)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨i, u₁, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨j, u₂, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have hij : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ⟨j - i - 1, by omega⟩
      exact not_unit_of_pow_succ hϖ u₁ u₂ i d hm1 (key m1)
    · exact h
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, i = j + d + 1 := ⟨i - j - 1, by omega⟩
      exact not_unit_of_pow_succ hϖ u₂ u₁ j d hm0 (key m0).symm
  subst hij
  refine ⟨u₁ * u₂⁻¹, ?_⟩
  rw [div_eq_iff hsF, ← map_mul]
  congr 1
  rw [Units.val_mul, mul_assoc, ← mul_assoc ((u₂⁻¹ : Rˣ) : R), Units.inv_mul, one_mul]

end

end GroundTheory.Heights₂.Heights.Vertical
end

