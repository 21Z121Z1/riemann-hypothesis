import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.DeltaQExpansionIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm EisensteinSeries PowerSeries ArithmeticFunction
open scoped MatrixGroups ArithmeticFunction.sigma

noncomputable section

def DeltaQExpansionIntegral.Statement : Prop :=
  ∃ D : PowerSeries ℤ, constantCoeff D = 1 ∧
    qExpansion 1 ModularForm.discriminant = map (Int.castRingHom ℂ) (X * D)

namespace DeltaQExpansionIntegral

def sigmaSeries (k : ℕ) : PowerSeries ℤ := mk fun n ↦ (σ k n : ℤ)

theorem qExpansion_E₄ :
    qExpansion 1 E₄ = map (Int.castRingHom ℂ) (1 + (240 : ℤ) • sigmaSeries 3) := by
  ext m
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, coeff_map]
  have hb : bernoulli 4 = -1 / 30 := by decide +kernel
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sigmaSeries]
  · rw [map_add, map_zsmul]
    simp [hm, sigmaSeries, hb, coeff_one]
    norm_num

theorem qExpansion_E₆ :
    qExpansion 1 E₆ = map (Int.castRingHom ℂ) (1 - (504 : ℤ) • sigmaSeries 5) := by
  ext m
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, coeff_map]
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sigmaSeries]
  · rw [map_sub, map_zsmul]
    simp [hm, sigmaSeries, hb, coeff_one]
    norm_num

theorem twelve_dvd (n : ℕ) : 12 ∣ 5 * σ 3 n + 7 * σ 5 n := by
  rw [sigma_apply, sigma_apply, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.dvd_sum fun d _ ↦ ?_
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  generalize (d : ZMod 12) = x
  revert x
  decide

def cSeries : PowerSeries ℤ := mk fun n ↦ (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)

theorem twelve_smul_cSeries :
    (12 : ℤ) • cSeries = (5 : ℤ) • sigmaSeries 3 + (7 : ℤ) • sigmaSeries 5 := by
  ext n
  have h := Nat.mul_div_cancel' (twelve_dvd n)
  rw [map_add, map_zsmul, map_zsmul, map_zsmul]
  simp only [cSeries, sigmaSeries, coeff_mk, smul_eq_mul]
  exact_mod_cast h

theorem qExpansion_discriminant_smul :
    (1728 : ℂ) • qExpansion 1 ModularForm.discriminant =
      qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
  have e : (1728 : ℂ) • (⇑CuspForm.discriminant) = ⇑(E₄.pow 3) - ⇑(E₆.pow 2) := by
    funext τ
    simp only [Pi.smul_apply, Pi.sub_apply, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul,
      CuspForm.coe_discriminant, discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3,
    ← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ 2,
    ← ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL (E₄.pow 3) (E₆.pow 2), ← e,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1728 : ℂ) CuspForm.discriminant]
  rfl

theorem proof : Statement := by
  set A := sigmaSeries 3
  set B := sigmaSeries 5
  set Ez : PowerSeries ℤ := 100 * A ^ 2 + 8000 * A ^ 3 - 147 * B ^ 2 + cSeries with hEz
  have hC := twelve_smul_cSeries
  simp only [zsmul_eq_mul, Int.cast_ofNat] at hC
  have hring : (1 + (240 : ℤ) • A) ^ 3 - (1 - (504 : ℤ) • B) ^ 2 = 1728 * Ez := by
    simp only [zsmul_eq_mul, Int.cast_ofNat, hEz]
    linear_combination (-144 : PowerSeries ℤ) * hC
  have key : qExpansion 1 ModularForm.discriminant = map (Int.castRingHom ℂ) Ez := by
    have h2 : (1728 : ℂ) • map (Int.castRingHom ℂ) Ez = qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
      rw [qExpansion_E₄, qExpansion_E₆, ← map_pow, ← map_pow, ← map_sub, hring, map_mul,
        map_ofNat, Algebra.smul_def, map_ofNat]
    exact smul_right_injective _ (by norm_num : (1728 : ℂ) ≠ 0)
      (qExpansion_discriminant_smul.trans h2.symm)
  have h0 : constantCoeff Ez = 0 := by
    simp [hEz, A, B, sigmaSeries, cSeries]
  obtain ⟨D, hD⟩ := X_dvd_iff.mpr h0
  refine ⟨D, ?_, hD ▸ key⟩
  have h1 := discriminant_qExpansion_coeff_one
  rw [key, hD, coeff_map, coeff_succ_X_mul, eq_intCast] at h1
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact_mod_cast h1

end DeltaQExpansionIntegral

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeries
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries

noncomputable section

def IntSeriesConv (F : PowerSeries ℤ) (r : ℝ) : Prop :=
  Summable fun n ↦ |((coeff n F : ℤ) : ℝ)| * r ^ n

def intSeriesEval (F : PowerSeries ℤ) (z : ℂ) : ℂ :=
  ∑' n, ((coeff n F : ℤ) : ℂ) * z ^ n

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PWIdealField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField

noncomputable section

theorem isIntegral_of_map {F F' : Type*} [Field F] [Field F'] (j : F →+* F') {x : F}
    (h : IsIntegral ℤ (j x)) : IsIntegral ℤ x :=
  (isIntegral_algHom_iff j.toIntAlgHom j.injective).1 h

theorem le_of_map_le {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) ≤ B.map (RingOfIntegers.mapRingHom j)) : A ≤ B := by
  obtain ⟨b, hbB, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  obtain ⟨B', hB'⟩ : B ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbB)
  have hB'0 : B' ≠ 0 := by
    rintro rfl
    rw [mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hB'
    exact hb0 hB'
  have key : A * B' ≤ B * B' := by
    rw [← hB', Ideal.mul_le]
    intro x hx y hy
    have hm : RingOfIntegers.mapRingHom j (x * y) ∈
        (Ideal.span {b}).map (RingOfIntegers.mapRingHom j) := by
      rw [hB', Ideal.map_mul, map_mul]
      exact Ideal.mul_mem_mul (h (Ideal.mem_map_of_mem _ hx)) (Ideal.mem_map_of_mem _ hy)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
    obtain ⟨z, hz⟩ := hm
    have hbF : (b : F) ≠ 0 := by
      intro h0
      exact hb0 (RingOfIntegers.ext (by simpa using h0))
    have hz' : (z : F') * j (b : F) = j ((x * y : 𝓞 F) : F) := by
      have := congrArg (fun t : 𝓞 F' ↦ (t : F')) hz
      simpa using this
    have himg : j (((x * y : 𝓞 F) : F) / (b : F)) = (z : F') := by
      rw [map_div₀, ← hz', mul_div_assoc, div_self ((map_ne_zero j).2 hbF), mul_one]
    have hq : IsIntegral ℤ (((x * y : 𝓞 F) : F) / (b : F)) := by
      apply isIntegral_of_map j
      rw [himg]
      exact RingOfIntegers.isIntegral_coe z
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨_, hq⟩, RingOfIntegers.ext ?_⟩
    show ((x * y : 𝓞 F) : F) / (b : F) * (b : F) = ((x * y : 𝓞 F) : F)
    rw [div_mul_cancel₀ _ hbF]
  have hdvd : B * B' ∣ A * B' := Ideal.dvd_iff_le.2 key
  exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_right hB'0).1 hdvd)

theorem eq_of_map_eq {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) = B.map (RingOfIntegers.mapRingHom j)) : A = B := by
  have hA : A ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.map_eq_bot_iff_of_injective] at h
    · exact hB h
    · intro x y hxy
      exact RingOfIntegers.ext (j.injective (by simpa using congrArg (fun t : 𝓞 F' ↦ (t : F')) hxy))
  exact le_antisymm (le_of_map_le j hB h.le) (le_of_map_le j hA h.ge)

theorem exists_extension_mem_range {F : Type} [Field F] [NumberField F] (τ : F →+* ℂ) {z₁ z₂ : ℂ}
    (h₁ : IsAlgebraic ℚ z₁) (h₂ : IsAlgebraic ℚ z₂) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (j : F →+* F') (τ' : F' →+* ℂ),
      τ'.comp j = τ ∧ z₁ ∈ Set.range τ' ∧ z₂ ∈ Set.range τ' := by
  let e := AlgEquiv.ofInjectiveField τ.toRatAlgHom
  let E₁ : IntermediateField ℚ ℂ := τ.toRatAlgHom.fieldRange
  let E₂ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {z₁, z₂}
  have : FiniteDimensional ℚ E₁ := LinearEquiv.finiteDimensional e.toLinearEquiv
  have : FiniteDimensional ℚ E₂ :=
    IntermediateField.finiteDimensional_adjoin_pair h₁.isIntegral h₂.isIntegral
  have : FiniteDimensional ℚ ↥(E₁ ⊔ E₂) := IntermediateField.finiteDimensional_sup E₁ E₂
  have : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite ℚ _
  refine ⟨↥(E₁ ⊔ E₂), inferInstance, inferInstance,
    ((IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)).toRingHom.comp e.toRingEquiv.toRingHom),
    (E₁ ⊔ E₂).val.toRingHom, ?_, ?_, ?_⟩
  · ext x
    rfl
  · exact ⟨⟨z₁, (le_sup_right : E₂ ≤ E₁ ⊔ E₂)
      (IntermediateField.subset_adjoin ℚ _ (by simp))⟩, rfl⟩
  · exact ⟨⟨z₂, (le_sup_right : E₂ ≤ E₁ ⊔ E₂)
      (IntermediateField.subset_adjoin ℚ _ (by simp))⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

