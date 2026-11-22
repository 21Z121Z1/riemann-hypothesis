import Mathlib
import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.AvgStep

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.GelfCptOfSteps
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix

theorem gelfCpt_of_steps (hAvg : AvgStep) (hMul : MulStep) (hSpan : PI.UMultOne.IntSpan)
    (hConv : PI.UMultOne.ConvComm) : PI.UMultOne.GelfandCompact := by
  intro G _ _ _ _ _ _ H τ hH hτc hτa hτi hτH N ρ hc hirr A B hA hB
  borelize G
  let μ : Measure G := Measure.haar
  obtain ⟨a, ha, hAa⟩ := hSpan G μ N ρ hc hirr A
  obtain ⟨b, hb, hBb⟩ := hSpan G μ N ρ hc hirr B
  have eA : A = intMat μ ρ a := by ext i j; exact hAa i j
  have eB : B = intMat μ ρ b := by ext i j; exact hBb i j
  subst eA eB
  obtain ⟨a', ha'c, ha'i, ea'⟩ := hAvg G μ H hH N ρ hc a ha hA
  obtain ⟨b', hb'c, hb'i, eb'⟩ := hAvg G μ H hH N ρ hc b hb hB
  rw [← ea', ← eb', hMul G μ N ρ hc a' b' ha'c hb'c, hMul G μ N ρ hc b' a' hb'c ha'c]
  congr 1
  funext z
  exact hConv G μ H τ hτc hτa hτi hτH a' b' ha'c hb'c ha'i hb'i z

end PI.UnitaryGroupMassFormula.GelfCpt
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.IntegrableOfContinuousCpt
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix

theorem integrable_of_continuous_cpt {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {F : X → ℂ} (hF : Continuous F) : Integrable F ν :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem mul_entry {N : ℕ} (μ : Measure G) [μ.IsHaarMeasure] (R : G → Matrix (Fin N) (Fin N) ℂ)
    (hR : ∀ i j, Continuous fun g => R g i j) (hRm : ∀ x y, R (x * y) = R x * R y)
    (f₁ f₂ : G → ℂ) (h₁ : Continuous f₁) (h₂ : Continuous f₂) (i j : Fin N) :
    ∑ k, (∫ x, f₁ x * R x i k ∂μ) * (∫ y, f₂ y * R y k j ∂μ) =
      ∫ z, (∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ) * R z i j ∂μ := by
  calc ∑ k, (∫ x, f₁ x * R x i k ∂μ) * (∫ y, f₂ y * R y k j ∂μ)
      = ∑ k, ∫ x, f₁ x * R x i k * (∫ y, f₂ y * R y k j ∂μ) ∂μ := by
        congr 1; funext k; rw [integral_mul_const]
    _ = ∫ x, ∑ k, f₁ x * R x i k * (∫ y, f₂ y * R y k j ∂μ) ∂μ := by
        rw [integral_finsetSum]
        intro k _
        exact integrable_of_continuous_cpt μ ((h₁.mul (hR i k)).mul continuous_const)
    _ = ∫ x, ∫ y, f₁ x * f₂ y * R (x * y) i j ∂μ ∂μ := by
        congr 1; funext x
        have e : ∀ y, f₁ x * f₂ y * R (x * y) i j = ∑ k, f₁ x * R x i k * (f₂ y * R y k j) := by
          intro y; rw [hRm, Matrix.mul_apply, Finset.mul_sum]; congr 1; funext k; ring
        simp_rw [e]
        rw [integral_finsetSum]
        · congr 1; funext k; rw [integral_const_mul]
        · intro k _
          exact integrable_of_continuous_cpt μ (continuous_const.mul (h₂.mul (hR k j)))
    _ = ∫ x, ∫ z, f₁ x * f₂ (x⁻¹ * z) * R z i j ∂μ ∂μ := by
        congr 1; funext x
        rw [← integral_mul_left_eq_self (fun z => f₁ x * f₂ (x⁻¹ * z) * R z i j) x]
        simp only [inv_mul_cancel_left]
    _ = ∫ z, ∫ x, f₁ x * f₂ (x⁻¹ * z) * R z i j ∂μ ∂μ := by
        rw [integral_integral_swap]
        exact integrable_of_continuous_cpt (μ.prod μ)
          (F := Function.uncurry fun x z => f₁ x * f₂ (x⁻¹ * z) * R z i j)
          (((h₁.comp continuous_fst).mul
            (h₂.comp (continuous_fst.inv.mul continuous_snd))).mul ((hR i j).comp continuous_snd))
    _ = ∫ z, (∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ) * R z i j ∂μ := by
        congr 1; funext z; rw [integral_mul_const]

end

theorem mulStep : MulStep := by
  intro G _ _ _ _ _ _ _ _ μ _ N ρ hc f₁ f₂ h₁ h₂
  ext i j
  simp only [intMat, Matrix.of_apply, Matrix.mul_apply]
  exact mul_entry μ (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))
    (fun i j => hc.matrix_elem i j) (fun x y => by simp only [map_mul, Units.val_mul])
    f₁ f₂ h₁ h₂ i j

end PI.UnitaryGroupMassFormula.GelfCpt
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.MulIntMatMul
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix

theorem integrable_of_cont {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] {F : X → ℂ} (hF : Continuous F) :
    Integrable F ν :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem haar_rightInv (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  constructor
  intro g
  have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
  have hu : Measure.map (· * g) μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h0 : μ Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr (NeZero.ne μ)).ne'
  have ht : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  have h1 : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) * μ Set.univ =
      1 * μ Set.univ := by
    rw [one_mul]
    conv_rhs => rw [← hu, e]
    simp
  have hc : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 h1
  rw [e, ENNReal.coe_eq_one.mp hc, one_smul]

theorem integral_conj (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ) (h : G) :
    ∫ g, F (h * g * h⁻¹) ∂μ = ∫ g, F g ∂μ := by
  have := haar_rightInv μ
  have e1 := integral_mul_left_eq_self (μ := μ) (fun y => F (y * h⁻¹)) h
  have e2 := integral_mul_right_eq_self (μ := μ) F h⁻¹
  exact e1.trans e2

theorem mul_intMat_mul (μ : Measure G) [IsFiniteMeasure μ] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (M M' : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) :
    (M * intMat μ ρ f * M') i j =
      ∫ g, f g * (M * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * M') i j ∂μ := by
  have hR : ∀ k l, Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) k l :=
    fun k l => (continuous_apply l).comp ((continuous_apply k).comp hc)
  simp only [Matrix.mul_apply, intMat, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← integral_const_mul, ← integral_mul_const]
      congr 1
      funext g
      ring
    · intro k _
      exact integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const))
  · intro l _
    exact integrable_finsetSum _ (fun k _ =>
      integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const)))

theorem intMat_conj (μ : Measure G) [μ.IsHaarMeasure] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (h : G)
    (hA : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f =
      intMat μ ρ f * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) (i j : Fin N) :
    ∫ g, f (h⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ =
      intMat μ ρ f i j := by
  have hRmul : ∀ x y, ((ρ (x * y) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
        ((ρ y : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun x y => by
    rw [map_mul, Units.val_mul]
  have e : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f *
      ((ρ h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = intMat μ ρ f := by
    rw [hA, Matrix.mul_assoc, ← hRmul, mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one]
  rw [← e, mul_intMat_mul μ ρ hc hf]
  refine (integral_conj μ (fun x => f (h⁻¹ * x * h) *
    ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) h).symm.trans ?_
  congr 1
  funext g
  have hg : h⁻¹ * (h * g * h⁻¹) * h = g := by group
  simp only [hg, hRmul]

end

theorem avgStep : AvgStep := by
  intro G _ _ _ _ _ _ _ _ μ _ H hH N ρ hc f hf hA
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let ν : Measure H := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν := ⟨by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at this⟩
  have hF : Continuous (Function.uncurry fun (g : G) (h : H) => f ((h : G)⁻¹ * g * h)) :=
    hf.comp (((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  refine ⟨fun g => ∫ h : H, f ((h : G)⁻¹ * g * h) ∂ν, ?_, ?_, ?_⟩
  · have := continuous_parametric_integral_of_continuous (μ := ν) hF isCompact_univ
    simpa only [Measure.restrict_univ] using this
  · intro k hk x
    show ∫ h : H, f ((h : G)⁻¹ * (k * x * k⁻¹) * h) ∂ν = ∫ h : H, f ((h : G)⁻¹ * x * h) ∂ν
    have e := integral_mul_left_eq_self (μ := ν) (fun h : H => f ((h : G)⁻¹ * x * h))
      (⟨k, hk⟩⁻¹ : H)
    rw [← e]
    congr 1
    funext h
    show f ((h : G)⁻¹ * (k * x * k⁻¹) * h) = f (((⟨k, hk⟩⁻¹ * h : H) : G)⁻¹ * x * ((⟨k, hk⟩⁻¹ * h : H) : G))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  · ext i j
    have hR : Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hc)
    have hI : Integrable (Function.uncurry fun (g : G) (h : H) =>
        f ((h : G)⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j)
        (μ.prod ν) :=
      integrable_of_cont _ (hF.mul (hR.comp continuous_fst))
    simp only [intMat, Matrix.of_apply]
    calc ∫ g, (∫ h : H, f ((h : G)⁻¹ * g * h) ∂ν) *
          ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ
        = ∫ g, ∫ h : H, f ((h : G)⁻¹ * g * h) *
            ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂ν ∂μ := by
          congr 1; funext g; rw [integral_mul_const]
      _ = ∫ h : H, ∫ g, f ((h : G)⁻¹ * g * h) *
            ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ ∂ν :=
          integral_integral_swap hI
      _ = ∫ _h : H, intMat μ ρ f i j ∂ν := by
          congr 1; funext h
          exact intMat_conj μ ρ hc hf (h : G) (hA h h.2) i j
      _ = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ := by
          simp [intMat]

end PI.UnitaryGroupMassFormula.GelfCpt
end
end

