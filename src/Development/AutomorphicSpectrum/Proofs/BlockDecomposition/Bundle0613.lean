import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerTrans

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mp_mul' (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  simp only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s

theorem continuous_vecMul_gl (k : GL (Fin 2) F) :
    Continuous fun x : Fin 2 → F ↦ x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) :=
  continuous_id.matrix_vecMul continuous_const

def vecMulHomeo (k : GL (Fin 2) F) : (Fin 2 → F) ≃ₜ (Fin 2 → F) where
  toFun x := x ᵥ* (k : Matrix (Fin 2) (Fin 2) F)
  invFun x := x ᵥ* ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  left_inv x := by
    simp only [Matrix.vecMul_vecMul]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv x := by
    simp only [Matrix.vecMul_vecMul]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  continuous_toFun := continuous_vecMul_gl k
  continuous_invFun := continuous_vecMul_gl k⁻¹

theorem rt_mem {φ : (Fin 2 → F) → ℂ} (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F)
    (k : GL (Fin 2) F) : rt φ k ∈ GodementSectionLocal.schwartzBruhat2 F :=
  ⟨hφ.1.comp_continuous (continuous_vecMul_gl k),
    hφ.2.comp_isClosedEmbedding (vecMulHomeo k).isClosedEmbedding⟩

variable [MeasurableSpace F] [BorelSpace F]

theorem whittaker_right_translation_formula (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ)
    (g h : GL (Fin 2) F) :
    W2 ψ μ₁ μ₂ φ (g * h) = ((μ₂ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      mp (GeneralLinearGroup.det h) (1 / 2) * W2 ψ μ₁ μ₂ (rt φ h) g := by
  simp only [W2, rt, map_mul, Units.val_mul, mp_mul', Matrix.vecMul_vecMul]
  ring

theorem sTrans : Ad3.SchwartzSpaceL2.STrans := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ _ φ hφ h
  exact ⟨rt_mem hφ h, fun g => whittaker_right_translation_formula ψ μ₁ μ₂ φ g h⟩

end GlobalTheory.CompanionTheory.WhittakerTrans
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishingAtZero
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.DoubleTate

theorem quasiCharExponent_eq_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {χ : Fˣ →* ℂˣ} (h : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) :
    quasiCharExponent χ = 0 := by
  simp [quasiCharExponent, h]

theorem sdz : SDZ := by
  intro F _ _ _ _ _ _ f hf G hG α β hα hβ s hs
  let P : Fˣ → ℂ := fun u => f u * ((α u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ s
  let Q : Fˣ → ℂ := fun u => G u * (((α * β⁻¹) u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ s
  have hγ : Continuous (α * β⁻¹) := by
    have : ⇑(α * β⁻¹) = fun x => α x * (β x)⁻¹ := by
      funext x; simp
    rw [this]
    exact hα.1.mul hβ.1.inv
  have hγ1 : ∀ x, ‖(((α * β⁻¹) x : ℂˣ) : ℂ)‖ = 1 := by
    intro x
    simp [hα.2, hβ.2]
  have hP : Integrable P (multHaar F) :=
    integrable_localZeta hf hα.1 (by rw [quasiCharExponent_eq_zero hα.2]; simpa using hs)
  have hQ : Integrable Q (multHaar F) :=
    integrable_localZeta hG hγ (by rw [quasiCharExponent_eq_zero hγ1]; simpa using hs)
  have hPQ : Integrable (fun z : Fˣ × Fˣ => P z.1 * Q z.2) ((multHaar F).prod (multHaar F)) :=
    hP.mul_prod hQ
  have me := measurePreserving_mul_prod_inv (multHaar F) (multHaar F)
  have h1 : Integrable (fun z : Fˣ × Fˣ => P (z.2 * z.1) * Q z.1⁻¹)
      ((multHaar F).prod (multHaar F)) := me.integrable_comp_of_integrable hPQ
  have h2 : Integrable (fun z : Fˣ × Fˣ => P (z.1 * z.2) * Q z.2⁻¹)
      ((multHaar F).prod (multHaar F)) := h1.swap
  have key : ∀ a h : Fˣ, ((α a : ℂˣ) : ℂ) * mp a s *
      (((β h : ℂˣ) : ℂ) * f ((h : F) * a) * G ((h⁻¹ : Fˣ) : F)) = P (a * h) * Q h⁻¹ := by
    intro a h
    have hm : ((modulus (((a * h : Fˣ)) : F) : ℝ) : ℂ) ^ s *
        ((modulus (((h⁻¹ : Fˣ)) : F) : ℝ) : ℂ) ^ s = mp a s := by
      rw [← Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
      have hmm : ((modulus (((a * h : Fˣ)) : F) : ℝ)) * (modulus (((h⁻¹ : Fˣ)) : F) : ℝ) =
          modulus (a : F) := by
        rw [← NNReal.coe_mul, ← modulus_mul]
        congr 2
        simp
      rw [mp, ← Complex.ofReal_mul, hmm]
    have hc : ((α (a * h) : ℂˣ) : ℂ) * (((α * β⁻¹) h⁻¹ : ℂˣ) : ℂ) =
        ((α a : ℂˣ) : ℂ) * ((β h : ℂˣ) : ℂ) := by
      have : α (a * h) * (α * β⁻¹) h⁻¹ = α a * β h := by
        simp [mul_comm, mul_left_comm]
      exact_mod_cast congrArg Units.val this
    simp only [P, Q]
    rw [← hm, show ((a * h : Fˣ) : F) = (h : F) * a by simp [mul_comm]]
    linear_combination (-(f ((h : F) * a) * G ((h⁻¹ : Fˣ) : F) *
      ((modulus ((h : F) * a) : ℝ) : ℂ) ^ s * ((modulus (((h⁻¹ : Fˣ)) : F) : ℝ) : ℂ) ^ s)) * hc
  have hin : ∀ a : Fˣ, ((α a : ℂˣ) : ℂ) * mp a s *
      (∫ h : Fˣ, ((β h : ℂˣ) : ℂ) * f ((h : F) * a) * G ((h⁻¹ : Fˣ) : F) ∂multHaar F) =
      ∫ h : Fˣ, P (a * h) * Q h⁻¹ ∂multHaar F := by
    intro a
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => key a h)
  refine ⟨?_, ?_⟩
  · simp only [hin]
    exact h2.integral_prod_left
  · simp only [hin]
    rw [← integral_prod (fun z : Fˣ × Fˣ => P (z.1 * z.2) * Q z.2⁻¹) h2]
    have e1 : ∫ z : Fˣ × Fˣ, P (z.1 * z.2) * Q z.2⁻¹ ∂((multHaar F).prod (multHaar F)) =
        ∫ z : Fˣ × Fˣ, P (z.2 * z.1) * Q z.1⁻¹ ∂((multHaar F).prod (multHaar F)) :=
      integral_prod_swap (fun z : Fˣ × Fˣ => P (z.2 * z.1) * Q z.1⁻¹)
    have e2 : ∫ z : Fˣ × Fˣ, P (z.2 * z.1) * Q z.1⁻¹ ∂((multHaar F).prod (multHaar F)) =
        ∫ z : Fˣ × Fˣ, P z.1 * Q z.2 ∂((multHaar F).prod (multHaar F)) := by
      conv_rhs => rw [← me.map_eq]
      exact (integral_map me.measurable.aemeasurable
        (by rw [me.map_eq]; exact hPQ.1)).symm
    rw [e1, e2, integral_prod_mul]
    rfl

end GlobalTheory.CompanionTheory.DoubleTate
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerTorus

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem integral_comp_unit_mul (ν : Measure F) [ν.IsAddHaarMeasure] (h : Fˣ) (G : F → ℂ) :
    ∫ y, G ((h : F) * y) ∂ν = ((modulus (h : F) : ℝ) : ℂ)⁻¹ * ∫ t, G t ∂ν := by
  have hne : (h : F) ≠ 0 := h.ne_zero
  have hemb : MeasurableEmbedding (fun x : F => (h : F) * x) :=
    (Homeomorph.mulLeft₀ (h : F) hne).measurableEmbedding
  have h1 : ∫ t, G t ∂(Measure.map (fun x : F => (h : F) * x) ν) = ∫ y, G ((h : F) * y) ∂ν :=
    hemb.integral_map G
  rw [← h1, map_mul_left_eq_smul ν hne, integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

theorem mp_one (h : Fˣ) : mp h 1 = ((modulus (h : F) : ℝ) : ℂ) := by
  simp [mp]

theorem det_diagonal_two (a : Fˣ) : GeneralLinearGroup.det (dg2 a (1 : Fˣ)) = a := by
  ext
  simp [dg2, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem vecMul_diagonal_bottom_row (a : Fˣ) (u v : F) :
    ![u, v] ᵥ* ((dg2 a (1 : Fˣ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = ![u * a, v] := by
  ext i
  fin_cases i <;> simp [dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem inner_pt (ψ : AddChar F Circle) (f g : F → ℂ) (a h : Fˣ) :
    mp h 1 * ∫ x, pt f g (![(h : F), h * x] ᵥ* ((dg2 a (1 : Fˣ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-x) : ℂ) ∂selfDualMeasure ψ =
      f ((h : F) * a) * localFourier (selfDualMeasure ψ) ψ g (-((h⁻¹ : Fˣ) : F)) := by
  have hne : (h : F) ≠ 0 := h.ne_zero
  have hm : ((modulus (h : F) : ℝ) : ℂ) ≠ 0 := by
    have := modulus_ne_zero hne
    exact_mod_cast this
  have e1 : ∀ x : F, pt f g (![(h : F), h * x] ᵥ* ((dg2 a (1 : Fˣ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-x) : ℂ) = f ((h : F) * a) *
          ((fun t : F => g t * (ψ (t * (-((h⁻¹ : Fˣ) : F))) : ℂ)) ((h : F) * x)) := by
    intro x
    have e2 : ((h : F) * x) * (-((h⁻¹ : Fˣ) : F)) = -x := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
    simp only [vecMul_diagonal_bottom_row, pt, e2]
    simp [mul_assoc]
  have e3 := integral_comp_unit_mul (selfDualMeasure ψ) h
    (fun t : F => g t * (ψ (t * (-((h⁻¹ : Fˣ) : F))) : ℂ))
  rw [integral_congr_ae (Filter.Eventually.of_forall e1), integral_const_mul, e3, mp_one]
  unfold localFourier
  rw [mul_left_comm, mul_inv_cancel_left₀ hm]

theorem swd : SWd := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ _ f _ g _ a
  unfold W2
  rw [det_diagonal_two]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  have := inner_pt ψ f g a h
  simp only [mul_assoc] at this ⊢
  rw [this]

end GlobalTheory.CompanionTheory.WhittakerTorus
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_occurs_irreducible_subquotient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL k), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  first | exact @GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | exact GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | (intros; apply GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd <;> assumption)
end

