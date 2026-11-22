import Mathlib
import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0057

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.CommMultOf
section
namespace PI.UnitaryGroupMassFormula.CommMult

open Matrix

theorem commMult_of (hS : SchurStep) (hI : InjStep) (hA : AvStep) : PI.UMultOne.CommutantMult := by
  intro H _ _ _ _ _ _ N M π σ hπ hσ hirr hcomm Hm hHm
  have key : ∀ T₁ ∈ Hm, T₁ ≠ 0 → ∀ T₂ ∈ Hm, ∃ c : ℂ, c • T₁ = T₂ := by
    intro T₁ h₁ hne T₂ h₂
    rw [hHm] at h₁ h₂
    obtain ⟨X, hX⟩ := hI H N M π σ hirr T₁ h₁ hne
    obtain ⟨S, hSeq, hST⟩ := hA H N M π σ hπ hσ T₁ X h₁ hX
    obtain ⟨c, hc⟩ := hS H M σ hirr (S * T₂) (fun g => by
      rw [← Matrix.mul_assoc, hSeq g, Matrix.mul_assoc, h₂ g, Matrix.mul_assoc])
    refine ⟨c, ?_⟩
    by_contra hne'
    set T := T₂ - c • T₁ with hT
    have hT0 : T ≠ 0 := sub_ne_zero.mpr (Ne.symm hne')
    have hTeq : ∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T =
        T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) := fun g => by
      rw [hT, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h₁ g, h₂ g]
    have hST0 : S * T = 0 := by
      rw [hT, Matrix.mul_sub, Matrix.mul_smul, hST, hc, sub_self]
    obtain ⟨X', hX'⟩ := hI H N M π σ hirr T hTeq hT0
    obtain ⟨S', hS'eq, hS'T⟩ := hA H N M π σ hπ hσ T X' hTeq hX'
    have hP : ∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (T₁ * S') =
        (T₁ * S') * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun g => by
      rw [← Matrix.mul_assoc, h₁ g, Matrix.mul_assoc, hS'eq g, Matrix.mul_assoc]
    have hQ : ∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (T * S) =
        (T * S) * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun g => by
      rw [← Matrix.mul_assoc, hTeq g, Matrix.mul_assoc, hSeq g, Matrix.mul_assoc]
    have hPQ := hcomm _ _ hP hQ
    have e1 : T₁ * S' * (T * S) = T₁ * S := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc S', hS'T, Matrix.one_mul]
    have e2 : T * S * (T₁ * S') = T * S' := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, hST, Matrix.one_mul]
    have e3 : T₁ * S = T * S' := by rw [← e1, ← e2, hPQ]
    have e4 : S = 0 := by
      calc S = S * T₁ * S := by rw [hST, Matrix.one_mul]
        _ = S * T * S' := by rw [Matrix.mul_assoc, e3, ← Matrix.mul_assoc]
        _ = 0 := by rw [hST0, Matrix.zero_mul]
    rw [e4, Matrix.zero_mul] at hST
    have hM : M = 0 := by
      by_contra hM
      have h := congrFun (congrFun hST ⟨0, Nat.pos_of_ne_zero hM⟩) ⟨0, Nat.pos_of_ne_zero hM⟩
      simp at h
    subst hM
    exact hT0 (Matrix.ext fun _ j => j.elim0)
  by_cases h0 : ∃ T₁ ∈ Hm, T₁ ≠ 0
  · obtain ⟨T₁, h₁, hne⟩ := h0
    apply finrank_le_one (⟨T₁, h₁⟩ : Hm)
    intro w
    obtain ⟨c, hc⟩ := key T₁ h₁ hne w.1 w.2
    exact ⟨c, Subtype.ext hc⟩
  · push Not at h0
    have hb : Hm = ⊥ := (Submodule.eq_bot_iff _).mpr h0
    subst hb
    simp

end PI.UnitaryGroupMassFormula.CommMult
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.InjStep
section
namespace PI.UnitaryGroupMassFormula.CommMult

open Matrix

theorem injStep : InjStep := by
  intro G _ N M π σ hirr T hT hne
  have hstab : ∀ g, ∀ v ∈ LinearMap.ker (Matrix.toLin' T),
      ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ).mulVec v ∈ LinearMap.ker (Matrix.toLin' T) := by
    intro g v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hT g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases hirr _ hstab with h | h
  · obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' T) h
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    calc LinearMap.toMatrix' g * T = LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.toLin' T) := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' T) := (LinearMap.toMatrix'_comp _ _).symm
      _ = 1 := by rw [hg, LinearMap.toMatrix'_id]
  · have h0 : Matrix.toLin' T = 0 := LinearMap.ker_eq_top.mp h
    exact absurd (Matrix.toLin'.injective (h0.trans (map_zero _).symm)) hne

end PI.UnitaryGroupMassFormula.CommMult
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.IntegrableEntry
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CommMult

open MeasureTheory Matrix

section Integral

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

def mInt (μ : Measure H) {m n : Type} (F : H → Matrix m n ℂ) : Matrix m n ℂ :=
  Matrix.of fun i j => ∫ h, F h i j ∂μ

lemma integrable_entry (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {m n : Type}
    {F : H → Matrix m n ℂ} (hF : Continuous F) (i : m) (j : n) :
    Integrable (fun h => F h i j) μ :=
  (hF.matrix_elem i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma mul_mInt (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {l m n : Type} [Fintype m]
    (A : Matrix l m ℂ) {F : H → Matrix m n ℂ} (hF : Continuous F) :
    A * mInt μ F = mInt μ (fun h => A * F h) := by
  ext i j
  simp only [mInt, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ (fun k _ => (integrable_entry μ hF k j).const_mul (A i k))]
  simp only [integral_const_mul]

lemma mInt_mul (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {l m n : Type} [Fintype m]
    {F : H → Matrix l m ℂ} (hF : Continuous F) (B : Matrix m n ℂ) :
    mInt μ F * B = mInt μ (fun h => F h * B) := by
  ext i j
  simp only [mInt, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ (fun k _ => (integrable_entry μ hF i k).mul_const (B k j))]
  simp only [integral_mul_const]

lemma mInt_const (μ : Measure H) {m n : Type} (C : Matrix m n ℂ) :
    mInt μ (fun _ => C) = μ.real Set.univ • C := by
  ext i j
  simp [mInt, integral_const]

lemma mInt_left (μ : Measure H) [μ.IsMulLeftInvariant] {m n : Type} (F : H → Matrix m n ℂ)
    (g : H) : mInt μ (fun h => F (g * h)) = mInt μ F := by
  ext i j
  simp only [mInt, Matrix.of_apply]
  exact integral_mul_left_eq_self (fun h => F h i j) g

end Integral

theorem avStep : AvStep := by
  intro H _ _ _ _ _ N M π σ hπ hσ T X hT hXT
  let _ : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  set μ : Measure H := Measure.haar with hμ
  set F : H → Matrix (Fin M) (Fin N) ℂ := fun h =>
    ((σ h : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * X *
      ((π h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hFdef
  have hπi : Continuous (fun h : H => ((π h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) :=
    (show Continuous (fun g : H => ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) from hπ).comp
      continuous_inv
  have hF : Continuous F :=
    ((show Continuous (fun g : H => ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) from
      hσ).matrix_mul continuous_const).matrix_mul hπi
  set S₀ := mInt μ F with hS₀
  have hequi : ∀ g, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * S₀ =
      S₀ * ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    intro g
    have hFg : Continuous (fun h => F (g * h)) := hF.comp (continuous_const.mul continuous_id)
    have hpt : (fun h => ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * F h) =
        (fun h => F (g * h) * ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := by
      funext h
      simp only [hFdef, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ), ← Units.val_mul,
        ← map_mul, ← Units.val_mul (π (g * h)⁻¹), ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
    rw [hS₀, mul_mInt μ _ hF, hpt, ← mInt_mul μ hFg, mInt_left μ F g]
  have hST : S₀ * T = μ.real Set.univ • (1 : Matrix (Fin M) (Fin M) ℂ) := by
    have hpt : (fun h => F h * T) = (fun _ => (1 : Matrix (Fin M) (Fin M) ℂ)) := by
      funext h
      simp only [hFdef]
      rw [Matrix.mul_assoc, hT h⁻¹, ← Matrix.mul_assoc, Matrix.mul_assoc _ X T,
        hXT, Matrix.mul_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [hS₀, mInt_mul μ hF, hpt, mInt_const]
  have hc : 0 < μ.real Set.univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
      (measure_ne_top μ _)
  refine ⟨(μ.real Set.univ)⁻¹ • S₀, fun g => ?_, ?_⟩
  · rw [Matrix.mul_smul, hequi g, Matrix.smul_mul]
  · rw [Matrix.smul_mul, hST, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

end PI.UnitaryGroupMassFormula.CommMult
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStepAlt
section
namespace PI.UnitaryGroupMassFormula.CommMult

open Matrix

theorem schurStep : SchurStep :=
  _root_.UpperTheory.Reformulated.B.SchurIrreducible.schurStep

end PI.UnitaryGroupMassFormula.CommMult
end

