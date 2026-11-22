import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0004
import Formalism.FormalDegreeBessel.StatementIO
import Formalism.FormalDegreeBessel.StatementDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0009

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiCapelliStatement
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def negL (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => -Lhol (Matrix.single a b 1) F z

theorem real_EabV (ε : Fin n → Bool) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.REAL.EabV ε a b f = EabV ε a b f := rfl

def PsiCapelliStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ), IsMu lam μ →
    ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) (PsiM T μ) g =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • PsiM T μ g

def PsiAllCapStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        opGelfand (rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
        opGelfand (rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)) ∧
      (∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma toMK_mul' (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma toMK_one' : toMK (1 : KG ε) = 1 := rfl

lemma op_mul' (T : KType ε Λ) (k k' : KG ε) : T.op (k * k') = T.op k * T.op k' := by
  show ((T.τ (k * k') : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_mul]
  rfl

lemma op_one' (T : KType ε Λ) : T.op 1 = 1 := by
  show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
  rw [map_one]
  rfl

lemma toMK_mul_inv' (k : KG ε) : toMK k * toMK k⁻¹ = 1 := by rw [← toMK_mul', mul_inv_cancel, toMK_one']

lemma toMK_inv_mul' (k : KG ε) : toMK k⁻¹ * toMK k = 1 := by rw [← toMK_mul', inv_mul_cancel, toMK_one']

theorem psiM_kexp (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    PsiM T μ (toMK k * NormedSpace.exp X) = T.op k * psM T μ (NormedSpace.exp X) := by
  have h : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧
      toMK k * NormedSpace.exp X = toMK k' * NormedSpace.exp X' := ⟨k, X, hX, rfl⟩
  obtain ⟨hk, hXX⟩ := polar_unique hX h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  rw [PsiM, dif_pos h, ← hXX, ← hk]

theorem psiM_equiv (T : KType ε Λ) (μ : Fin n → ℤ) (k₁ k₂ : KG ε) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    PsiM T μ (toMK k₁ * g * toMK k₂) = T.op k₁ * PsiM T μ g * T.op k₂ := by
  obtain ⟨k, X, hX, rfl⟩ := polar_exists hg
  obtain ⟨hX', hexp⟩ := inP_conj k₂⁻¹ hX
  rw [inv_inv] at hX' hexp
  have hc := psM_conj T μ k₂⁻¹ (NormedSpace.exp X)
  rw [inv_inv] at hc
  have hg' : toMK k₁ * (toMK k * NormedSpace.exp X) * toMK k₂ =
      toMK (k₁ * k * k₂) * NormedSpace.exp (toMK k₂⁻¹ * X * toMK k₂) := by
    rw [hexp, toMK_mul', toMK_mul']
    simp only [_root_.mul_assoc]
    rw [← _root_.mul_assoc (toMK k₂) (toMK k₂⁻¹), toMK_mul_inv', _root_.one_mul]
  rw [hg', psiM_kexp T μ _ hX', psiM_kexp T μ k hX, hexp, hc, op_mul', op_mul']
  simp only [_root_.mul_assoc]
  rw [← _root_.mul_assoc (T.op k₂) (T.op k₂⁻¹), ← op_mul', mul_inv_cancel, op_one', _root_.one_mul]

theorem psiM_one (T : KType ε Λ) (μ : Fin n → ℤ) : PsiM T μ 1 = 1 := by
  have h0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by
    first | exact ⟨by simp [inG], by simp⟩ | exact ⟨by first | exact inG_zero ε | exact inG_zero, by simp⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = toMK (1 : KG ε) * NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [toMK_one', NormedSpace.exp_zero, one_mul]
  rw [h1, psiM_kexp T μ 1 h0, op_one', one_mul, NormedSpace.exp_zero]
  first | exact psM_one T μ | exact psM_one | simp [psM_one]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

