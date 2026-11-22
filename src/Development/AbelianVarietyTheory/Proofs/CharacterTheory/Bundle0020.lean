import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharactersStatement
section
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_virtualCharacters_iff_sub_characters : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L), f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  first | exact @GlobalTheory.BI.mem_virt_iff_sub | exact GlobalTheory.BI.mem_virt_iff_sub | (intros; apply GlobalTheory.BI.mem_virt_iff_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.TraceLiftMonomialMatrixEqSumEigenvaluesStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_lift_monomialMatrix_eq_sum_eigenvalues : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n N : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → (N : k) ≠ 0 → (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k) ^ N = 1 → (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) ^ N = 1 → Matrix.trace (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) = ((Matrix.charpoly (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k)).roots.map θ).sum := by
  first | exact @GlobalTheory.MonoTrace.trace_lift_monomial | exact GlobalTheory.MonoTrace.trace_lift_monomial | (intros; apply GlobalTheory.MonoTrace.trace_lift_monomial <;> assumption)
end

