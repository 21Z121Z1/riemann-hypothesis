import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0026
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingConstantEqNablaStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferRtt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightedSumDifferenceIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GammaFamilyCommuteGenerators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0027
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMatrixTransferConjTransposeCommute

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerLevelsSameScalar
section
namespace Formalism.FourierDecayAlt.P

theorem start_matrix_is_module : Formalism.FourierDecayAlt.M.StartIsStart :=
  start_module_assemble transfer_hermitian transfer_rtt transfer_determinant

theorem start_admissible_model : Formalism.FourierDecayAlt.M.StartOK :=
  start_assemble start_matrix_is_module lower_left_commute_model shift_scalar_relation shift_shift_relation rho_raise

theorem lower_levels_same_scalar : Formalism.FourierDecayAlt.M.LowerStart :=
  mx_lowerStart_of start_matrix_is_module

theorem model_words_all_levels : Formalism.FourierDecayAlt.M.ModelWords :=
  model_words_assemble word_statements_all_hold lower_levels_same_scalar sites_admissible_model model_chain
    lower_commutes

theorem model_frame : Formalism.FourierDecayAlt.M.ModelFrame :=
  model_assemble interlacing_sign q_positive_interlacing q_positive_shift cPos_true c_pos_truncated
    frame_of_admissible_word frame_eq_word_module c_diagonal level_exists_model level_star start_admissible_model
    types_interlace realPoints_statement cut_admissible

theorem model_frame_base : Formalism.FourierDecayAlt.M.ModelFrameBase :=
  model_assemble_base interlacing_sign interlace_sign_two q_positive_interlacing q_positive_shift
    c_pos_base c_pos_truncated_base frame_of_recursive_word admissible_rec_of_base_case frame_module_of_word c_diagonal
    level_exists_model level_star start_admissible_model types_interlace realPoints_statement
    cut_admissible_base

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionUpdateSums
section
namespace Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums

open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix

section Slot

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem finset_fin_two_eq_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  exact h i

def flipA (a : S) (u : Ix S) : Ix S := Function.update u a (Fin.rev (u a))

theorem flipA_invol (a : S) : Function.Involutive (flipA a) := by
  intro u
  funext b
  by_cases hb : b = a
  · subst hb; simp [flipA]
  · simp [flipA, Function.update_of_ne hb]

theorem sum_position {M : Type} [AddCommMonoid M] (a : S) (F : Ix S → M) :
    ∑ u, F u = ∑ u, if u a = 0 then F u + F (Function.update u a 1) else 0 := by
  have h1 : ∑ u, F u = ∑ u, ((if u a = 0 then F u else 0) + (if u a = 1 then F u else 0)) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rcases finset_fin_two_eq_cases (u a) with h | h <;> simp [h]
  have h2 : ∑ u, (if u a = 1 then F u else 0) =
      ∑ u, (if u a = 0 then F (Function.update u a 1) else 0) := by
    refine (Equiv.sum_comp (flipA_invol a).toPerm (fun u => if u a = 1 then F u else 0)).symm.trans ?_
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Function.Involutive.coe_toPerm, flipA, Function.update_self]
    rcases finset_fin_two_eq_cases (u a) with h | h
    · rw [h]; rfl
    · rw [h]; rfl
  rw [h1, Finset.sum_add_distrib, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> simp

theorem update_zero_of (a : S) (u : Ix S) (h : u a = 0) : Function.update u a 0 = u := by
  rw [← h]; exact Function.update_eq_self a u

theorem free_zero {a : S} {G : SlopeTestRemainingChoices S A} (hG : FreeOf a G) (u y : Ix S) (h : u a ≠ y a) :
    G u y = 0 := by
  have e := congrFun (congrFun (hG (u a) (u a)).eq u) y
  rw [Formalism.FourierDecayAlt.P.Wd1.eU_mul_apply, Formalism.FourierDecayAlt.P.Wd1.mul_eU_apply] at e
  simp only [if_true, Function.update_eq_self] at e
  rw [e, if_neg (Ne.symm h)]

theorem free_shift {a : S} {G : SlopeTestRemainingChoices S A} (hG : FreeOf a G) (u y : Ix S) (i : Fin 2) :
    G (Function.update u a i) (Function.update y a i) = G (Function.update u a 0) (Function.update y a 0) := by
  have e := congrFun (congrFun (hG i 0).eq (Function.update u a i)) (Function.update y a 0)
  rw [Formalism.FourierDecayAlt.P.Wd1.eU_mul_apply, Formalism.FourierDecayAlt.P.Wd1.mul_eU_apply] at e
  simp only [Function.update_self, if_true, Function.update_idem] at e
  exact e.symm

theorem freeOf_mul {a : S} {M N : SlopeTestRemainingChoices S A} (hM : FreeOf a M) (hN : FreeOf a N) : FreeOf a (M * N) :=
  fun i j => (hM i j).mul_right (hN i j)

theorem freeOf_io (a : S) (x : A) : FreeOf a (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  refine Matrix.ext fun z z' => ?_
  rw [Formalism.FourierDecayAlt.P.Wd1.eU_mul_apply, Formalism.FourierDecayAlt.P.Wd1.mul_eU_apply]
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h1 : z a = i <;> by_cases h2 : z' a = j
  · simp only [h1, h2, if_true]
    by_cases h3 : Function.update z a j = z'
    · have h4 : z = Function.update z' a i := by rw [← h3]; simp [← h1]
      rw [if_pos h3, if_pos h4]
    · have h4 : z ≠ Function.update z' a i := by
        intro h4; apply h3; rw [h4]; simp [← h2]
      rw [if_neg h3, if_neg h4]
  · have : Function.update z a j ≠ z' := by intro h3; apply h2; rw [← h3]; simp
    rw [if_pos h1, if_neg h2, if_neg this]
  · have : z ≠ Function.update z' a i := by intro h3; apply h1; rw [h3]; simp
    rw [if_neg h1, if_pos h2, if_neg this]
  · rw [if_neg h1, if_neg h2]

end Slot

section Vec

variable {A S V : Type} [Ring A] [Fintype S] [DecidableEq S] [AddCommGroup V] [Module A V]

theorem act_place {a : S} {G : SlopeTestRemainingChoices S A} (hG : FreeOf a G) (X : Ix S → V)
    (hX : ∀ u, u a ≠ 0 → X u = 0) (C : Fin 2 → A) (z : Ix S) :
    act G (fun u => C (u a) • X (Function.update u a 0)) z =
      act G (C (z a) • X) (Function.update z a 0) := by
  unfold act
  conv_lhs => rw [sum_position a]
  conv_rhs => rw [sum_position a]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u a = 0
  · simp only [hu, if_true, Function.update_idem, update_zero_of a u hu, Function.update_self,
      Pi.smul_apply]
    have hX1 : X (Function.update u a 1) = 0 := hX _ (by simp)
    rw [hX1, smul_zero, smul_zero, add_zero]
    rcases finset_fin_two_eq_cases (z a) with hz | hz
    · rw [free_zero hG z (Function.update u a 1) (by simp [hz]), zero_smul, add_zero,
        update_zero_of a z hz, hz]
    · rw [free_zero hG z u (by simp [hz, hu]), zero_smul, zero_add, hz]
      have e := free_shift hG z u 1
      have hz1 : Function.update z a 1 = z := by rw [← hz]; exact Function.update_eq_self a z
      rw [hz1] at e
      rw [e, update_zero_of a u hu]
  · simp [hu]

end Vec

end Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
end

