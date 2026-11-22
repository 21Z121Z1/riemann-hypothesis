import Mathlib
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Bundle0001
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Bundle0003
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Bundle0002
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.CutPlace
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LemmaC
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.AprimeCuts
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.DescentEstimateDownUp
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LinExtEqZeroOfMemExt
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LevelsModConstIffOfDownDown

namespace Formalism.ExponentWindows

theorem descent_lemmas_all_hold : SatDist ∧ ConstDist ∧ CoprimeProd ∧ KillerShift ∧ InvConst ∧ DUConst ∧ MNone ∧ CutPlace ∧ LemmaCValR ∧ Rounding ∧ AprimeCuts ∧ MDU ∧ MD ∧ UnivPart ∧ Descent ∧ MUD ∧ MDD :=
  ⟨mem_span_pow_of_uniformizer_mul, pow_dvd_of_const_mem_span, coprimeProd_statement, aeval_sub_eval_one_smul_mem, exists_fixed_add_of_sub_mem, unit_constant_holds, levels_mod_const_iff_of_no_down, exists_cuts_of_sparse_thick, lemma_C_valuation_real, filtration_rounding, exists_cuts_exponent_bounds, descent_estimate_down_up, descent_estimate_down, exists_complement_adapted, mem_span_of_frobenius_mem_span, descent_estimate_up_down, levels_mod_const_iff_of_down_down⟩

end Formalism.ExponentWindows
