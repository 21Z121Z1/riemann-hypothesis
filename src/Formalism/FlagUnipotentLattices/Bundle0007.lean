import Formalism.FlagUnipotentLattices.Bundle0002
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ColonCountWeighted
import Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality
import Formalism.FlagUnipotentLattices.Bundle0001
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LocalIntegralStructure
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ComplexMultiplicationRoot
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.Bundle0001

-- bundled from Formalism.FlagUnipotentLattices.IdealCountLeWAsm
section
namespace Formalism.HermitianLatticeCounting.Final.S6

theorem iotaDual : Formalism.HermitianLatticeCounting.S6.IotaDual := Formalism.HermitianLatticeCounting.P.embedding_dual_compatible
theorem iotaDetermined : Formalism.HermitianLatticeCounting.S6.IotaDetermined := Formalism.HermitianLatticeCounting.P.embedding_determined_by_restriction
theorem dualIndex : Formalism.HermitianLatticeCounting.S6.DualIndex := Formalism.HermitianLatticeCounting.P.dual_lattice_index
theorem subGen : Formalism.HermitianLatticeCounting.S6.SubGen := Formalism.HermitianLatticeCounting.P.submodule_generator_count
theorem extGen : Formalism.HermitianLatticeCounting.S6.ExtGen := Formalism.HermitianLatticeCounting.P.extension_generator_count
theorem colonScale : Formalism.HermitianLatticeCounting.S6.ColonScale := Formalism.HermitianLatticeCounting.P.colon_ideal_scaling
theorem colonNorm : Formalism.HermitianLatticeCounting.S6.ColonNorm := Formalism.HermitianLatticeCounting.P.colon_ideal_norm
theorem idealCountEq : Formalism.HermitianLatticeCounting.S6.IdealCountEq := Formalism.HermitianLatticeCounting.P.ideal_count_eq
theorem idealCountLe : Formalism.HermitianLatticeCounting.S6.IdealCountLe := Formalism.HermitianLatticeCounting.P.quotient_card
theorem totientBound : Formalism.HermitianLatticeCounting.S6.TotientBound := Formalism.HermitianLatticeCounting.P.totient_bound_alt
theorem torsionBound : Formalism.HermitianLatticeCounting.S6.TorsionBound := Formalism.HermitianLatticeCounting.P.torsion_bound_alt
theorem cCount : Formalism.HermitianLatticeCounting.S6.CCount := Formalism.HermitianLatticeCounting.P.colon_count_bound
theorem cCount' : Formalism.HermitianLatticeCounting.S6.CCountAsm := Formalism.HermitianLatticeCounting.P.colon_count_of_hyp
theorem idealCountLeW : Formalism.HermitianLatticeCounting.S6.IdealCountLeW := Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted
theorem idealCountLeWAsm : Formalism.HermitianLatticeCounting.S6.IdealCountLeW' := Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted_of_hyp
theorem cCountW : Formalism.HermitianLatticeCounting.S6.CCountW := Formalism.HermitianLatticeCounting.P.colon_count_weighted
theorem cCountWAsm : Formalism.HermitianLatticeCounting.S6.CCountWAsm := Formalism.HermitianLatticeCounting.P.colon_count_weighted_of_hyp
theorem torsionBoundAsm : Formalism.HermitianLatticeCounting.S6.TorsionBoundAsm := Formalism.HermitianLatticeCounting.P.torsion_bound_of_totient
theorem quotCard : Formalism.HermitianLatticeCounting.S6.QuotCard := Formalism.HermitianLatticeCounting.P.height_loss_bound
theorem costBound : Formalism.HermitianLatticeCounting.S6.CostBound := Formalism.HermitianLatticeCounting.P.cost_bound
theorem hLoss : Formalism.HermitianLatticeCounting.S6.HLoss := Formalism.HermitianLatticeCounting.P.loss_bound_holds

end Formalism.HermitianLatticeCounting.Final.S6
end

-- bundled from Formalism.FlagUnipotentLattices.SignaturePreservingEntryNorms
section
namespace Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure

theorem torsionIndex : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TorsionIndex := Formalism.HermitianLatticeCounting.P.card_range_nsmul_mul_card_le
theorem local_integral_entries_of_signature_preserving : Formalism.HermitianLatticeCounting.LocalIntegralStructure.EntriesOfSignaturePreserving := Formalism.HermitianLatticeCounting.P.unipotent_upper_entries
theorem perpCompl : Formalism.HermitianLatticeCounting.LocalIntegralStructure.PerpCompl := Formalism.HermitianLatticeCounting.P.orthogonal_complement_formula
theorem cofactorVec : Formalism.HermitianLatticeCounting.LocalIntegralStructure.CofactorVec := Formalism.HermitianLatticeCounting.P.cofactor_vector_formula
theorem zZgPreserve : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZgPreserve := Formalism.HermitianLatticeCounting.P.integer_group_preservation
theorem localCongr : Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocalCongr := Formalism.HermitianLatticeCounting.P.local_congruence_condition
theorem sInt : Formalism.HermitianLatticeCounting.LocalIntegralStructure.SInt := Formalism.HermitianLatticeCounting.P.s_integrality
theorem thmB : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ThmB := Formalism.HermitianLatticeCounting.P.theorem_B_statement

theorem gramDetGen : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramDetGen := Formalism.HermitianLatticeCounting.P.gram_determinant_general
theorem gramDet : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramDet := Formalism.HermitianLatticeCounting.P.gram_determinant_formula
theorem gramNondeg : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramNondeg := Formalism.HermitianLatticeCounting.P.gram_matrix_nondegenerate
theorem denomNormFrac : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DenomNormFrac := Formalism.HermitianLatticeCounting.P.denominator_norm_fraction
theorem arithmetic_square_bound_fourth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductInequalitySq := Formalism.HermitianLatticeCounting.P.L4_arithmetic_square
theorem arithmetic_square_bound_fifth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductPlacesInequalitySq := Formalism.HermitianLatticeCounting.P.L5_arithmetic_square

theorem volRatio : Formalism.HermitianLatticeCounting.LocalIntegralStructure.VolRatio := Formalism.HermitianLatticeCounting.P.volume_ratio_formula
theorem constProduct : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ConstProduct := Formalism.HermitianLatticeCounting.P.constant_product_formula
theorem tcritForm : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TcritForm := Formalism.HermitianLatticeCounting.P.critical_threshold_form

end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
end

