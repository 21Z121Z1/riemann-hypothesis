import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0005
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0006
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProduct
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LatticeGeneratedLowestWeight
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SplittingThirdPartHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NonemptyDvrSettingOfStandard
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0005
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0021
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0020
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumSingleApplyZero
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0022
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.M0LeBwOfIsW
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.BfamAtWLetterEq

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities
section
namespace Formalism.MainNotions.G.ColumnFamilies.Top

open Formalism.MainNotions.CovariantDegrees

theorem b1 (D : Formalism.BasicNotions.D7) : PathPairCorrespondence D := path_pair_correspondence D
theorem b2 (D : Formalism.BasicNotions.D7) : admB2 D := admissible_standard_basis D
theorem b3 (D : Formalism.BasicNotions.D7) : admB3 D := admissible_thm_B1 D
theorem b4 (D : Formalism.BasicNotions.D7) : ColumnFamilyLowerSet D := admissible_thm_B2 D
theorem b5 (D : Formalism.BasicNotions.D7) : GenericProjectionCriterion D := admissible_thm_B3 D
theorem b6 (D : Formalism.BasicNotions.D7) : ColumnFamilyClosure D := column_family_closure D
theorem b7 (D : Formalism.BasicNotions.D7) : TensorColumnFamily D := admissible_B7 D
theorem b8 (D : Formalism.BasicNotions.D7) : BranchingColumnFamily D := admissible_thm_C3 D
theorem b9 (D : Formalism.BasicNotions.D7) : GlobalSectionsSchur D := global_sections_schur D
theorem b10 (D : Formalism.BasicNotions.D7) : BracketPolynomialSpan D := bracket_polynomial_span D
theorem b11 (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := adm_eleven D
theorem b12 (D : Formalism.BasicNotions.D7) : NestedTypeBound D := adm_twelve D
theorem b14 (D : Formalism.BasicNotions.D7) : JointComponentsPaths D := adm_fourteen D
theorem b15 (D : Formalism.BasicNotions.D7) : SaturatedLowerSetSpan D := admissible_lowerSet_span D
theorem b16 (D : Formalism.BasicNotions.D7) : PairedPathIndependence D := admissible_externalProduct D
theorem b17 (D : Formalism.BasicNotions.D7) : PathBasisOverRing D := admissible_standardPath_basis D
theorem b18 (D : Formalism.BasicNotions.D7) : FirstLettersLowerSet D := admissible_word_basis D
theorem b19 (D : Formalism.BasicNotions.D7) : WeylDualityLattice D := admissible_lattice_biduality D
theorem a2 (D : Formalism.BasicNotions.D7) : PathColumnBasis D := admissible_polynomial_basis D
theorem HyperplaneRank (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D := admissible_polynomial_basis_prov D
theorem Conclusion2 (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.Conclusion2 D := splitting_package_holds D

end Formalism.MainNotions.G.ColumnFamilies.Top
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree
section
namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem second_estimate_of_restrictions (D : Formalism.BasicNotions.D7) (h41 : DiscriminantNonzeroModUniformiser) (h45 : AdmB D → GeneratorModuloUniformiser 1088)
    (hLam : AdmB D → RestLam 1088) (hPad : RestPad 1088) (hSum : RestSum 1088 1)
    (hMem : AdmB D → RestMem 1088) (hInd : AdmB D → RestInd 1088)
    (hT1 : AdmB D → GoodPathWeight 1088) (hMon : RestMon 1088) : SecondPartClosed D :=
  second_estimate_of_rank_bound D 1088 1 (by norm_num) (by norm_num) restDeg restSel fun hA =>
    restRank_of 1088 1 h41 (h45 hA)
      (restCount_of 1088 1 (hLam hA) (restSeg_of 1088 (hMem hA) (hInd hA) restFin (hT1 hA) hMon) hPad hSum)

theorem restMon : RestMon 1088 := restMon_of 1088 beta_ratio_bound tau_degree_on_path_bound residue_class_count

theorem restInd (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestInd 1088 := restInd_of 1088 (restKey_of D hAdm 1088)

theorem secondPartClosed (D : Formalism.BasicNotions.D7) : SecondPartClosed D :=
  second_estimate_of_restrictions D discriminant_nonzero_mod_uniformiser (fun hA => generator_modulo_uniformiser_of_adm D hA 1088 (by norm_num))
    (fun hA => restLam_of D hA 1088 restLamDeg)
    restPad restSum (fun hA => restMem_of D hA) (fun hA => restInd D hA) (fun hA => good_path_weight D hA) restMon

end Formalism.MainNotions.SelectionLemmas.Pf
end

