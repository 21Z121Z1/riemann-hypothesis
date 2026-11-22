import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TotalDegreeEplus
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FirstCoefficientFacts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0005
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0006
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0010
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockInj
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0011
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0008
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0009
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WtBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0013
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bracket
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0014
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreesLargeOfStd
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0015
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0012
import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ComponentsInFiltrationContractionSingle
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.AntitoneOfAppend
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSum
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.CanonicalTranslateJetIdentity
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.PlaneGramTheoremOfLemmas
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SecondValuationOfAdmitted
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrRenExpandMonomial
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Bundle0007
import Formalism.LocalToGlobal.CharacterGerms.RowTieValK

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem closed_extendedAllConclusions {D : Formalism.BasicNotions.D7} (h3 : adm3 D) (hU : RestUp) (hL : RestLow) (hL1 : PartnersToFactors)
    (hLift : RestLift) : Closed (ExtendedAllConclusions D) :=
  have hA2 : RemainderSegmentBoundSecond D := restAlt2_of (restSegLow_of hL) (dimHH_of h3) charZeroAt
  closed_of_rests (fun _ _ _ => segment_statement_holds D _ _ _) (restFree D) (remainderSegmentBoundFirst D) (rest2 D) (restAlt3 D)
    (one_segment_of_upper_lower hU hL) hA2 (restExt_of restRk hL1 hLift hA2)

theorem dimYAt_of_adm {D : Formalism.BasicNotions.D7} (hA : admitted D) : DimYAt :=
  dimY_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 (stWeylAt D)

theorem extended_fourth_of_upper_bound {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (h : UpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    ExtendedDigitRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc j rz ry hd
  exact h X W Qq O Kf ι σ jO w hS hH hc j 0 le_rfl rz ry hd

theorem restUp_of_adm {D : Formalism.BasicNotions.D7} (hA : admitted D) : RestUp :=
  have hY := dimYAt_of_adm hA
  restUp_of blockRankAt hY charZeroAt
    (upper_count_of_top_rows (chainDim_of hY) (numBranch_of hA.2.1 hA.2.2.1) top_rows_bound_holds)

theorem fourth_bound_of_admitted {D : Formalism.BasicNotions.D7} (hA : admitted D) :
    TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc =>
      ExtendedDigitRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc ∧ Conclusion4 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => ⟨extended_fourth_of_upper_bound h, (extended_fourth_of_upper_bound h).toDigitRankBound⟩) (restUp_of_adm hA)

def Open : Prop := RestPairLift

theorem stmtEExt_of {D : Formalism.BasicNotions.D7} (h : admitted D → Open) : ExtendedClosedForm D := fun hA =>
  have hPL := h hA
  have hY := dimYAt_of_adm hA
  have hCD : ChainDimAt := chainDim_of hY
  have hNB : NumBranchAt := numBranch_of hA.2.1 hA.2.2.1
  have hT : RestTail := restTail_of hCD hNB restPairCount (restNotKeptWt_of (wtBound_of hCD) (restBracket_of (restPairFacts_of restNUp) coarse_degrees_large_holds))
  have hK2 : LeadingRowsBeyondThreshold := top_rows_bound_holds
  have hB : BlockRankAt := blockRankAt
  have hK4 : KeptBlocksBeyondThreshold := kept_blocks_holds
  have hL1 : PartnersToFactors := partners_to_factors_holds
  have hCU : RestCountUp := upper_count_of_top_rows hCD hNB hK2
  have hMU : RestMatchUp := restMatchUp_of (restFirstRows_of (restSTopRows_of hK2))
  have hCL : RestCountLow := restCountLow_of'' hCD hT hMU hK4
  closed_extendedAllConclusions hA.2.2.1 (restUp_of hB hY charZeroAt hCU) (restLow_of hB hY charZeroAt hCL) hL1 (restLift_of (restLiftVec_of hPL))

theorem stmtE_of {D : Formalism.BasicNotions.D7} (h : admitted D → Open) : ClosedFormOfAdmitted D := (stmtEExt_of h).closed_of_extended_closed

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths
section
noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

lemma adm_fourteen_of_adm {D : Formalism.BasicNotions.D7} (h : AdmB D) : JointComponentsPaths D := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma adm_sixteen_of_adm {D : Formalism.BasicNotions.D7} (h : AdmB D) : PairedPathIndependence D := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma adm_seventeen_of_adm {D : Formalism.BasicNotions.D7} (h : AdmB D) : PathBasisOverRing D := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem nested_sets_lemma_of_admitted (D : Formalism.BasicNotions.D7) (h14 : JointComponentsPaths D) (h16 : PairedPathIndependence D) : ConclusionB3 D :=
  lemma_B3 D h16 (lemma_B2 D) (integral_joint_type_sum D h14 h16)

theorem aux_of_valuationField_of_admB (D : Formalism.BasicNotions.D7) (hV : ValuationLemmaField D) (hB : AdmB D) : Conclusion2 D :=
  ⟨automorphicSideConclusion_of_pathBasis D (adm_seventeen_of_adm hB), prvA3_of_valuationField_of_admB D hV hB, prvB1_of_D7 D, lemma_B2 D,
    nested_sets_lemma_of_admitted D (adm_fourteen_of_adm hB) (adm_sixteen_of_adm hB), coefficientDependence D, canonical_translate_jet_identity D⟩

theorem hodgeTateFromSandwich (D : Formalism.BasicNotions.D7) : HodgeTateFromSandwich D := fun _ hV hB => aux_of_valuationField_of_admB D hV hB

theorem part_two_closed_form (D : Formalism.BasicNotions.D7) : SecondPartClosed D := hodgeTateFromSandwich D

theorem part_two_along_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : SecondPartFamily Fm := by
  intro _ hV hB
  obtain ⟨x0, h⟩ := hV
  exact ⟨x0, fun x hx i => aux_of_valuationField_of_admB _ (h x hx i) (hB x i)⟩

theorem part_two_closed_form_along_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : SecondPartFamilyClosed Fm := part_two_along_family Fm

end Formalism.MainNotions.LemmaBAlt
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments
section
noncomputable section

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G

theorem stmt (D : Formalism.BasicNotions.D7) {CH : ℝ} (hCH : 26 ≤ CH) : Formalism.MainNotions.PlaneGramData.Stmt D CH 2 24 60 := by
  intro p O _ _ _ _ hSet hAdm
  obtain ⟨⟨S⟩, n', hG⟩ := hSet
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hAdm
  exact Br.plane_gram_of_theorem_at S hG
    (plane_gram_theorem_of_five_lemmas le_rfl (second_valuation_of_admitted h2) (brSPAN S h3) (brPROJ S h4) (brDIG D S hG h5)
      (brDER S h6)) hCH

theorem stmtE (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaneGramData.ClosedFormOfAdmitted D :=
  ⟨26, 2, 24, 60, by norm_num, by norm_num, by norm_num, by norm_num, fun _ hCH => stmt D hCH⟩

theorem stmtEF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.PlaneGramData.FamilyClosedForm Fm :=
  ⟨26, 2, 24, 60, by norm_num, by norm_num, by norm_num, by norm_num, 0, fun _ hCH _ _ _ => stmt _ hCH⟩

theorem stmtEDF (Fm : Formalism.MainNotions.DFamP) : Formalism.MainNotions.PlaneGramData.DerivativeStatementClosedDesign Fm :=
  ⟨26, 2, 24, 60, by norm_num, by norm_num, by norm_num, by norm_num,
    fun _ _ _ => ⟨0, fun _ hCH _ _ _ => stmt _ hCH⟩⟩

end Formalism.MainNotions.PlaneGram
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsDef
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

structure IsEndo (Y : FBChart C V O dd) (φ : Pt C 1 dd) : Prop where
  int : ∀ i, IntS V (φ i)
  cc : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0
  add : comp1 φ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
    addOf Y.B.G.F (comp1 φ (pt C (n := 2) dd 0)) (comp1 φ (pt C (n := 2) dd 1))

structure GmPack (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
    (γ γ' : Fin 2 → Fin 2 → Pt C 1 dd) : Prop where
  endo : ∀ r s, IsEndo Y (γ r s)
  endo' : ∀ r s, IsEndo Y (γ' r s)
  comm : ∀ r s a, comp1 (γ r s) (Y.B.A.act a) = comp1 (Y.B.A.act a) (γ r s)
  comm' : ∀ r s a, comp1 (γ' r s) (Y.B.A.act a) = comp1 (Y.B.A.act a) (γ' r s)
  lin : ∀ r s c, linAct (γ r s) (p.e c) = p.gm (p.ty0 c) r s • p.e c
  lin' : ∀ r s c, linAct (γ' r s) (p.e c) = p.gm (p.ty0 c + p.hd) r s • p.e c
  img : ∀ r s (v : Fin dd → C), ∃ b : I0 → C, linAct (γ r s) v = ∑ c, b c • p.e c
  img' : ∀ r s (v : Fin dd → C), ∃ b : I0 → C, linAct (γ' r s) v = ∑ c, b c • p.e c
  adj : ∀ r s, IntS V (FB.expS C (ev (n := 2) ![comp1 (γ r s) (pt C dd 0), pt C dd 1] Y.h -
    ev (n := 2) ![pt C dd 0, comp1 (γ' r s) (pt C dd 1)] Y.h))

def GmPackSt (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) : Prop :=
  ∃ γ γ' : Fin 2 → Fin 2 → Pt C 1 dd, GmPack Y p γ γ'

end Formalism.L2.FormalSeriesBounds
end
end

