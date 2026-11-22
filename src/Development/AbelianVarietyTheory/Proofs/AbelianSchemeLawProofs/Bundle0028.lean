import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsLineBundlePowEqPow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GoodPtOfIrredOfMulPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsUnitIffMem
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqIdOfFixesTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws5
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVarietyStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cube_theorem_and_sections_finite_growth_abelianVariety : (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (∀ j : ℕ, Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) ∧ ∃ N c C : ℕ, 1 ≤ N ∧ 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ P.g ≤ c * Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ∧ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ≤ C * t ^ P.g) := by
  first | exact @GlobalTheory.AbLaw.CubeAssembly.cube_and_sections | exact GlobalTheory.AbLaw.CubeAssembly.cube_and_sections | (intros; apply GlobalTheory.AbLaw.CubeAssembly.cube_and_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.AllLaws

theorem laws_of_h0_eq_one :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1) → Laws ∧ Laws2 := by
  intro h1
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  obtain ⟨g, rig, pbc, lemB, cext⟩ := GlobalTheory.laws_without_cohomology
  obtain ⟨cg, fin, grow⟩ := GlobalTheory.AbLaw.CubeAssembly.cube_and_sections
  obtain ⟨cube, square, mulPull, kerPow, weil, symLift, nondeg, charPair, mulq, rel⟩ :=
    GlobalTheory.AbLaw.FromCube.all_of_cubeGen cg
  have sq := (GlobalTheory.AbSquare.square_of_cube cg).1
  have neg := GlobalTheory.exists_gen_negLB g
  have mp := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1
  have ker := (GlobalTheory.kerPow_of_square sq).1
  have lft := (GlobalTheory.kerPow_of_square sq).2.2
  have sym := (GlobalTheory.symLift_odd g lft neg).1
  have wc := GlobalTheory.weilIs_iff_commIsOf_and_lift_subsingleton g lft sym
  have w₃ := GlobalTheory.weilIs_alternating_skew_natural g lft
  have act := GlobalTheory.thetaGrp_acts_linearly g
  have gal := GlobalTheory.torsion_invariant_descends mulq
  have tw := GlobalTheory.twisted_pow_translate sq mulq
  have proj := GlobalTheory.AbLaw.polAV_veryAmpleBy pbc
  have h0 : GlobalSectionsRankAlgClosed := GlobalTheory.FinrankGrowthBounds.finrank_sections_lineBundlePow_eq_pow gi h1 rel grow mulq
  have mulN : MulNSt := GlobalTheory.mulN_of_decomposition mulq rel h0 pbc
  have h0T := (GlobalTheory.secM_invariant_eq_bot_or_univ_at_geometric_point pbc).1 h0
  have van := GlobalTheory.AbLaw.PowVanish.first_cohomology_vanishes_powers proj GlobalTheory.T.serre_vanishing_very_ample.1 GlobalTheory.AbLaw.h1Zero_of_isIso mp mulq gal
  obtain ⟨sbcAny, sbc⟩ := GlobalTheory.AbLaw.SecBC.secBaseChange_of_perf GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj proj van
    GlobalTheory.AbLaw.h1Zero_of_isIso GlobalTheory.exists_matrix_basis_ker_of_exact_at_point pbc h0T
  have stw : SecTwistSt := GlobalTheory.SecTwist.secTwist_of_perf GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj proj van
    GlobalTheory.AbLaw.h1Zero_of_isIso GlobalTheory.exists_matrix_basis_ker_of_exact_at_point pbc h0T tw
  have irred : IrredSt :=
    GlobalTheory.irredSt_of_heis act wc GlobalTheory.heisenberg_family_irreducible weil w₃ nondeg mulN h0
  have irrT := (GlobalTheory.secM_invariant_eq_bot_or_univ_at_geometric_point pbc).2 irred
  have gen := GlobalTheory.NoBasePoint.exists_sec_value_isUnit gi sq h0T mulq
  have mono := GlobalTheory.SepPoints.eq_of_forall_value_eq gi cg sbc mulq
  have ample : AmpleSt :=
    GlobalTheory.VeryAmplePow.ample (GlobalTheory.exists_sections_span_affine sbc) gen mono
  have goodPt : GoodPtSt := GlobalTheory.GoodPoint.goodPt_of_irred gi irred act ker mp mulq gen
  have vv := GlobalTheory.VVRank.vvRank sbcAny irrT mp lft act ker pbc mulq
  have finOrd := GlobalTheory.TorsionFixedAut.eq_id_of_fixes_torsion g symLift act wc irred h0 ample kerPow
  have sep := GlobalTheory.EndDivisible.eq_one_of_forall_pow_dvd gi mp fin
  have serreK := GlobalTheory.SerreField.serre_algClosed mulq
    (GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one mulq) sep finOrd
    GlobalTheory.eq_one_of_pow_eq_one_of_congr_one
  have serre : SerreSt := GlobalTheory.serre_of_algClosed pbc g GlobalTheory.local_rigidity serreK
  have ext : Semi.extend_existsSt.{0} :=
    GlobalTheory.ExtendRig.extend_exists gi GlobalTheory.isRegularRing_of_smooth
      (GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
        GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
        GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE)
      GlobalTheory.exists_lineBundle_extension
  have quot : QuotientSt :=
    GlobalTheory.quotient_isAbelianScheme_of_quotientScheme gi
      (GlobalTheory.exists_quotient_scheme_of_finite_flat_subgroup GlobalTheory.FiniteFlatKilled.main
        (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal) mulq)
  exact ⟨⟨h0, sbc, ample, kerPow, mulPull, mulN, cube, square, rig, weil, nondeg, symLift, irred,
    goodPt, serre, ext, cext, lemB, GlobalTheory.EvVal.evValSt, vv, g, pbc, quot, GlobalTheory.unramExt_law⟩,
    ⟨sbcAny, stw, charPair, GlobalTheory.smoothDense⟩⟩

end GlobalTheory.AbLaw.AllLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsThirdToSixthOfLaws
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem laws_third_to_sixth_of_laws :
    Laws → DVR.TwistBaseChangeStatement → Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 :=
  fun h ht =>
    ⟨laws3, uniformisationLaws_of_baseChange_laws h.polBaseChange h.globalFns h.secBaseChange ht,
      laws5 h.globalFns h.secBaseChange,
      lawsSixth_of_unifUniq h.globalFns h.secBaseChange h.ample⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PowEqOneOfLocalLift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLawsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws

theorem theta_pt_pow {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S}
    (θ : ThetaGrp P.A P.L (k : ℤ) T) : θ.pt ^ k = 1 := by
  refine ((GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube
    GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).1 S P k T θ.pt).1 ?_
  intro p
  refine ⟨⊤, trivial, (GlobalTheory.KerPow.pull_iff _ _ _).2 ?_⟩
  exact GlobalTheory.KerPow.HasGen.pull ⟨θ.φ, θ.isGen⟩ _ fun _ => rfl

theorem pow_eq_one_of_local_lift {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} (x : T ⟶ P.A)
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp P.A P.L (k : ℤ) (overRes V), θ.pt = overResι V ≫ x) : x ^ k = 1 := by
  ext1
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hV, θ, hθ⟩ := h p
  refine ⟨V, hV, ?_⟩
  have e : overResι V ≫ (x ^ k) = overResι V ≫ (1 : T ⟶ P.A) := by
    rw [MonObj.comp_pow, MonObj.comp_one, ← hθ, theta_pt_pow]
  exact congrArg (fun q => q.left) e

theorem mem_tors_of_weilIs {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs P.A P.L (k : ℤ) x y c) :
    x ∈ tors P T k ∧ y ∈ tors P T k := by
  constructor
  · refine pow_eq_one_of_local_lift P k x fun p => ?_
    obtain ⟨V, hV, ⟨θx, θy, hx, -⟩, -⟩ := h p
    exact ⟨V, hV, θx, hx⟩
  · refine pow_eq_one_of_local_lift P k y fun p => ?_
    obtain ⟨V, hV, ⟨θx, θy, -, hy⟩, -⟩ := h p
    exact ⟨V, hV, θy, hy⟩

section Clauses

variable {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (T : Over S)

end Clauses

def unitSpecEquiv (K : Type) [CommRing K] : Kˣ ≃* Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
  Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.toMulEquiv

end GlobalTheory.PairingLawsCompare
end
end

