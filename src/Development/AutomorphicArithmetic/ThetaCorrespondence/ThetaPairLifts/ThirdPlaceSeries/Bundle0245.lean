import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0042
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0166
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0244
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0161
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3579
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0198
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0149
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0144
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0142
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0145
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0154
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0143
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremPublishedInputsThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0152
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0229
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0231
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0211
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringBadLocusOfDescentSteps
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop
theorem covering_bad_locus_of_descent_steps_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral →
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal →
    _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition →
    _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.LiftBadSet := by
  intro hX hP hGD hQ hST hTF hSA hGC hGr hEx hDG hS hF hD hSh
  have h1 := _root_.GlobalTheory.T.lifts_badAt_last_of_green_cuspidal hP hGC hGr
  have h2 := _root_.GlobalTheory.T.covers_badAt_of_deep_good_size_flat_degree hX hP hGD hQ hST hTF hSA hGC hGr hDG hS hF hD hSh
  unfold _root_.GlobalTheory.CovTop.LiftBadSet _root_.GlobalTheory.CovTop.LiftsCondition
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at h2
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at h1
  unfold _root_.GlobalTheory.CovTop.DeepExistence _root_.GlobalTheory.CovTop.LiftsCondition at hEx
  refine ((h1.and h2).and hEx).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩, ⟨C3, -, e3⟩⟩ := h
  obtain ⟨x0, e⟩ := (e1.and e2).and e3
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := e x hx hle ι p hp
  rcases Nat.lt_or_ge ((i : ℕ) + 1) (Fm.D x ι).R.m with hlt | hge
  · obtain ⟨Y, hY⟩ := a3 i hlt
    exact a2 i hlt Y hY
  · exact a1 i (le_antisymm (Nat.succ_le_of_lt i.isLt) hge)
end GlobalTheory.CovTop
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBadSet_of_deep_size_flatDeg_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.LiftBadSet := by
  first | exact @_root_.GlobalTheory.CovTop.covering_bad_locus_of_descent_steps_alt | exact _root_.GlobalTheory.CovTop.covering_bad_locus_of_descent_steps_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_bad_locus_of_descent_steps_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HilbertSamuelLowerBoundOfComponents
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.ShortRoad
set_option maxHeartbeats 1000000 in
theorem hilbertSamuel_of_component_estimates_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree →
    _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverHeightSum := by
  intro hX h2 hGD hQd hSi hTo hSA hDG hS hF hDe hSh
  obtain ⟨Cp, hCp, htw⟩ := _root_.GlobalTheory.T.twisted_bundle_degree_lower_bound h2
  have hrk := _root_.GlobalTheory.T.twisted_flat_bundle_ranks h2
  have hgood := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  refine Closed.imp (((((((_root_.GlobalTheory.T.exists_degree_parameters_bound_alt_alt hX h2 hGD hQd hSi hTo hSA hDG hS hF).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS)).and hS).and hF).and
    hDe).and hSh) ?_
  intro eps Fm CH _ H
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _, hR⟩, _, _, hZ⟩, _, _, hQu⟩, CS, _, hSz⟩, _, _, hFl⟩, _, _, hDg⟩, _, _, hSr⟩ := H
  refine ⟨10000 + 2 * Cp, by positivity, ?_⟩
  obtain ⟨x0, H⟩ := ((((((hR.and hZ).and hQu).and hSz).and hFl).and hDg).and hSr)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨hR, hZ⟩, hQu⟩, hSz⟩, hFl⟩, hDg⟩, hSr⟩ := H x hx hle ι p hp
  set PP := (Fm.parT x hx ι).PP
  set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ with hPdef
  obtain ⟨hp1, hq1, hfin, hqe, hanti, ⟨w, hw, huM⟩, -⟩ := hQu i hi
  obtain rfl := hqe u1 hu1
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, hflat, -, hZPP, hTPP, hzb, hz2, -, -⟩ := hZ i hi Y hY
  obtain ⟨hb1, hbU, -, -, -, hbPP, hSq⟩ := hSz i
  obtain ⟨hT, hρ, -, -⟩ := (hSq hi).2 _ hu1
  have hY1 := hY.1
  have hAG := hgood (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (P.wt (lenT p i PP))
    (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P (lenT p i PP) (fun τ => (hanti τ).1) (by omega) hp1 hq1 τ).1)
    (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P (lenT p i PP) (fun τ => (hanti τ).1) (by omega) hp1 hq1 τ).2)
  have hFZ := hFl i hi Y hY
  have hrkZ := (hrk (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 _ hFZ).1
  have htwZ := htw (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (Fm.L x ι).sc.L hL1 hM hfs hfr (le_of_eq (by rw [zBase]))
    _ hFZ (by rw [abs_neg]; exact hflat) (P.wt (lenT p i PP)) w
  have hDf : 1 ≤ CompHt.dimFlag (dat p i) := by
    rw [GlobalTheory.CovTop.WtShape.dim_eq]
    exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hz1 : 1 ≤ zBase (Fm.L x ι) := by
    unfold zBase
    have a : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have b : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hPP1 : 1 ≤ PP := (one_le_pow₀ hz1).trans hZPP
  have hLz : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    unfold zBase
    have a : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have b : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hz12 : zBase (Fm.L x ι) ≤ zBase (Fm.L x ι) ^ 12 := le_self_pow₀ hz1 (by norm_num)
  have hlb : Real.log (Fm.L x ι).sc.b ≤ PP := by
    rw [Formalism.BasicNotions.Scale.b, Real.log_exp]
    linarith
  have hT1 : (1 : ℝ) ≤ (lenT p i PP : ℝ) := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hsq : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ (Fm.L x ι).sc.b by linarith)
    have := Real.one_le_sqrt.2 hb1
    nlinarith
  have hZb : zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.b := by
    have a1 : zBase (Fm.L x ι) ^ 2 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hz1 (by norm_num)
    have a2 : PP ≤ (lenT p i PP : ℝ) * PP := le_mul_of_one_le_left (by linarith) hT1
    exact a1.trans (hZPP.trans (a2.trans (hTPP.trans hsq)))
  have hkap : 0 ≤ kap p i := le_of_lt (pos_of_mul_pos_right (by linarith) (by linarith : (0 : ℝ) ≤ PP))
  have hz0 : 0 ≤ zed p i PP P.u₁ := by
    unfold zed
    exact mul_nonneg (by norm_num) (add_nonneg (by positivity) (mul_nonneg (by positivity) hρ))
  have hDf0 : (0 : ℝ) < CompHt.dimFlag (dat p i) := by exact_mod_cast hDf
  refine ⟨26 * (26 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 + 2 * zed p i PP P.u₁ * lenT p i PP),
    4000 * (Fm.L x ι).sc.b + 2 * (Cp * zBase (Fm.L x ι) ^ 2), by positivity, by positivity, ?_, fun Z => ?_⟩
  · have hA := GlobalTheory.hilbertSamuel_ALogA_le (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (Fm.L x ι).sc.b (zed p i PP P.u₁) hDf (by omega)
      hPP1 hb1 hlb hTPP hz0 hz2
    have e1 := mul_le_mul_of_nonneg_left hZb hCp
    have e2 := mul_le_mul_of_nonneg_left hbU (by positivity : (0 : ℝ) ≤ 10000 + 2 * Cp)
    nlinarith
  obtain ⟨n, Λ, β, ΛD, ΛT, J, hn, hΛ, hβ, hΛD, hΛT, hln, hlβ, hlδ, hlΛ, hlΛD, hlΛT, hJ, hcl⟩ := hR i hi Y hY Z
  obtain ⟨δ0, hδ0, hδ⟩ := hDg i hi Y hY _ hu1
  have hdg : 1 ≤ Y.dg P.u₁ Z := by
    have h0 : (0 : ℝ) < Y.dg P.u₁ Z := hδ0.trans_le (hδ Z).1
    simp only [Deep.dg] at h0 ⊢
    exact Nat.one_le_cast.2 (Nat.cast_pos.1 h0)
  have hsh := hSr i hi Y hY _ hu1 Z
  rw [huM, hrkZ] at hsh
  have hbin : (1 : ℝ) ≤ binT p i PP := by
    unfold binT
    exact Nat.one_le_cast.2 (Nat.choose_pos (by omega))
  have hd : 0 < Y.rkC (P.wt (lenT p i PP)) Z := by nlinarith [hsh.1]
  have htwz := htwZ Z hw (hAG.2 Z)
  rw [← huM] at htwz
  exact GlobalTheory.CovHSNum.deg_bound_of_claim_numbers (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (kap p i) (Fm.L x ι).sc.b (zed p i PP P.u₁)
    (CompHt.rhoB (dat p i) P.u₁) n Λ β ΛD ΛT J (Y.dg P.u₁ Z) (Y.ht P.u₁ Z) (Y.rkC (P.wt (lenT p i PP)) Z)
    (Y.degC (P.wt (lenT p i PP)) Z) (Y.degC (uM p i) Z) (Cp * zBase (Fm.L x ι) ^ 2) hDf hT hPP1 hb1 hlb hTPP rfl hρ hz2 hzb
    hkap hn hΛ hβ hΛD hΛT hdg hd hln hlβ hlδ hlΛ hlΛD hlΛT hJ hsh.2 hcl (by positivity) (by rw [zBase]; exact htwz)
end GlobalTheory.CovTop.ShortRoad
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverHeightSum_of_flatDeg_coverDegree_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverHeightSum := by
  first | exact @_root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates_alt | exact _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates_alt | (intros; apply _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpenOrbitOfUnramifiedExponents
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.S0.Open0ProofU
theorem open_orbit_of_unramified_exponents_alt : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) := by
  intro P hL cDep
  have hNE : ∀ K B f T w Z Wt p0 t nch n xd c, _root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩
  have hB : ∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z) := fun _ q => q.x.nx.2.1.2.down
  have hPA := _root_.GlobalTheory.T.linkedAt_hPA_prmR hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hDc := _root_.GlobalTheory.T.linkedAt_hDcPtG_prmR hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hTie := _root_.GlobalTheory.T.linkedAt_tie_of_nonempty_extensionWithLaw P.discreteSeriesCover P.harishChandraModules P.casselmanWallach P.weilRepresentationUnitaryPair
    P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hNE
  have hJ := _root_.GlobalTheory.T.entries_combined_real_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hPA hDc hTie
  have hMi := _root_.GlobalTheory.T.main_theorem_published_inputs_third_alt_alt P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules P.casselmanWallach
    GlobalTheory.Hk3.howeUnram_holds P.weilRepresentationUnitaryPair P.weilSiegelFormulaUnitary P.siegelWeilUnitaryConvergent
    P.doublingMethod P.unramifiedDoublingGL P.discreteSeriesClassification P.strongApproxSU P.siegelWeilUnitaryConvergent2
    hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hDiv := _root_.GlobalTheory.T.bk_law_entries_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.discreteSeriesCover P.harishChandraModules P.casselmanWallach hL _ SExt.none (geoCl anyGeometry) hB hMi.1
  have hLam := _root_.GlobalTheory.T.real_group_inputs_combined_alt_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass P.dixmierMalliavinFactorisation
    P.flathFactorisation
    P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hKap := _root_.GlobalTheory.T.harish_chandra_inputs_combined_alt_alt P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass
    P.dixmierMalliavinFactorisation P.flathFactorisation P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal
    hL _ SExt.none (geoCl anyGeometry) hLam
  have hGood := _root_.GlobalTheory.T.linked_bundles_good_of_local_langlands_alt_alt (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hNE
  have hLab := _root_.GlobalTheory.T.good_ft_entries_alt_alt (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing hL _ SExt.none (geoCl anyGeometry) hNE hGood.1
  have hGeo := _root_.GlobalTheory.T.linkedAt_geometricWeakTies_of_tie P.rayClassFieldSt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hNE hDiv hTie
  have hDf := _root_.GlobalTheory.T.weil_unitary_entries' P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  exact ⟨hPA, hLam, hDiv, hDc, hJ, hTie, hLab, hGood.2, hGeo, hMi.2, hKap, hDf⟩
end GlobalTheory.Fc.S0.Open0ProofU
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open0_of_unitary_group_hypotheses : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) := by
  first | exact @_root_.GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt | exact _root_.GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt | (intros; apply _root_.GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt <;> assumption)
end
end
end

