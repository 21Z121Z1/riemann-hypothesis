import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0041
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0122
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0242
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0216
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0237
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0094
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0161
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0219
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainTheoremPublishedInputsVariantStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0243
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0174
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadComponentsIndefinite
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
noncomputable section
namespace GlobalTheory.BadIndef
set_option maxHeartbeats 1000000 in
theorem bad_components_indefinite_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i _ _ _ => BadAt p i := by
  intro hX hP hGD hQ hS hT hSA hGr hG hDG hSz hFD hDg hSh
  have hB := _root_.GlobalTheory.T.cover_type_lattice_comparison_alt hP hG hDG
  have hW := _root_.GlobalTheory.T.local_share_number_bound_alt hP hGr
  have hE := _root_.GlobalTheory.T.bad_embedding_locus_covered_by_regular_alt hX hP hGD hQ hS hT hSA hG hDG hSz hFD hDg hSh
  refine Formalism.MainNotions.Closed.imp (((hB.and hW).and hE).and hDG) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩, ⟨C4, -, x4, h4⟩⟩
  refine ⟨0, le_rfl, max (max x1 x4) (max x2 x3), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hle
  have l4 : x4 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨ψ₀, hψ₀, hsh⟩ := h2 x hx l2 ι p hp i
  obtain ⟨fr, π, s, ρ, χ, Pb, lam, ψ, lamb, H, hsp, hwh, hlb, hhalf, hPb, hH, hρ, hrkT, hrkB⟩ :=
    h1 x hx l1 ι p hp i hi Y hY
  have hemb := fun k => h3 x hx l3 ι p hp i hi Y hY fr π ρ χ Pb lamb H hPb hH hρ k
  choose n hn1 hn2 using hemb
  have hgd := (h4 x hx l4 ι p hp i hi Y hY).1
  haveI : FiniteDimensional Y.d.c₂.F (Y.V (Gk p i)) := finiteDimensional_of_lat _ hgd.2.1 hgd.2.2
  obtain ⟨S, hSg, hbd⟩ := GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker (Fm.D x ι) _ _ π s hsp ρ Pb lam ψ hwh lamb hlb H hhalf n (3 / 2) hn1 hn2 ψ₀ hψ₀
  have hs := hsh S hSg
  have e0 : (0 : ℝ) ≤ Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := Nat.cast_nonneg _
  have e1 : 0 ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := (Real.exp_pos _).le
  have k1 := mul_le_mul_of_nonneg_right hs e0
  have k2 := mul_nonneg e1 e0
  have key : (Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) : ℝ) ≤
      3 * Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) := by
    rw [hrkT, hrkB]
    refine hbd.trans ?_
    linarith
  exact key
end GlobalTheory.BadIndef
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
theorem _root_.GlobalTheory.T.covers_badAt_of_deep_good_size_flat_degree : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i _ _ _ => BadAt p i := by
  first | exact @_root_.GlobalTheory.BadIndef.bad_components_indefinite_alt | exact _root_.GlobalTheory.BadIndef.bad_components_indefinite_alt | (intros; apply _root_.GlobalTheory.BadIndef.bad_components_indefinite_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDegreeParametersBound
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
namespace GlobalTheory.HSShortRun
open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}
set_option maxHeartbeats 1000000 in
theorem hsClaim_short_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ n Λ β ΛD ΛT J : ℝ, 1 ≤ n ∧ 1 ≤ Λ ∧ 1 ≤ β ∧ 1 ≤ ΛD ∧ 1 ≤ ΛT ∧ Real.log n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ Real.log ΛD ≤ PP * kap p i ∧ Real.log ΛT ≤ PP * kap p i ∧ J ≤ 4 * (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1) + lenT p i PP * PP) + 2 * PP * (kap p i / lenT p i PP) * CompHt.dimFlag (dat p i) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 (lenT p i PP) (CompHt.dimFlag (dat p i)) n 1 Λ β ΛD ΛT J (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.ht (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) (Y.degC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) := by
  intro hX h2 hG hQ hS hK hL hDG hSz hF
  have hP := _root_.GlobalTheory.T.covering_topology_refinement h2
  have H₄ := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  have H₃ : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg
      (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
    apply _root_.GlobalTheory.T.log_dg_u1_le_of_flatDeg <;> assumption
  refine Closed.imp (Closed.and (Closed.and (Closed.and (_root_.GlobalTheory.T.hilbertSamuel_bergman_frame_bound_alt h2 hDG hSz hF) (_root_.GlobalTheory.T.birOn_weightPair_both_components_alt hX hG hQ hS h2 hSz))
    (Closed.and H₃ _root_.GlobalTheory.HSApp.wtBig_run_alt)) (Closed.and (Closed.and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz) (_root_.GlobalTheory.T.size_bounds_for_family_alt hSz))
    (Closed.and (_root_.GlobalTheory.T.short_vectors_span_cusp_lattice_alt h2 hDG hSz hF) (_root_.GlobalTheory.T.short_path_weight_bound_alt h2 hDG hSz hF)))) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨_, -, a₃⟩, _, -, a₄⟩, ⟨⟨_, -, a₅⟩, _, -, a₆⟩, ⟨_, -, a₇⟩, _, -, a₈⟩
  obtain ⟨x0, a⟩ := (((a₁.and a₂).and (a₃.and a₄)).and ((a₅.and a₆).and (a₇.and a₈)))
  clear a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY Z => ?_⟩
  obtain ⟨⟨⟨a₁, a₂⟩, a₃, a₄⟩, ⟨a₅, a₆⟩, a₇, a₈⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨⟨f₂⟩, f₁, Λ, β, hΛ, hβ, hn, hlβ, hlΛ, hfr, hberg⟩ := a₁ i hi Y hY Z
  have hW := a₄ i hi
  obtain ⟨hp1, hq1, hE, -⟩ := a₅ i hi
  obtain ⟨hLaw, hIn, -, -, -, -, -, -, -, -, -, -, hPP, -⟩ := a₆ i hi Y hY
  obtain ⟨hPk, hsh⟩ := a₈ i hi Y hY
  have hg := gapGe_wt_of_wtBig hW
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hPP
  have hκ0 : 0 ≤ kap p i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨c₁, c₂⟩ := _root_.GlobalTheory.HSShortRun.hilbertSamuel_estimate_at_level hP hG hQ h2.q15 h2.q16 hS hK.toroidalChartsForFan hL hY.1 hE Z hW
    (fun j _ => (H₄ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1 _ (fun τ => antitone_of_gapGe (by positivity) (hg j) τ)
      (fun τ => le_trans (by omega) (hg j τ ((dat p i).p - 1) (by omega)))).1)
    hPP0 hκ0 f₂ f₁ hΛ hβ hfr hberg (a₂ i hi Y hY Z) (a₇ i hi Y hY Z) (hsh Z)
  refine ⟨f₁.n, Λ, β, _, _, _, c₁, hΛ, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk, hn, hlβ, a₃ i hi Y hY Z, hlΛ,
    (Real.log_exp _).le, (Real.log_exp _).le, ?_, c₂⟩
  have e₁ : 0 ≤ CompHt.dimFlag (dat p i) * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
    positivity
  have e₂ : 0 ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP := by positivity
  have e₃ : 0 ≤ 2 * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP) * CompHt.dimFlag (dat p i) := by
    positivity
  linarith
end GlobalTheory.HSShortRun
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
theorem _root_.GlobalTheory.T.exists_degree_parameters_bound_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ n Λ β ΛD ΛT J : ℝ, 1 ≤ n ∧ 1 ≤ Λ ∧ 1 ≤ β ∧ 1 ≤ ΛD ∧ 1 ≤ ΛT ∧ Real.log n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ Real.log ΛD ≤ PP * kap p i ∧ Real.log ΛT ≤ PP * kap p i ∧ J ≤ 4 * (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1) + lenT p i PP * PP) + 2 * PP * (kap p i / lenT p i PP) * CompHt.dimFlag (dat p i) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 (lenT p i PP) (CompHt.dimFlag (dat p i)) n 1 Λ β ΛD ΛT J (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.ht (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) (Y.degC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) := by
  first | exact @_root_.GlobalTheory.HSShortRun.hsClaim_short_alt_alt | exact _root_.GlobalTheory.HSShortRun.hsClaim_short_alt_alt | (intros; apply _root_.GlobalTheory.HSShortRun.hsClaim_short_alt_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremPublishedInputsVariant
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem miStarRowClosing_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  intro hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hDiag hL p hRX
  exact _root_.GlobalTheory.T.main_theorem_published_results_final_alt_alt hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hDiag hL p hRX
    (_root_.GlobalTheory.T.point_lines_of_cusp_rapid_decay hDSC hHCM hCW hHCF hCusp hL p)
end GlobalTheory
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_published_inputs_variant_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  first | exact @_root_.GlobalTheory.miStarRowClosing_alt_alt | exact _root_.GlobalTheory.miStarRowClosing_alt_alt | (intros; apply _root_.GlobalTheory.miStarRowClosing_alt_alt <;> assumption)
end
end
end

