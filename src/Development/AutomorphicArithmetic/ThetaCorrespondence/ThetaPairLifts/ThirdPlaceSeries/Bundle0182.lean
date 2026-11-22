import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0402
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3322
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0839
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0147
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0171
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0174
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0180
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0177
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RefinedSumWeightOfSizeLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0164
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0161
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0006
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0016
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGenCx
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0620
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0103
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0124

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemMonoOfColPin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NRows.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
theorem atMem_mono_of_colPin {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {P : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL}
    (hP : EvLgG P) (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T, P K B f T → KPx B f → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) →
      Nonempty (RXs t) → ColPin w → p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp (EvG.inter hP h) fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T H.1 kp w Z Wt p0 t nch n xd c a b d (H.2 kp w Z Wt p0 t nch n xd c a b d)
end GlobalTheory.NRows.AtLayer
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompareOffOwnAtRunsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigOn_comparison_at_twisted_places : (_root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) := by
  first | exact @_root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt | exact _root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt | (intros; apply _root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjRootStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_ratio_realization_same_dual_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ c : ℂ, (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
        rdAt p w j hρ' ν f = c • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.conjRoot_alt | exact _root_.GlobalTheory.BigOn.Exp.conjRoot_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.conjRoot_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExBLIsLinkedPrmR
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
theorem exBL_isLinked_prmR_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → PositionMv p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  intro hG hCov hHM hCW hW hD hH hC hA hWb hRF hL N Γ p hp hN hS hM
  have hz := _root_.GlobalTheory.T.zeta_uniform_of_extension' ⟨hCov, hHM, hCW, hH, hC⟩ hL N SExt.none Γ hN
  subst hp
  refine _root_.GlobalTheory.T.eta_size_recursion_alt hA hWb hRF hL _ ?_ ?_ ?_
  · exact witExE_of_witMv _ (GlobalTheory.T.witnesses_pass_along_set_division _ hS)
  · exact GlobalTheory.Fc.EvP.of_all fun _ K _ q => hz K q
  · exact _root_.GlobalTheory.T.local_langlands_prm_reduction_alt hG hCov hHM hCW hW hD hH hC hA hRF hL N Γ _ rfl hN hM
end GlobalTheory.Mem.Top.Bl
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisInputs
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 800000
namespace GlobalTheory.TwGalInputs
theorem galois_inputs_alt : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), _root_.UpperTheory.GalS.GalHodgeN D G.wd → BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D) ∧ BlochKatoReduction.adm2 D ∧ BlochKatoReduction.adm8 D ∧ AllGood D.nexp ∧ D.nexp.sig_all ∧ (∃ N0, BlochKatoReduction.adm9 D N0) ∧ BlochKatoReduction.adm10 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i := by
  intro hC hArt hTor D G hGH
  have h2 : BlochKatoReduction.adm2 D := _root_.GlobalTheory.TripleAdm.adm2_of_isTriple_wildOne D G.triple (GlobalTheory.T.full_degree_label_forces_trivial_wild_inertia D G.wd G.lab)
  have hF : GlobalTheory.TypeLeaf.FrobDense D :=
    GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)
  have hg := _root_.GlobalTheory.TripleLocal.adm1_adm8_selfDual_noJump_of_isTriple G.chr hF hGH h2 G.triple
  have hs := _root_.GlobalTheory.Triple.adm8_allGood_sig_of_isTriple D G.triple
  have hL := GlobalTheory.LamTie.isToricElt_of_isLamTie D _ D.ntw G.lam G.lamOk G.lamTie
  obtain ⟨N0, h9, h10, -⟩ := GlobalTheory.ToricAssembly.toric_properties hArt hTor D hL.1
  exact ⟨hg.1, h2, hg.2.1, hs.2.1, hs.2.2, ⟨N0, h9⟩, h10,
    _root_.GlobalTheory.SettingHypotheses.setHyp_of_isTriple_of_nonzeroIndexPlace hC D G.wd G.cf G.chr hGH h2 G.triple G.lam G.lamOk G.lamTie G.rank G.primes⟩
end GlobalTheory.TwGalInputs
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefinedSumWeightOfSizeLe
section
set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum
theorem refinedSum_weight_of_size_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceWeight :=
  fun hP _ hS hF => _root_.GlobalTheory.T.refW_of_prints_size_flatDeg_refTheta hP hS hF (_root_.GlobalTheory.T.refTheta_of_size_refCore hS (_root_.GlobalTheory.T.reference_core_of_size_and_sum_point hS (_root_.GlobalTheory.T.sum_pt_of_size hS)))
end GlobalTheory.RefSum
end
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refW_of_prints_deepGood_size_flatDeg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceWeight := by
  first | exact @_root_.GlobalTheory.RefSum.refinedSum_weight_of_size_alt | exact _root_.GlobalTheory.RefSum.refinedSum_weight_of_size_alt | (intros; apply _root_.GlobalTheory.RefSum.refinedSum_weight_of_size_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RhoBarOfRows
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
namespace PointStatements
section Loc
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
theorem built_anti_alt {big big' : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)} (h : ∀ w, big' w ⊆ big w)
    (hb : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L := by
  obtain ⟨Sp, hA, hs⟩ := hb
  exact ⟨{ Sp with iq_big := fun i z hz => Sp.iq_big i z (h _ hz) }, hA, hs⟩
theorem eventuallyOfBuilt_mono_withLoc {P Q : D7 → Prop} (h : ∀ L : LocAll (lay0 D), P (withLoc L) → Q (withLoc L))
    (hP : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P) : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup Q :=
  let ⟨b, hb⟩ := hP; ⟨b, fun L hL => h L (hb L hL)⟩
theorem eventuallyOfBuilt_and {P Q : D7 → Prop} (hP : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P) (hQ : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup Q) :
    _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup fun D' => P D' ∧ Q D' := by
  classical
  obtain ⟨b1, h1⟩ := hP
  obtain ⟨b2, h2⟩ := hQ
  exact ⟨fun w => b1 w ∪ b2 w, fun L hL => ⟨h1 L (_root_.GlobalTheory.HeightCounting.Up.PointStatements.built_anti_alt (fun w => Finset.subset_union_left) hL),
    h2 L (_root_.GlobalTheory.HeightCounting.Up.PointStatements.built_anti_alt (fun w => Finset.subset_union_right) hL)⟩⟩
end Loc
theorem residualIrreducibleGood_of_inputs (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (I : _root_.GlobalTheory.NRows.LinkedInputs hL D) (R : _root_.GlobalTheory.NRows.PointConditions' D) : AutomorphicSideWildInertia.ResidualIrreducibleGood D :=
  _root_.Formalism.MainNotions.AdmissibleThreePrime.residual_irreducible_of_theorem_three_prime_alt D
    ⟨R.a.tieLab, _root_.GlobalTheory.AdmTame.main_alt_alt_alt D R.a.tie0 R.a.a2 R.a.a5 (_root_.GlobalTheory.TieLabAt.main_alt_alt hL D I.P).2.1⟩
    R.a.a5 (GlobalTheory.BrauerNesbittIrr.litBNIrr _) R.c.rho R.c.dz
end PointStatements
end GlobalTheory.HeightCounting.Up
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGenCxStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_embedding_compatibility_rows_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ z ∈ twSet hρ (rdAt p w j hρ ν) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w) (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w),
  ∃ (n : ℕ) (h : Fin n → GA (Fm.D x i) (Vc (Fm.D x i) j)) (w' : Fin n → ((R2 p).cV j).W) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (κ : ℂ) (N : ℕ),
    IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) ∧ (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) ∧
    (∀ k, h k ∈ GfC (Vc (Fm.D x i) j) ∧ InCoefLat (R2 p) j (h k) (w' k)) ∧
    ∀ y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL,
      (∀ k, ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j (y k) (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) (h k) (w' k) v)) →
      rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TwCx.twGen_cx_alt | exact _root_.GlobalTheory.BigOn.Exp.TwCx.twGen_cx_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TwCx.twGen_cx_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLeStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_upper_bound_of_prints : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.twLe_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.twLe_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.twLe_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VolLevelWtConst
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem vol_level_wt_const_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ (V : ℕ → ℂ) (VT : ℂ), (∀ j, j < B.R.m → V j ≠ 0) ∧ VT ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.Vol V ∧ J.VolT VT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT
  obtain ⟨VT, hVT, hT3⟩ := _root_.GlobalTheory.T.exists_volume_constant_of_true_geometry W hW u a ha haT
  refine ⟨fun j => if h : j + 2 ≤ B.R.m then Classical.choose (_root_.GlobalTheory.T.true_geometry_chain_step_identity_alt W hW u a ha haT j h)
    else if h' : j + 1 = B.R.m then Classical.choose (_root_.GlobalTheory.T.true_geometry_chain_step_value_alt W hW u a ha haT j h') else 1, VT, ?_, hVT, ?_⟩
  · intro j hj
    by_cases h : j + 2 ≤ B.R.m
    · simp only [dif_pos h]; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_identity_alt W hW u a ha haT j h)).1
    · have h' : j + 1 = B.R.m := by omega
      simp only [dif_neg h, dif_pos h']; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_value_alt W hW u a ha haT j h')).1
  · intro t J hJ
    refine ⟨?_, hT3 t J hJ⟩
    intro j hj α
    by_cases h : j + 2 ≤ B.R.m
    · simp only [dif_pos h]; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_identity_alt W hW u a ha haT j h)).2 t J hJ α
    · have h' : j + 1 = B.R.m := by omega
      simp only [dif_neg h, dif_pos h']; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_value_alt W hW u a ha haT j h')).2 t J hJ α
end GlobalTheory.Fam
end
end

