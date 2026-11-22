import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0763
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0144
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0145
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0758
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0137
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0770
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0604
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0603
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0077
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemGoodLIffOfStateStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_goodL_iff_iotaR_mem_goodW : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ θ : (∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ), (∀ kk, θ kk ≠ 1) → LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → ∀ j, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v : (SOf x).WL j, (v ∈ goodL (Dof x) (SOf x) θ j ↔ GlobalTheory.EigSpanDesc.iotaR x.m.z.R (idxOf (Dof x) j) v ∈ GlobalTheory.EigRows.goodW x.m.z.R.toRealDat x.m.z.F.lv2 (idxOf (Dof x) j)) := by
  first | exact @_root_.GlobalTheory.EigSpanTie.mem_goodL_iff_iotaR_mem_goodW_of_level_psi | exact _root_.GlobalTheory.EigSpanTie.mem_goodL_iff_iotaR_mem_goodW_of_level_psi | (intros; apply _root_.GlobalTheory.EigSpanTie.mem_goodL_iff_iotaR_mem_goodW_of_level_psi <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelSt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem modelSt_alt : _root_.GlobalTheory.ShareOn.ModelStatement := by
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and _root_.GlobalTheory.ShareOn.p0_extreme_or_archOn_of_runModel _root_.GlobalTheory.BigOn.typePrimes_gt_three_r_alt) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and hx0.1 hx0.2
  refine ⟨x0, fun x hx hle ι p hrows hmore r hr hown i => ?_⟩
  obtain ⟨harch, hg⟩ := hx0 x hx hle ι p hrows
  obtain ⟨C, hfin, hact, M, ka, hRM⟩ := exists_runModel p hmore r hr hown i
  have hb0 : 0 < badN (Fm.D x ι) := by
    obtain ⟨v, -⟩ := hRM
    exact (GlobalTheory.TrivLevel.badN_pos_iff _).2 (hmore.2.1.fieldAt v).bad
  obtain ⟨hcard, ρ, σ, f, h1, h2, h3, h4⟩ :=
    Reading.reading_of_runModel p r hr i M ka hb0 (Fm.parT x hx ι).nV_ge hRM
  exact ⟨C, hfin, hact, M, ka, ρ, σ, f, h1, h2, h3, h4, levelCondition_restrict_of_halfUnipotent p r hr i M ka (hg hmore) hRM, hcard,
    harch hmore r hr hown i C M ka hRM⟩
end GlobalTheory.ShareOn
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtAdLStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mtAd_psiVectorLocal_of_yRel : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0), YRel L Y → ∃ ad : MtAd Y (_root_.GlobalTheory.HeightCounting.Fin3.localMultiplicityFamily L l), ad.PV = _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l := by
  first | exact @_root_.GlobalTheory.HeightCounting.Fin3.exists_mtAd_psi_vector_of_yRel | exact _root_.GlobalTheory.HeightCounting.Fin3.exists_mtAd_psi_vector_of_yRel | (intros; apply _root_.GlobalTheory.HeightCounting.Fin3.exists_mtAd_psi_vector_of_yRel <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpec
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
def Mv.ndSpec_alt {big} {L : LocAll (lay0 D)} (x : NdSpec A.pl M C big L.X L.T) : NdSpec (m.sideA_alt A).pl (m.mt M) (m.ch C) big (m.loc L).X (m.loc L).T := @_root_.GlobalTheory.HeightCounting.NdSpec.mk (_) (_) (_) (_) (_) (_) (_)
    (iq := (by with_unfolding_all exact (x.iq :)))
    (iq_alg := (by with_unfolding_all exact (x.iq_alg :)))
    (iq_LL := (by with_unfolding_all exact (x.iq_LL :)))
    (iq_big := (by with_unfolding_all exact (x.iq_big :)))
    (B := @_root_.Formalism.L2.NLocBase.mk (_) (_)
      (Oc := (by with_unfolding_all exact (x.B.Oc :)))
      (ringOc := (by with_unfolding_all exact (x.B.ringOc :)))
      (domOc := (by with_unfolding_all exact (x.B.domOc :)))
      (dvrOc := (by with_unfolding_all exact (x.B.dvrOc :)))
      (ec := (by with_unfolding_all exact (x.B.ec :)))
      (ec_w := (by with_unfolding_all exact (x.B.ec_w :)))
      (V := (by with_unfolding_all exact (x.B.V :)))
      (acgV := (by with_unfolding_all exact (x.B.acgV :)))
      (modV := (by with_unfolding_all exact (x.B.modV :)))
      (modVO := (by with_unfolding_all exact (x.B.modVO :)))
      (towV := (by with_unfolding_all exact (x.B.towV :)))
      (iV := (by with_unfolding_all exact (x.B.iV :)))
      (iV_basis := (by with_unfolding_all exact (x.B.iV_basis :)))
      (Qc := (by with_unfolding_all exact (x.B.Qc :)))
      (hL := (by with_unfolding_all exact (x.B.hL :)))
      (hL_def := (by with_unfolding_all exact (x.B.hL_def :)))
      (hK := (by with_unfolding_all exact (x.B.hK :)))
      (hK_def := (by with_unfolding_all exact (x.B.hK_def :)))
      (split := (by with_unfolding_all exact (x.B.split :)))
      (Qc_over := (by with_unfolding_all exact (x.B.Qc_over :)))
      (Qc_conj := (by with_unfolding_all exact (x.B.Qc_conj :))))
    (Q_eq := (by with_unfolding_all exact (x.Q_eq :)))
    (mx := (by with_unfolding_all exact (x.mx :)))
    (mx_max := (by with_unfolding_all exact (x.mx_max :)))
    (mx_inj := (by with_unfolding_all exact (x.mx_inj :)))
    (mx_all := (by with_unfolding_all exact (x.mx_all :)))
    (phO := (by with_unfolding_all exact (x.phO :)))
    (phK := (by with_unfolding_all exact (x.phK :)))
    (phK_alg := (by with_unfolding_all exact (x.phK_alg :)))
    (phK_emb := (by with_unfolding_all exact (x.phK_emb :)))
    (Psi := (by with_unfolding_all exact (x.Psi :)))
    (Psi_inj := (by with_unfolding_all exact (x.Psi_inj :)))
    (Psi_range := (by with_unfolding_all exact (x.Psi_range :)))
    (Psi_pr := (by with_unfolding_all exact (x.Psi_pr :)))
    (ptX := (by with_unfolding_all exact (x.ptX :)))
    (ptX_hT := (by with_unfolding_all exact (x.ptX_hT :)))
    (iotaC := (by with_unfolding_all exact (x.iotaC :)))
    (iotaC_coh := (by with_unfolding_all exact (x.iotaC_coh :)))
    (Qc_eq := (by with_unfolding_all exact (x.Qc_eq :)))
    (std := (by with_unfolding_all exact (x.std :)))
    (act_hK := (by with_unfolding_all exact (x.act_hK :)))
    (twOf_eq := (by with_unfolding_all exact (x.twOf_eq :)))
    (twSide_eq := (by with_unfolding_all exact (x.twSide_eq :)))
    (psi_eq := (by with_unfolding_all exact (x.psi_eq :)))
    (twO_alg := (by with_unfolding_all exact (x.twO_alg :)))
    (tw_reads := (by with_unfolding_all exact (x.tw_reads :)))
    (heckeLoc_gamma_places := (by with_unfolding_all exact (x.heckeLoc_gamma_places :)))
    (nbr := (by with_unfolding_all exact (x.nbr :)))
    (nbr_ind := (by with_unfolding_all exact (x.nbr_ind :)))
    (self_good := (by with_unfolding_all exact (x.self_good :)))
    (nbr_iq := (by with_unfolding_all exact (x.nbr_iq :)))
    (bj := (by with_unfolding_all exact (x.bj :)))
    (bj_span := (by with_unfolding_all exact (x.bj_span :)))
    (bj_rel := (by with_unfolding_all exact (x.bj_rel :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPointStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetNum_nCol_lenT_bounds_of_quo : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → JetNum (Fm.D x ι) (DF (dat p i) (aOf p i u1)) (1 / 2500) ∧ 2 * (Fm.D x ι).R.r ≤ nCol (dat p i) ∧ (lenT p i PP : ℝ) * (Real.log ((Fm.D x ι).host.g 0) + Real.log ((Fm.D x ι).host.g 1)) ≤ C * unitE p := by
  first | exact @_root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point | exact _root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point | (intros; apply _root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParameterOfDiscreteSeriesRay
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 4000000 in
private theorem logLam_of_part_pz : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D →
    ∀ (X : DivX D), LamAre Z X → ∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    X.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e)) ∧ R.EEp3 c ≠ ⊥ := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost X hX i π c e he hne hle
  have rat := GlobalTheory.T.complexSpan_rationalLiftForms_eq_basePart h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_familyLabel_containing_finiteTypeParts h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost π
  obtain ⟨lab, hl, hv⟩ := hX
  have hov : OverIx Z π (lab π) := hl π ⟨p, fun j => by
    rw [rat j p]
    exact Submodule.map_le_iff_le_comap.1 (hp.1 j)⟩
  have hi := hov i
  rw [rat i (lab π)] at hi
  have hc : c = lab π := GlobalTheory.Mem.R3.ScalarComponentUnique.part_unique R F cG X0 Y hP hH i π c (lab π) hne hle hi
  refine ⟨?_, fun hb => ?_⟩
  · rw [(hv i π e he).1 hne, hc]
    rfl
  · have hW : R.Wp3 i c = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun s hs => ?_)
      have hs' : R.EEc s ≤ R.EEp3 c := le_iSup₂_of_le (f := fun s (_ : R.Carries c s) => R.EEc s) s hs le_rfl
      rw [hb] at hs'
      exact absurd (le_bot_iff.1 hs') hs.1
    apply hne
    refine eq_bot_iff.2 fun x hx => ?_
    have h0 : Y.mj.eW i x ∈ R.Wp3 i c := hle hx
    rw [hW] at h0
    have hx0 : Y.mj.eW i x = 0 := (Submodule.mem_bot ℂ).1 h0
    have hn1 := Y.mj.eW_norm i x
    rw [hx0, norm_zero, zero_pow two_ne_zero] at hn1
    have hn : (0 : ℝ) < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have hn2 : ‖x‖ ^ 2 = 0 := (mul_eq_zero.1 hn1.symm).resolve_left hn.ne'
    exact (Submodule.mem_bot ℂ).2 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hn2))
set_option maxHeartbeats 4000000 in
private theorem logLam_twArgs_pz : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t), HostHyp (w.st Z).toD7 → ∀ (X : DivX (w.st Z).toD7), LamAre t.r.Z X →
    letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (w.st Z).toD7.R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (w.st Z).toD7.what₂.LL →+* ℂ), e ≠ (w.st Z).toD7.what₂.embLL → (w.st Z).toD7.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (w.st Z).toD7.what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro h1 h2 h3 h4 K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a hHost X hX
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  intro i π c e he hne hle
  have hW : Y.mj.eW = t.r.Y.mj.eW := by kexactB eq_of_heq heW
  have hle' : (w.st Z).toD7.what₂.isot ((i : ℕ) + 1) π ≤ (t.r.z.R.Wp3 i c).comap (t.r.Y.mj.eW i) := by
    rw [← hW]
    kexactB hle
  have h := logLam_of_part_pz h1 h2 h3 h4 t.r.z.R t.r.z.F t.r.z.cG _ t.r.Y t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange hHost X hX i π c e he hne hle'
  kexactB h.1.trans (congrArg Real.log (lam_eq i _ c (InfinitePlace.mk e) h.2).symm)
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.parameter_of_discrete_series_ray_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ), e ≠ (q.w.D q.Z).what₂.embLL → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a
  exact logLam_twArgs_pz h4 h5 h6 hCRD K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
    (hHost (q.w.st q.Z) q.x.isOver).1 q.O.X q.x.ox.lam
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenMatchStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_line_family_value : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (n : Fin a.n) (hj : (a.G n).s + 1 ≤ B.R.m),
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads →
    ∀ (α : J.Ch (a.G n).s) (γ : J.Ch ((a.G n).s + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z,
      B.embLL (Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P 1
        (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 (a.G n).s (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P) (GlobalTheory.QTw.homOf I l Z (a.G n).s hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2))) = c * _root_.GlobalTheory.Fam.PenLoc.penXi_alt a n z := by
  first | exact @_root_.GlobalTheory.Fam.PenLoc.pen_match_alt | exact _root_.GlobalTheory.Fam.PenLoc.pen_match_alt | (intros; apply _root_.GlobalTheory.Fam.PenLoc.pen_match_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhtOn
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.phtOn_alt {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {fr : Formalism.L2.OmFrame D} (x : PhtOn A.wd fr fun _ _ _ _ => True) : PhtOn (m.sideA_alt A).wd (m.omFrame fr) fun _ _ _ _ => True := @_root_.GlobalTheory.HeightCounting.PhtOn.mk (_) (_) (_) (_) (_)
    (card := (by with_unfolding_all exact (x.card :)))
end
end GlobalTheory.LayerMove
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkValOfBWitStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valEqv_of_bWit_std : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.x.what₂.r.z.Std → ∃ cv, _root_.GlobalTheory.TopVal.ValEqvAlt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv ∧ _root_.GlobalTheory.TopVal.PackageValuation (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv := by
  first | exact @_root_.GlobalTheory.TopVal.pkVal_of_bWit_alt | exact _root_.GlobalTheory.TopVal.pkVal_of_bWit_alt | (intros; apply _root_.GlobalTheory.TopVal.pkVal_of_bWit_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointRead
section
set_option synthInstance.maxHeartbeats 200000

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
namespace GlobalTheory.DefRead
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
set_option maxHeartbeats 1000000 in
theorem point_read_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) (hg : GramAt p i)
    (hfree : ∀ k : Fin 2, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH D k) X)
      (A : X → Submodule ℂ (VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), ∀ v ∈ A y, repAt p i (h : G0g D.nd) v ∈ A (h • y)) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
      (π : Γ →* G0g D.nd) (s : G0g D.nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ)
      (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ)
      (H : Fin 2 → Subgroup (G0g D.nd)), IsSplit π s ∧ IsWhit D Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧
      (∀ k, IsHalf D k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X)
        (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
        ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧
      Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧
      Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) := by
  classical
  obtain ⟨lam, ψ, hW, hlam, -⟩ := _root_.GlobalTheory.ShareOn.isWhit_and_eq_embLL_inv_and_halfUnip D L hT Gi Gl Kc Y0 cX ex Csz p hp.1
  have hfin : Finite (G0g D.nd) := Finite.of_equiv _ (p.R.eG.trans p.cG).toEquiv
  let e := p.R.eG.trans p.cG
  let Pb := p.P.P0.map e.toMonoidHom
  let lamb : Pb.comap (MonoidHom.id (G0g D.nd)) →* ℂˣ :=
    lam.comp (MulEquiv.subgroupCongr (Subgroup.comap_id Pb)).toMonoidHom
  have hEig : eig (repAt p i) (Pb.comap (MonoidHom.id (G0g D.nd))) lamb =
      eig (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi) (p.F.lv2.lvl false).P
        ((Units.map D.what₂.embLL.toMonoidHom).comp (p.F.lv2.lvl false).ψ⁻¹) := by
    ext v
    rw [mem_eig, mem_eig]
    constructor
    · intro h g
      have hm : e g ∈ Pb := ⟨g, g.2, rfl⟩
      have := h ⟨e g, hm⟩
      rw [repAt_apply] at this
      simp only [e, MulEquiv.symm_apply_apply] at this
      rw [this]
      congr 2
      exact Units.ext (hlam g hm)
    · intro h γ
      obtain ⟨g, hg, hge⟩ := γ.2
      have := h ⟨g, hg⟩
      rw [repAt_apply]
      have h1 : (p.R.eG.trans p.cG).symm (γ : G0g D.nd) = g := by
        rw [MulEquiv.symm_apply_eq]; exact hge.symm
      rw [h1, this]
      congr 2
      apply Units.ext
      have h2 := hlam ⟨g, hg⟩ ⟨g, hg, rfl⟩
      have h3 : lamb γ = lam ⟨e g, ⟨g, hg, rfl⟩⟩ := by
        show lam ⟨(γ : G0g D.nd), _⟩ = _
        congr 1
        exact Subtype.ext hge.symm
      rw [h3, h2]
      rfl
  refine ⟨G0g D.nd, inferInstance, hfin, VAt p i, inferInstance, inferInstance, inferInstance, MonoidHom.id _, MonoidHom.id _,
    repAt p i, Pb, lam, ψ, lamb, GlobalTheory.BadCount.Inh.halfH D, ⟨fun g => rfl, fun g γ hγ => ?_⟩, hW, fun γ => rfl,
    fun k => GlobalTheory.BadCount.Inh.isHalf_halfH D k, fun k => ?_, ?_, ?_⟩
  · have : γ = 1 := hγ
    subst this; simp
  · obtain ⟨X, hX, hXd, hact, A, hf, hA, hc⟩ := hfree k
    let f : (GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd)) →* GlobalTheory.BadCount.Inh.halfH D k :=
      { toFun := fun h => ⟨h.1, h.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    letI : MulAction ((GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd))) X := MulAction.compHom X f
    refine ⟨X, hX, hXd, this, A, fun h y hy => ?_, hA, fun h y v hv => hc (f h) y v hv⟩
    have := hf (f h) y hy
    exact Subtype.ext (congrArg Subtype.val this)
  · have hC := _root_.GlobalTheory.T.gram_MK_spans_of_gramAt p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _) = _
    rw [hB.1, typeSubspace_eq_iInf_ker, hA.1, hEig]
  · have hC := _root_.GlobalTheory.T.gram_MK_spans_of_gramAt p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    obtain ⟨-, -, -, hc, -, -⟩ := p.grpRecPin
    have hsum : ∀ x : MonoidAlgebra ℂ (G0g D.nd), x = ∑ h, MonoidAlgebra.single h (x.coeff h) := fun x =>
      MonoidAlgebra.ext (by
        rw [MonoidAlgebra.coeff_sum]
        simp only [MonoidAlgebra.coeff_single]
        exact (Finsupp.univ_sum_single _).symm)
    have he0 : D.ntypes.e0 = ∑ g : p.P.Gp,
        MonoidAlgebra.single (e g) (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)) := by
      rw [hsum D.ntypes.e0, ← Equiv.sum_comp e.toEquiv]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hc g]
      rfl
    have hK : Representation.asAlgebraHom ((repAt p i).comp (MonoidHom.id (G0g D.nd))) D.ntypes.e0 =
        Representation.asAlgebraHom (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi)
          (∑ g, MonoidAlgebra.single g (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g))) := by
      rw [he0, map_sum, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
      have hee : (p.R.eG.trans p.cG).symm (e g) = g := MulEquiv.symm_apply_apply _ _
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, repAt_apply, hee]
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _ ⊓ (LinearMap.ker (eGood p.R.toRealDat i)).restrictScalars _) = _
    have hEG : eGood p.R.toRealDat i = ∑ g, ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g *
        (((p.R.toRealDat.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (p.R.toRealDat.FW i).ρ g := by
      unfold eGood Formalism.IndefR.Arith.FormsL.eOp; rfl
    rw [hB.2, typeSubspace_eq_iInf_ker, hEG, hA.2]
    rw [hEig, hK]
end GlobalTheory.DefRead
namespace GlobalTheory.DefRead
end GlobalTheory.DefRead
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrimitiveAtLinkedAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem Mv.herm_wCell_last_mul_mulVec_eq_of_inWb {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {rep} (x : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w ↦ (A.wdT.e w) (A.row.locR σ w)) A.row.satR) : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL m.D rep (fun σ w ↦ ((m.sideA_alt A).wdT.e w) ((m.sideA_alt A).row.locR σ w)) (m.sideA_alt A).row.satR := (by with_unfolding_all exact (x :))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumCOfDeepGood
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop Formalism.MainNotions
namespace GlobalTheory.CovTop
theorem sumC_of_deepGood_alt : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := fun h =>
  Closed.imp h fun _ _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i hi Y hY => by
    obtain ⟨-, -, -, h4, -, h6, -, h8⟩ := h x hx hle ι p hp i hi Y hY
    exact GlobalTheory.T.sum_component_degrees_div_le_latticeSlope _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left 1 _, hi.le⟩ hY.1 hY.2.1 hY.2.2 (uM p i) h4 h6 h8⟩
end GlobalTheory.CovTop
end
end

