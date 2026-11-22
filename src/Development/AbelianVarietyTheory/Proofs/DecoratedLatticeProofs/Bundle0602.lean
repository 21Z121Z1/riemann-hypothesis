import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0563
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0545
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobalRowsOfSizeParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0457
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0380
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0461
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0598
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0519
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0594

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftOntoAll
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem ontoAll_of_classicalTheorems_and_hecke : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D :=
  fun hHC hCusp hDS hHCM hCW hHowe hWeil hSW hSWc hDoub hUnr D =>
    GlobalTheory.T.thetaLiftChain_onto_cuspForms_of_innerProduct hHC hCusp hDS hHCM hCW D
      (GlobalTheory.T.hecke_form_of_doubling hWeil hCusp hSW hSWc hDoub hUnr D)
      (GlobalTheory.T.thetaChainUpwardLift_heckeParam_transferred hCusp hHowe D (GlobalTheory.T.thetaChain_level_properties D))

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopValueVanishingUniform
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal.Inj

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem exists_fin {D : D7} (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) :
    ∃ g' : GA D V, g' ∈ GfC V ∧ finHom V g' = finHom V g ∧
      ∃ y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        y ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
        ∀ i j, (Formalism.UG.bc (swapAE D) (finHom V g')).1 i j = y.1 (finCongr hn i) (finCongr hn j) := by
  subst hn
  let z := (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).symm (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g)
  have hz : GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram z.1 = GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g :=
    (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).apply_symm_apply _
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V _ rfl
  refine ⟨z.1, z.2, congrArg Subtype.val hz, (e ⟨z.1, z.2⟩).1, (e ⟨z.1, z.2⟩).2, fun i j => ?_⟩
  rw [he]
  rfl

theorem eq_zero_of_models {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g, (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  have h1 : R.B.jR t x = 0 := by
    funext k
    obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective k
    exact (congrFun (h t x) k).symm.trans ((congrArg ((R.HX t).e (R.jX t x)) hg.symm).trans (hx g))
  have h2 : Function.Injective (R.B.jR t) := GlobalTheory.PresBasic.extL_injective (R.B.R t).pres
  exact (injective_iff_map_eq_zero (R.B.jR t)).1 h2 x h1

theorem eq_zero_of_isRes {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : Col2.TC B X) (a : I.ι) (φ : Frm I a) τ (e : I.tup a = τ)
    (ok : (Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).Ok)
    (h : IsRes φ (0 : ((Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).toCSD ok).Forms)) : φ = 0 := by
  subst e
  obtain ⟨ok', h⟩ := h
  exact (LinearEquiv.map_eq_zero_iff _).1 (eq_of_heq h)

set_option maxHeartbeats 2000000 in

theorem eq_zero_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) :
    ∀ (s : a.x.T) (φ : Frm w.I (a.x.Y.tup s)), IsRes φ (0 : a.x.A3.A.fam.amb.FR s) → φ = 0 := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  intro s φ h
  have e : w.I.tup (Y.tup s) = s.1 :=
    (congrArg w.I.tup ((congrFun hT' s).trans (t.r.tup_ix s))).trans (R3.tup_ixOf w.I s)
  exact eq_zero_of_isRes w.I _ φ s.1 e _ h

theorem exists_hasMat {D : D7} (gP : Formalism.L2.Forms.gramP D = 1) (g : GA D D.sp.X') :
    ∃ g' y, GlobalTheory.Core.Rk.Top.HasMat g' y ∧ y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) ∧
      (finHom D.sp.X').rangeRestrict g = (finHom D.sp.X').rangeRestrict g' := by
  obtain ⟨g', h1, h2, y, h3, h4⟩ := exists_fin _ _ (Formalism.L2.Forms.rankP D) g
  have h6 : y ∈ Formalism.UG.UPts _ (Formalism.L2.Forms.gramP D) _ := h3
  rw [gP] at h6
  exact ⟨g', y, ⟨h1, h4⟩, h6, Subtype.ext h2.symm⟩

theorem eq_zero_of_hasMat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (gP : Formalism.L2.Forms.gramP D = 1)
    (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) →
      (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  refine eq_zero_of_models R h t x fun g => ?_
  exact (exists_hasMat gP g).elim fun g' h1 => h1.elim fun y h2 =>
    (congrArg ((R.HX t).e (R.jX t x)) h2.2.2).trans (hx g' y h2.1 h2.2.1)

theorem eq_zero_of_pkAt {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : Col2.TC B X} {l : I.Laws} {Z : Col2.TC.Later B (I.cols l)}
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)
    (gP : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t)
    (hz : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → IsUni B y → pkAt W t x g = 0) : x = 0 := by
  exact eq_zero_of_hasMat (pk W) W.Q.charW.base.models.jX gP t x hz

set_option maxHeartbeats 1000000 in

theorem val_eq_zero : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ (t : (packB b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((packB b).P.I.tup t)) (x : (packB b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → GlobalTheory.TopVal.pkAt (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  intro hL p K q c b hw t φ x hx hz d
  have hx0 : x = 0 := eq_zero_of_pkAt (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b)
    (Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z).2.1 t x hz
  subst hx0
  obtain ⟨x, a, ax, y, -⟩ := hw
  have e : a.x = x := eq_of_heq ax
  subst e
  have h0 := eq_zero_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have key : ∀ k : Bl.RPk b.R b.S, k = Bl.rpkX y.y →
      ∀ (s : k.P.T) (φ : Frm q.w.I (k.P.I.tup s)), IsRes φ (0 : k.P.A3.A.fam.amb.FR s) → φ = 0 := by
    intro k hk
    subst hk
    exact h0
  rw [key (Bl.rpkB b) y.eq t φ hx]
  rfl

end GlobalTheory.TopVal.Inj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceLowerBoundAllMembers
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.LevLow

theorem cloudUnit_lower {x eps k f CD cD : ℝ} (hx : 1 ≤ x) (he : eps ≤ 1) (hk0 : 0 ≤ f) (hfk : f ≤ k)
    (hk : k ≤ x ^ (5 : ℝ)) (hCD : 0 ≤ CD) (hc : 11 * CD ≤ cD) :
    (k * f * x ^ eps) ^ CD ≤ ((⌈x ^ cD⌉₊ : ℕ) : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hk0' : 0 ≤ k := le_trans hk0 hfk
  have h1 : x ^ eps ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx he
  have h2 : k * f ≤ x ^ (5 : ℝ) * x ^ (5 : ℝ) := mul_le_mul hk (le_trans hfk hk) hk0 (by positivity)
  have h3 : k * f * x ^ eps ≤ x ^ (11 : ℝ) := by
    have : x ^ (11 : ℝ) = x ^ (5 : ℝ) * x ^ (5 : ℝ) * x ^ (1 : ℝ) := by
      rw [← Real.rpow_add' hx0 (by norm_num), ← Real.rpow_add' hx0 (by norm_num)]; norm_num
    rw [this]
    exact mul_le_mul h2 h1 (by positivity) (by positivity)
  calc (k * f * x ^ eps) ^ CD ≤ (x ^ (11 : ℝ)) ^ CD := Real.rpow_le_rpow (by positivity) h3 hCD
    _ = x ^ (11 * CD) := by rw [← Real.rpow_mul hx0]
    _ ≤ x ^ cD := Real.rpow_le_rpow_of_exponent_le hx hc
    _ ≤ _ := Nat.le_ceil _

theorem Dstar_mass (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    X.toD7.what₂.Dstar = StandardLattice.massI X.toD7 X.toD7.R.r * StandardLattice.idxSig X.toD7 (X.toD7.host.g 0) (X.toD7.host.g 1) *
      ∏ τ, X.toD7.dsig τ := by
  have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
  rw [e, hO.sizes.2]
  unfold DsPre
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

theorem admissibleRanks_of_mass_formula (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D)
    (hD : D.what₂.Dstar = StandardLattice.massI D D.R.r * StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ τ, D.dsig τ) :
    LocalBesselAndTopKernel.FamilyMidVolume D := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  intro V _ _ _ _ h L _
  refine ⟨fun hL u => ?_, fun hL => ?_⟩
  · have e := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
      (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
    have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.k := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.k)
    rw [em, ← Formalism.MainNotions.J.idxColTie_holds D]
    exact e
  · have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.r := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.r)
    rw [em, ← Formalism.MainNotions.J.idxRowTie_holds D, hD]

theorem eventually_le_trace : EvP fun _ K => ∀ β : BPt K, LocalBesselAndTopKernel.FamilyMidVolume β.D → (∀ u, GlobalTheory.Core.Rk.RankMu β.D u) →
    ∀ u : β.D.what₂.Word, β.O.L.sc.b ^ ((1 / 2 : ℝ) * (β.D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr β.D u := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨max c1 (11 * 40), fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD (le_trans (le_max_left _ _) hcD)
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch hch
  obtain ⟨x2, hNo⟩ := GlobalTheory.Diag.PG.NodeParameters.nodes_of_parameters eps he he52
  obtain ⟨x3, hP⟩ := GlobalTheory.T.diagonal_hypotheses_of_rows_and_window GlobalTheory.Mass.siegelMassRatio_holds GlobalTheory.DsigSize.dsigHC eps 40 he he52 (by norm_num)
    (8 * C.CGam) 40 (C.P.CYL + 1) 0 le_rfl le_rfl
  refine ⟨max (max x1 x2) (max x3 ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)), fun K hK hx β hAdm hMu => ?_⟩
  obtain ⟨hC, hcD', hch', heps, -⟩ := hK
  have hsc : β.O.L.sc = K.s := β.sc
  have hx' : max (max x1 x2) (max x3 ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)) ≤ β.O.L.sc.x := by rw [hsc]; exact hx
  have hse : β.O.L.sc.eps = eps := by rw [hsc]; exact heps
  have hv : Val C cD ch β.O.L := by
    rw [show C = K.C from hC.symm, show cD = K.cD from hcD'.symm, show ch = K.ch from hch'.symm]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx') hv
    (GlobalTheory.Plug.hostArith_bpt β)
  have hx1 : 1 < β.O.L.sc.x := β.O.L.sc.one_lt_alt
  have hX : max 2 (5 / (eps / 100)) ≤ S.XX β.O.L := by
    unfold S.XX szTh
    rw [hse]
    have h0 : (0 : ℝ) ≤ max 2 (5 / (eps / 100)) := le_trans (by norm_num) (le_max_left _ _)
    have hp : 0 < eps / 100 := by positivity
    have hyP : (max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹ ≤ β.O.L.sc.x :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx'
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hyP hp.le
    rwa [Real.rpow_inv_rpow h0 hp.ne'] at this
  have G0 := GlobalTheory.Diag.PG.Model0.globalRows_of_sizeData β.O.L N.params N.sizes ((le_max_left _ _).trans hX)
    (by unfold szTh; rw [hse]; exact (le_max_right _ _).trans hX) N.params.CCount N.params.CCount_pos le_rfl
  have e2 : N.params.CYL = C.P.CYL := congrArg (fun l : List ℝ => l.getD 19 0) N.params_K
  rw [hse, e2] at G0
  have hDel : ((β.D.s.Del : ℚ) : ℝ) = ((⌈β.O.L.sc.x ^ cD⌉₊ : ℕ) : ℝ) := by
    rw [hv.Del_eq]; unfold Delv; push_cast; rfl
  have hDl : ((β.D.R.k : ℝ) * (β.D.R.f : ℝ) * β.O.L.sc.x ^ eps) ^ (40 : ℝ) ≤ ((β.D.s.Del : ℚ) : ℝ) := by
    rw [hDel]
    exact cloudUnit_lower hx1.le (by linarith) (by positivity) G0.nums.fk G0.nums.k_hi (by norm_num)
      (le_trans (le_max_right _ _) hcD)
  have G : GlobalTheory.Diag.PG.Glob0 β.D β.O.L.sc.x eps 40 (C.P.CYL + 1) :=
    ⟨⟨G0.nums.m_lo, G0.nums.mf, G0.nums.fk, G0.nums.k_lo, G0.nums.k_hi, G0.nums.lrd_lo, G0.nums.lrd_hi, hDl,
      G0.nums.Del_hi⟩, G0.g_win, G0.gap, G0.cloud, G0.off, G0.rd_lo⟩
  have hNd := hNo β.D β.O.L N.params N.sizes hse (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx')
  have hL : β.O.L.sc.L = β.O.L.sc.x ^ eps := by rw [← hse]; rfl
  have h8 : 8 * β.O.L.CGam ≤ 8 * C.CGam := by rw [N.CGam_eq]
  have hW : GlobalTheory.Diag.PG.DuWin β.D 3 := GlobalTheory.Diag.PG.duWin_three_of_count β.D (fun u' => by
    have h := hMu u'
    unfold GlobalTheory.Core.Rk.RankMu at h
    rw [GlobalTheory.Core.Rk.d0_eq] at h
    exact h)
  obtain ⟨⟨-, hHS, -⟩, -, -, -⟩ := hP β.O.L.sc.x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx') β.D β.O.L
    hL h8 β.p.pt.xa.ties hAdm G hNd hW
  have hH := GlobalTheory.Core.Deg.hypL_of hHS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT, -, -⟩ := hH
  exact fun u => (hT u).1

theorem levelPrime_lower_at_points : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D O _ _ => ∀ u : D.what₂.Word, O.L.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr D u) := by
  intro hL p
  have hA : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => LocalBesselAndTopKernel.FamilyMidVolume D) :=
    RowE.of_all fun _ K β _ b _ _ _ =>
      admissibleRanks_of_mass_formula β.D β.O.ex.lev b.R.T.toTiedDataS.cols (Dstar_mass K β.X β.c.isOver β.c.dsig_eq)
  exact (EvP.and (RowE.and hA (GlobalTheory.Fam.MemberCount.member_rankMu hL p)) eventually_le_trace).mono
    fun _ _ _ H β hq c b hl => H.2 β (H.1 β hq c b hl).1 (H.1 β hq c b hl).2

end GlobalTheory.Core.LevLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCosetRelationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_coset_relation : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → ¬ GlobalTheory.PenBridge.plF J v → ¬ GlobalTheory.PenBridge.plF J' v → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  first | exact @GlobalTheory.PenLevTyp.uloc_le | exact GlobalTheory.PenLevTyp.uloc_le | (intros; apply GlobalTheory.PenLevTyp.uloc_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowFamilyValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Fam.PenLoc

theorem psiAt_one_eq {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ S₁ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀)
    (mu' : Formalism.L2.DIV.Tup X.F X.E X.K S₁) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu))
    (cst' : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu')) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu)
    (P' : Formalism.L2.Col.rowSG Pr sel mu') (hPP : P.1 = P'.1) (hmem : P.1 ∈ Pr.vGs) (hsh : cst.sharp = cst'.sharp)
    (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))) :
    Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y = Formalism.L2.Col.PsiAt Ch sel mu' cst' s P' 1 x y := by
  have hmem' : P'.1 ∈ Pr.vGs := hPP ▸ hmem
  unfold Formalism.L2.Col.PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one]
  unfold Formalism.L2.Col.PhiAt
  rw [if_pos hmem, if_pos hmem', hsh, hPP]

theorem lastStepPoints_sub_integral_of_uniformiser_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S S' : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (h : valuation k (((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k)) ≤ 1) (r : GlobalTheory.StepData.XIx (Fin κ) t (s + 1)) :
    S.y0 t r - S'.y0 t r ∈ 𝒪[k] := by
  unfold GlobalTheory.SymChain.SymData.y0
  by_cases hr : r = Sum.inl (Sum.inr 0)
  · subst hr
    simp only [Pi.single_eq_same]
    have h3 := neg_mem (show ((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k) ∈ 𝒪[k] from h)
    rwa [neg_sub] at h3
  · simp [Pi.single_eq_of_ne hr]

theorem pen_match : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (n : Fin a.n) (hj : (a.G n).s + 1 ≤ B.R.m),
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (t : W.P.T) (J : QJ a t), J.Reads →
    ∀ (α : J.Ch (a.G n).s) (γ : J.Ch ((a.G n).s + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z,
      B.embLL (Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P 1
        (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 (a.G n).s (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P) (GlobalTheory.QTw.homOf I l Z (a.G n).s hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2))) = c * GlobalTheory.Fam.PenLoc.penXi a n z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr row col n hj
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hd := GlobalTheory.TypePrimeUnif.intAt_div_qOf B.fields (B.primes X) (GlobalTheory.Mem.FieldsLaws.fields_ok B) (GlobalTheory.BasePrimes.primes_ok B X).1
  have hR := (hIs.tie row col).2
  have hϖ := GlobalTheory.T.valuation_uniformizer_sub_qOf_lt_of_gRead W hW u a row col hR n
  obtain ⟨S', hSame, hA'⟩ := GlobalTheory.Fam.MidLoc.exists_atType hW a hR n hϖ
  have hA : ∀ t (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → GlobalTheory.SymBridge.AtType I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL P (GlobalTheory.Fam.TopLoc.emb a n) S' :=
    fun t P hP => hA' _ P hP
  obtain ⟨e'₀, he'₀⟩ := GlobalTheory.QTw.exists_xOrd B.R (a.G n).s
  obtain ⟨e₀, he₀⟩ := GlobalTheory.QTw.exists_xOrd B.R ((a.G n).s + 1)
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℂ, C ≠ 0 ∧ ∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) (a.G n).s ≃ Fin (B.R.N (a.G n).s))
      (e : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e →
      ∀ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
      ∀ (x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N (a.G n).s) (B.R.N ((a.G n).s + 1))) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
        (S'.T (Fin B.R.t)).Psi 1 (GlobalTheory.SymBridge.toLoc (GlobalTheory.Fam.TopLoc.emb a n) e e' x₀) (fun r => GlobalTheory.Fam.TopLoc.emb a n (y' (e r))) =
          C * B.embLL (Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P 1 x₀ y') := by
    by_cases h0 : ∃ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1
    · obtain ⟨t₀, P₀, hP₀⟩ := h0
      have hA₀ := hA t₀ P₀ hP₀
      obtain ⟨C, hC0, hC⟩ := GlobalTheory.SymBridge.psiAgree_of_atType _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a.G n).ν (a.G n).unitVol hA₀ e'₀ e₀ he'₀ he₀
      refine ⟨C, hC0, fun e' e he' he t P hP x₀ y' => ?_⟩
      obtain rfl : e' = e'₀ := Equiv.ext fun r => Fin.ext ((he' r).trans (he'₀ r).symm)
      obtain rfl : e = e₀ := Equiv.ext fun r => Fin.ext ((he r).trans (he₀ r).symm)
      rw [hC x₀ y']
      congr 2
      exact psiAt_one_eq I.Ch I.sel _ _ _ _ _ P₀ P (hP₀.trans hP.symm) hA₀.mem (hA₀.sharp.trans (hA t P hP).sharp.symm) x₀ y'
    · exact ⟨1, one_ne_zero, fun _ _ _ _ t P hP => absurd ⟨t, P, hP⟩ h0⟩
  refine ⟨C⁻¹, inv_ne_zero hC0, fun t J hJ α γ P hP z => ?_⟩
  have hAt := hA t P hP
  obtain ⟨hf1, hf2⟩ := GlobalTheory.T.true_geometry_finite_family W hW u a hIs hTr n t J hJ (a.G n).s (by omega) (J.ι _ α) P hP
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.true_geometry_finite_family W hW u a hIs hTr n t J hJ ((a.G n).s + 1) (by omega) (J.ι _ γ) P hP
  refine (congrArg B.embLL (GlobalTheory.T.penultimateDatum_unchanged_frames_congruent_one I.Ch I.sel _ _ (a.G n).s P hAt.mem hAt.steps (hd P.1 hAt.mem) _ _ hf1 hf2 hg1 hg2 (homOf I l Z _ hj z) (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2))).trans ?_
  rw [eq_inv_mul_iff_mul_eq₀ hC0]
  obtain ⟨e₁, he₁, hβ₁⟩ := (hIs.stdG n).1 (a.G n).s (Nat.le_succ _)
  obtain ⟨e₂, he₂, hβ₂⟩ := (hIs.stdG n).1 ((a.G n).s + 1) le_rfl
  have hr1 : ((I.rec7 l Z).sp.X (a.G n).s).rank = B.R.N (a.G n).s := rankN (I.rec7 l Z) _ (Nat.le_of_succ_le hj)
  have hr2 : ((I.rec7 l Z).sp.X ((a.G n).s + 1)).rank = B.R.N ((a.G n).s + 1) := rankN (I.rec7 l Z) _ hj
  set e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) (a.G n).s ≃ Fin (B.R.N (a.G n).s) := e₁.trans (finCongr hr1) with he'd
  set e : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1)) := e₂.trans (finCongr hr2) with hed
  have ho' : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' := fun r => he₁ r
  have ho : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e := fun r => he₂ r
  refine Eq.trans (hC e' e ho' ho t P hP (homOf I l Z _ hj z) (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2)).symm ?_
  have hq : ((S'.ϖ : (a.G n).kˣ) : (a.G n).k) = ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k) := by
    rw [hAt.tie.compl.unif, map_natCast]
    exact congrArg (fun Q => ((Formalism.L2.Col.qOf Q : ℕ) : (a.G n).k)) hP
  have hnear : valuation (a.G n).k (((S'.ϖ : (a.G n).kˣ) : (a.G n).k) - (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
    rw [hq, Valuation.map_sub_swap]; exact hϖ
  have hinv := GlobalTheory.SymChain.UnifChange.inv_sub_inv_mem (a.G n).S.unif hnear
  have hcos : (fun r => GlobalTheory.Fam.TopLoc.emb a n (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2 (e r))) -
      S'.y0 (Fin B.R.t) ∈ box (GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1)) (1 : (a.G n).kˣ) := fun r => by
    have h1 := hJ.cosG n γ e ho r
    have h2 := lastStepPoints_sub_integral_of_uniformiser_inv (a.G n).S S' (Fin B.R.t) hinv r
    have h4 := add_mem h1 h2
    rw [sub_add_sub_cancel] at h4
    exact h4
  refine ((GlobalTheory.SymChain.atMostOne_holds (a.G n).k (a.G n).ν (a.G n).unitVol _ _ S' (Fin B.R.t)).2.2.2.1 _ _ hcos).trans ?_
  refine (hSame.2.1 _).trans ?_

  have hb : ∀ {j : ℕ} (hjj : j ≤ (a.G n).s + 1) (hr : ((I.rec7 l Z).sp.X j).rank = B.R.N j) (e₃ : GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin B.R.t) j ≃ Fin ((I.rec7 l Z).sp.X j).rank),
      ((a.G n).FX j hjj).β = (1 : Matrix _ _ (a.G n).k).submatrix id e₃ → ∀ r c,
      ((a.G n).FX j hjj).β r c = GlobalTheory.Fam.TopLoc.emb a n ((LinearEquiv.refl B.fields.E (Formalism.L2.Col.Sp B.fields.E (B.R.N j))) (Pi.single ((e₃.trans (finCongr hr)) c) 1) (finCongr hr r)) := by
    intro j hjj hr e₃ hβ r c
    rw [hβ]
    change (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (a.G n).k) r (e₃ c) = _
    rw [Matrix.one_apply, LinearEquiv.refl_apply, Pi.single_apply]
    show _ = GlobalTheory.Fam.TopLoc.emb a n (if (finCongr hr) r = (finCongr hr) (e₃ c) then 1 else 0)
    by_cases h : r = e₃ c
    · rw [if_pos h, if_pos (by rw [h]), map_one]
    · rw [if_neg h, if_neg (fun h' => h ((finCongr hr).injective h')), map_zero]
  have hfr : GlobalTheory.SymBridge.toLoc (GlobalTheory.Fam.TopLoc.emb a n) e e' (homOf I l Z _ hj z) =
      ((a.G n).FX ((a.G n).s + 1) le_rfl).γ * z.map (ofSplit (a.G n).q).pr * ((a.G n).FX (a.G n).s (Nat.le_succ _)).β := by
    have h5 := GlobalTheory.SeeSaw.StdMatch.mul_toLoc (GlobalTheory.Fam.TopLoc.emb a n) hr1 hr2 (LinearEquiv.refl _ _) (LinearEquiv.refl _ _) e' e _ _
      (hb (Nat.le_succ _) hr1 e₁ hβ₁) (hb le_rfl hr2 e₂ hβ₂) z
    let T : Matrix (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((a.G n).s + 1)) (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) (a.G n).s) (a.G n).k :=
      GlobalTheory.SymBridge.toLoc (GlobalTheory.Fam.TopLoc.emb a n) e e' (homOf I l Z _ hj z)
    have h5' : ((a.G n).FX ((a.G n).s + 1) le_rfl).β * T =
        z.map (ofSplit (a.G n).q).pr * ((a.G n).FX (a.G n).s (Nat.le_succ _)).β := h5
    have h6 : ((a.G n).FX ((a.G n).s + 1) le_rfl).γ * (((a.G n).FX ((a.G n).s + 1) le_rfl).β * T) = T := by
      rw [← Matrix.mul_assoc, Frame.γβ, Matrix.one_mul]
    refine h6.symm.trans ?_
    refine (congrArg _ h5').trans ?_
    exact (Matrix.mul_assoc _ _ _).symm
  unfold penXi
  exact congrArg (fun x => ((a.G n).S.T (Fin B.R.t)).Psi 1 x ((a.G n).S.y0 (Fin B.R.t))) hfr

end GlobalTheory.Fam.PenLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesMatchWitnessStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_places_match_witness : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ t PP, PP ∈ (pk (packB b)).Q t ↔ PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (b.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K) := by
  first | exact @GlobalTheory.Fam.qplaces_of_bWit | exact GlobalTheory.Fam.qplaces_of_bWit | (intros; apply GlobalTheory.Fam.qplaces_of_bWit <;> assumption)
end

