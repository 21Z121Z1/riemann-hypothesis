import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0993
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0731
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0707
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0755
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0757
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Transport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0758
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClassTrivialStabiliserAtTypePlace

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.OPinAt

theorem mtInput_mtL {D : D7} (L : LocAll (lay0 D)) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) (h : MtInput D M tup Q) : MtInput (withLoc L) (mtL L M) tup Q :=
  ⟨h.prod, h.para, h.uni, h.hyp, h.wt, h.rat, h.int, h.full⟩

theorem classSum_loc_of_sumTw {D : D7} {M : MtFam D} (h : SumTw D M) (i : D.nd.Loc) :
    GlobalTheory.CoefDuty.ClassSum (M.loc i) := by
  have e := D.nd.mu_w i
  have hs := h (D.nd.w i) (D.nd.w_tw i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2
  unfold MtFam.loc
  rw [e]
  exact hs

theorem mtInput_at {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) : ∃ tup Q, MtInput D a.all.gal.mt tup Q := by
  have key : ∀ (D' : D7), D' = withLoc a.nt.L → ∀ M' : MtFam D', HEq (mtL a.nt.L a.nt.M) M' →
      ∃ tup Q, MtInput D' M' tup Q := by
    rintro _ rfl M' hM
    obtain rfl := eq_of_heq hM
    exact ⟨_, _, mtInput_mtL a.nt.L a.nt.M _ _ a.nt.mt⟩
  exact key D a.nt.eq _ a.mt_eq

theorem labTie_at {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp)
    (h : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) :
    GlobalTheory.SerSys.LabTie a.nt.D fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩ := by
  have key : ∀ (D' : D7), D' = withLoc a.nt.L →
      (GlobalTheory.SerSys.LabTie D' fun k => @GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩) →
      GlobalTheory.SerSys.LabTie a.nt.D fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩ := by
    rintro _ rfl h'
    exact fun k => ⟨(h' k).1, (h' k).2⟩
  exact key D a.nt.eq h

end GlobalTheory.HeightCounting.Up.OPinAt

open GlobalTheory.HeightCounting.Up.OPinAt in

theorem GlobalTheory.HeightCounting.Up.opin_atMem : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.CoefDuty.OPin c.a := by
  intro hL
  refine EvG.imp GlobalTheory.T.twistedPlace_innerProduct_classSum_rows fun K _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hne _ hcp => ?_
  obtain ⟨m⟩ := hne
  have hs := H kp w hcp Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt
  obtain ⟨tup, Q, hin⟩ := mtInput_at c.a
  have hsum := hs c.a.all.gal.mt tup Q m.ad hin
  have hlab : GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
    fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩
  exact
    { large := m.large
      inner := classSum_loc_of_sumTw hsum
      lab := labTie_at c.a hlab
      gen := fun k => m.zeta k }

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoublingInputsImply
section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem

theorem hypH_of_rowRatW : PrM → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → RowRatW → HypH :=
  fun m hm dc cw ws sw e1 e2 ud bz so rs r =>
    hypH_of dc (GlobalTheory.hypotheses3_of_siegelWeil GlobalTheory.Hk3.howeUnram_holds m.m3 m.m4 hm dc cw ws sw e1 e2 ud bz m.m14 so) rs GlobalTheory.Published.HeckeLPartialContinuation_holds
      (GlobalTheory.Mem.R3.Rw.MultAt.atDat_multEq m.m1 m.m2 m.m3 m.m4 m.m5 m.m6 m.m7 m.m8 m.m9 m.m10 m.m11 m.m12 m.m13 m.m14) r

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabeling
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

noncomputable section

namespace GlobalTheory.HeightCounting.Up.IdempotentAdelicReading

set_option maxHeartbeats 4000000 in

theorem gaL_jV {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hr : R.grp_red_L)
    (hj : R.models_jV) (j : Fin D.R.m) (hc : (R.cV j).Is) (t : T) (y : (A.fam.L j t).S.Forms)
    (l : (R.cV j).W →ₗ[ℂ] ℂ) :
    gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A) (sg0 D A)) (fun g => l (R.extV j t (R.jV j t y) g)) =
      fun g => l (R.extV j t (R.jV j t (∑ a, (idemOf A.X).coeff a • (A.fam.L j t).r a y)) g) := by
  let Φ : (R.HV j t).H →ₗ[ℂ] (GA D (Vc D j) → ℂ) := l.compLeft (GA D (Vc D j)) ∘ₗ R.extV j t
  have hs : ∀ a, RealDat.eC (A := A) (sg0 D A) a = D.what₂.embLL ((idemOf A.X).coeff a) := fun a => by
    show sg0 D A _ = _
    rw [sg0, sgAt_mk D.what₂.embLL R.hv0]
  have key : ∀ a, Φ (R.jV j t ((A.fam.L j t).r a y)) =
      Formalism.IndefR.Links.actL (Vc D j) (R.βV j) (R.datVt j t) (R.eG a) (Φ (R.jV j t y)) := fun a =>
    (GlobalTheory.GoodModelVec.actL_coord R hr hj j hc t a y l).symm
  show gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A) (sg0 D A)) (Φ (R.jV j t y)) =
    Φ (R.jV j t (∑ a, (idemOf A.X).coeff a • (A.fam.L j t).r a y))
  rw [map_sum, map_sum]
  simp only [LinearMap.map_smulₛₗ, key, gaL, LinearMap.sum_apply, LinearMap.smul_apply, hs, RingHom.id_apply]
  rfl

set_option maxHeartbeats 4000000 in

theorem act_of_read {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    (hg : GlobalTheory.LiftRows.Given R F) {s : ℕ} (hok : A3.A.fam.Ok s) (j : Fin D.R.m) :
    ∀ (μ : D.what₂.Tup) (t : T), Y.tup t = μ → ∀ (h : Used0 D μ) (f : D.what₂.Mt μ (j.1 + 1)) (l : (R.cV j).W →ₗ[ℂ] ℂ),
      gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A3.A) (sg0 D A3.A)) (fun g => l ((Y.IL.jMt μ h j f).1 g)) =
        fun g => l ((Y.IL.jMt μ h j (D.what₂.eMt μ (j.1 + 1) f)).1 g) := by
  intro μ t ht h f l
  subst ht
  let Ψ : D.what₂.Mt (Y.tup t) (j.1 + 1) →ₗ[ℂ] (GA D (Vc D j) → ℂ) :=
    l.compLeft (GA D (Vc D j)) ∘ₗ
      ((((toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).Amt (Y.tup t) j).subtype :
        _ →ₗ[ℂ] (GA D (Vc D j) → (R.cV j).W)) ∘ₗ (Y.IL.jMt (Y.tup t) h j).toLinearMap)
  have hΨ : ∀ f, Ψ f = fun g => l ((Y.IL.jMt (Y.tup t) h j f).1 g) := fun _ => rfl
  have hF := Y.formsL j t
  have main : gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A3.A) (sg0 D A3.A)) ∘ₗ Ψ =
      Ψ ∘ₗ D.what₂.eMt (Y.tup t) (j.1 + 1) := by
    refine LinearMap.ext_on_range hF.span fun k => ?_
    have hop := hF.op_eq (Pi.single k 1)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hop ⊢
    rw [hop, hΨ, hΨ, Y.mtRead j t h, Y.mtRead j t h]
    generalize (Pi.single k 1 : Fin _ → D.what₂.LL) = x
    have hl : liftForm A3.A F.P0 F.ψ0 j t ((lE D A3.A F.P0 F.ψ0 j t).mulVec x) =
        ∑ g, (idemOf A3.A.X).coeff g • (A3.A.fam.L j t).r g (liftForm A3.A F.P0 F.ψ0 j t x) :=
      GlobalTheory.ClassSumIdentity.lvlE_lvlOp hok.conj _ ((hok.lifts j t).hpos _) _ (hok.lifts j t).act _ _ _
        (fun b => (idempotent_central _ _ A3.A.X hok.irr).2 b) x
    rw [hl]
    exact gaL_jV R hg.core.grp.red_L hg.core.models.jV j (hg.core.models.cV j) t _ l
  exact LinearMap.congr_fun main f

theorem goodIdempotent_eq_goodProjector_adelicReading {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    {cf : CharFrame D} {nch : NChoice D} (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd)
    (labPi : E.Pi → A3.A.fam.base.Ix) (hbase : R.BaseW F)
    (htup : ∀ μ, Used0 D μ → R.toLevCh.xiH (Y.tupT μ) = tp.xi μ) (hg : GlobalTheory.LiftRows.Given R F) (hf : R.FullP)
    {s : ℕ} (hok : A3.A.fam.Ok s) :
    GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead R F Y tp hC Xd E labPi hbase htup hg hf) := by
  apply GlobalTheory.NRows.Model.unitaryRealisationReading_of_idempotent_acts_via_levelGroup
  intro μ hμ j f l
  rw [← D.nStage_trivialCharacter_compat.2]
  exact act_of_read R F Y hg hok j μ (Y.tupT μ) (Y.tupTie μ hμ) hμ f l

theorem goodIdempotentReadsAsGoodTypeProjector_realOfRead : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) := by
  intro _ hL
  exact GlobalTheory.HeightCounting.Up.CoefficientAgreement.atMem_of_forall fun _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ _ _ _ _ =>
    goodIdempotent_eq_goodProjector_adelicReading _ _ _ _ _ _ _ _ _ _ _ _ t.r.intersectionNumber_baseChange.ok.ok2

end GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2DescentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarged_base_lb2_descent : PrN → SerN → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : StrictHenselianAcyclic hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : LI hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : LI hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∃ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) := by
  first | exact @GlobalTheory.HeightCounting.Up.hkCopyRestaged | exact GlobalTheory.HeightCounting.Up.hkCopyRestaged | (intros; apply GlobalTheory.HeightCounting.Up.hkCopyRestaged <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2TransportStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarged_base_lb2_transport : PrN → SerN → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : StrictHenselianAcyclic hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : LI hL x'), SameGal (Dof x) (Dof x') → ∃ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e := by
  first | exact @GlobalTheory.HeightCounting.Up.CopyEx.exists_copy | exact GlobalTheory.HeightCounting.Up.CopyEx.exists_copy | (intros; apply GlobalTheory.HeightCounting.Up.CopyEx.exists_copy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqSubfamilyOfFaceSimplicialConePrimitive
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.FaceSub

variable {X : Type} [AddCommGroup X]

theorem eq_of_toReal_sum_eq {p : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} (hu : LinearIndependent ℤ u)
    {r r' : Fin p → ℝ} (h : ∑ j, r j • toReal (u j) = ∑ j, r' j • toReal (u j)) : r = r' := by
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin p → ℤ), ∑ j, c j • u j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c hc => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hc
    exact funext (Fintype.linearIndependent_iff.1 hu c hc)
  have h0 : ∑ j, (r - r') j • toReal (u j) = ∑ k, (Fin.elim0 k : ℝ) • toReal (Fin.elim0 k : LinearMap.BilinForm ℤ X) := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self, Finset.univ_eq_empty, Finset.sum_empty]
  exact sub_eq_zero.1 (eq_zero_of_toReal_rel hind h0)

theorem eq_zero_of_toReal_eq_zero {β : LinearMap.BilinForm ℤ X} (h : toReal β = 0) : β = 0 :=
  LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.zero_apply] at this
    simpa using this

theorem exists_ray {p q : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} {v : Fin q → LinearMap.BilinForm ℤ X}
    (hu : LinearIndependent ℤ u) (hv : ∀ l, v l ≠ 0) (A : Fin q → ℝ) (B : Fin q → Fin p → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hB : ∀ l k', 0 ≤ B l k') (k : Fin p) (hk : toReal (u k) = ∑ l, A l • toReal (v l))
    (hBe : ∀ l, 0 < A l → toReal (v l) = ∑ k', B l k' • toReal (u k')) :
    ∃ l, 0 < A l ∧ ∃ c : ℝ, 0 < c ∧ toReal (v l) = c • toReal (u k) := by
  classical
  set B' : Fin q → Fin p → ℝ := fun l k' => if 0 < A l then B l k' else 0 with hB'
  have hB'0 : ∀ l k', 0 ≤ B' l k' := fun l k' => by
    simp only [hB']; split_ifs <;> [exact hB l k'; exact le_rfl]
  have hterm : ∀ l, A l • toReal (v l) = A l • ∑ k', B' l k' • toReal (u k') := fun l => by
    rcases (hA l).lt_or_eq with hl | hl
    · simp only [hB', if_pos hl]; rw [hBe l hl]
    · simp [← hl]
  have hsum : ∑ k', (if k' = k then (1 : ℝ) else 0) • toReal (u k') =
      ∑ k', (∑ l, A l * B' l k') • toReal (u k') := by
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    rw [if_pos rfl, one_smul, hk]
    simp only [hterm, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc := eq_of_toReal_sum_eq hu hsum
  have hk1 : ∑ l, A l * B' l k = 1 := by simpa using (congrFun hc k).symm
  obtain ⟨l, -, hl⟩ : ∃ l ∈ Finset.univ, A l * B' l k ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero hne] at hk1
    exact zero_ne_one hk1
  have hAl : 0 < A l := (hA l).lt_of_ne fun h0 => hl (by rw [← h0, zero_mul])
  have hoff : ∀ k', k' ≠ k → B l k' = 0 := fun k' hk' => by
    have h0 : ∑ l, A l * B' l k' = 0 := by simpa [hk'] using (congrFun hc k').symm
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_nonneg (hA l) (hB'0 l k'))).1 h0 l (Finset.mem_univ _)
    simpa [hB', if_pos hAl, hAl.ne'] using this
  have hvl : toReal (v l) = B l k • toReal (u k) := by
    rw [hBe l hAl, Finset.sum_eq_single k (fun b _ hb => by rw [hoff b hb, zero_smul]) (by simp)]
  refine ⟨l, hAl, B l k, (hB l k).lt_of_ne fun h0 => hv l (eq_zero_of_toReal_eq_zero ?_), hvl⟩
  rw [hvl, ← h0, zero_smul]

end GlobalTheory.PolFan.FaceSub

open GlobalTheory.PolFan.FaceSub in

theorem GlobalTheory.PolFan.eq_subfamily_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (hδ : ∀ i, δ i ∈ balForms bar X)
    (hγ : ∀ j, γ j ∈ balForms bar X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    LinearIndependent ℤ δ → LinearIndependent ℤ γ → (∀ i, IsPrim bar (⟨δ i, hδ i⟩ : balForms bar X)) →
    (∀ j, IsPrim bar (⟨γ j, hγ j⟩ : balForms bar X)) → (∀ j, InRCone δ (γ j)) → (∀ i, 0 ≤ h (δ i)) →
    (∀ j, h (γ j) = 0) → (∀ i, h (δ i) = 0 → InRCone γ (δ i)) →
    ∃ s : Fin n ↪ Fin m, (∀ j, γ j = δ (s j)) ∧ ∀ i, h (δ i) = 0 ↔ i ∈ Set.range s := by
  intro O _ bar X _ _ m n δ γ hδ hγ h hδi hγi hδp hγp hγc hδn hγz hZ
  classical
  choose b hb hbe using hγc
  choose a ha hae using hZ
  have hsupp : ∀ j i, 0 < b j i → h (δ i) = 0 := fun j i hji => by
    have e := apply_eq_of_toReal_eq (hbe j) h
    rw [hγz j, Int.cast_zero] at e
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hb j i) (by exact_mod_cast hδn i))).1 e.symm i
      (Finset.mem_univ _)
    have h2 : ((h (δ i) : ℤ) : ℝ) = 0 := (mul_eq_zero.1 this).resolve_left hji.ne'
    exact_mod_cast h2
  have hex1 : ∀ i, h (δ i) = 0 → ∃ j, γ j = δ i := fun i hi => by
    obtain ⟨j, -, c, hc, e⟩ := exists_ray hδi hγi.ne_zero (a i hi) b (ha i hi) hb i (hae i hi) (fun l _ => hbe l)
    exact ⟨j, GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray bar (γ j) (δ i) (hγ j) (hδ i) (hγp j) (hδp i) c hc e⟩
  have hex2 : ∀ j, ∃ i, h (δ i) = 0 ∧ γ j = δ i := fun j => by
    obtain ⟨i, hbi, c, hc, e⟩ := exists_ray hγi hδi.ne_zero (b j)
      (fun i => if hi : h (δ i) = 0 then a i hi else 0) (hb j)
      (fun i j' => by split_ifs with hi <;> [exact ha i hi j'; exact le_rfl]) j (hbe j)
      (fun l hl => by rw [dif_pos (hsupp j l hl)]; exact hae l _)
    exact ⟨i, hsupp j i hbi, (GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray bar (δ i) (γ j) (hδ i) (hγ j) (hδp i) (hγp j) c hc e).symm⟩
  choose s hsZ hsγ using hex2
  have hsinj : Function.Injective s := fun j j' hjj => hγi.injective (by rw [hsγ j, hsγ j', hjj])
  refine ⟨⟨s, hsinj⟩, hsγ, fun i => ⟨fun hi => ?_, ?_⟩⟩
  · obtain ⟨j, hj⟩ := hex1 i hi
    exact ⟨j, hδi.injective (show δ (s j) = δ i by rw [← hsγ j, hj])⟩
  · rintro ⟨j, rfl⟩
    exact hsZ j
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLargeGrid
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem evLgG_gridA_of_exGrid : ExGrid → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) := by
  classical
  intro h
  obtain ⟨CF0, hCF⟩ := h
  refine ⟨CF0, fun CF hC => ?_⟩
  refine ⟨1 / 100, by norm_num, fun eps C8 C5 c6 Cb _ _ _ _ => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF eps CF hC
  refine ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ =>
    ⟨x₀, fun K _ _ _ hKe hKx _ => ?_⟩⟩⟩⟩
  have hS := fun (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) (hΞ : Ξ.Finite) =>
    hx K.s hKe hKx P f Ξ hΞ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if hΞ : Ξ.Finite then Classical.choose (hS P f Ξ hΞ) else ∅, ?_, ?_, ?_⟩
  · intro B f F z hz
    simp at hz
  · intro B f F F₀ Ξ z hz
    by_cases hΞ : Ξ.Finite
    · simp only [dif_pos hΞ] at hz
      exact (Classical.choose_spec (hS B f Ξ hΞ)).1 z hz
    · simp [dif_neg hΞ] at hz
  · intro B f T _ hHas _ _ C W V S N G
    have hfin := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
    have hspec := (Classical.choose_spec (hS B.toPre f (T.set f) hfin)).2
    refine hspec ⟨B, C, W, V, S, N, G⟩ f (T.set f) rfl HEq.rfl HEq.rfl ?_
    intro z hz
    have h2 := hHas.2 z
    simp only [dif_pos hfin] at h2
    exact h2 hz

example : ExGrid → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) := evLgG_gridA_of_exGrid

end GlobalTheory.Mem.LiteralAutomorphy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem sizes_host_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r ∧ (∀ k, 2 * (w.D Z).R.r ≤ (w.D Z).host.g k) ∧ RootsLL (w.D Z) ∧ SphericalInertData.HypEFK (w.D Z) ∧ SphericalInertData.HypCM (w.D Z) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite) ∧ ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine EvG.imp (GlobalTheory.T.eventually_hundred_le_hermitianRank_columnChoices.inter (GlobalTheory.T.eventually_two_mul_rank_le_levelPrime.inter (GlobalTheory.T.eventually_coeffField_contains_rootOfUnity_groupOrder.inter (GlobalTheory.T.eventually_host_eq_compositum_totallyReal_imagQuadratic.inter (GlobalTheory.T.eventually_baseChangeHypotheses_columnChoices.inter (GlobalTheory.T.eventually_spacesV_definite_columnChoices.inter GlobalTheory.T.eventually_auxiliary_places_split_distinct)))))) fun K _ _ _ _ H => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H
  exact (h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))).imp fun B f T _ G hk T' w Z =>
    ⟨G.1 hk T' w Z, G.2.1 hk T' w Z, G.2.2.1 hk T' w Z, G.2.2.2.1 hk T' w Z, G.2.2.2.2.1 hk T' w Z, G.2.2.2.2.2.1 hk T' w Z,
      G.2.2.2.2.2.2 hk T' w Z⟩

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddCharCompletionOfResidueAddCharStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addChar_completion_of_residue_addChar : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (ψ' : AddChar (ZMod p) ℂ), ψ' ≠ 1 →
    ∃ ψ₀ : AddChar (v.adicCompletion K) ℂ, (∀ x, Valued.v x < 1 → ψ₀ x = 1) ∧ (∃ x, Valued.v x ≤ 1 ∧ ψ₀ x ≠ 1) ∧
      ∀ y : v.adicCompletionIntegers K, ψ₀ (y : v.adicCompletion K) = ψ' (red y) := by
  first | exact @GlobalTheory.ResidueChar.exists_addChar_completion_lift_residue | exact GlobalTheory.ResidueChar.exists_addChar_completion_lift_residue | (intros; apply GlobalTheory.ResidueChar.exists_addChar_completion_lift_residue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMapsStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_frame_family_of_holomorphic_periodMaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → (La →+ (Fin g → ℂ))) (b₀ : ReciprocityTheory.L2DbarEstimates.V d), IsOpen B → b₀ ∈ B → (∀ b ∈ B, ∀ (a : 𝓞 E) (v : La) (j : Fin g), P b (a • v) j = ty j (a : E) * P b v j) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ ρ ∈ X.Ψ, ∀ m < X.p0, ∃ j, ty j = conjEmb ρ ∧ idx j = m) → (∀ j j', ty j = ty j' → idx j = idx j' → j = j') → (∀ j, ty j ∉ X.Ψ → idx j < X.p0) → (∀ b ∈ B, ∃ x' ∈ X.dom, ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → ∃ s : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, AnalyticAt ℂ s b₀ ∧ ∀ᶠ b in 𝓝 b₀, s b ∈ X.dom ∧ ∀ x' ∈ X.dom, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat x' τ) a b' = 0) ∧ (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a b' = 0) := by
  first | exact @GlobalTheory.PeriodFamFrame.lift_frame | exact GlobalTheory.PeriodFamFrame.lift_frame | (intros; apply GlobalTheory.PeriodFamFrame.lift_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClassTrivialStabiliserAtTypePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_class_trivial_stabiliser_at_typePlace : ∀ (D : D7) (k : Fin 2) (s : SplitPlace D.host.E), s.w ∈ placesOver D.host.E (D.host.g k) → ∃ g : GAf D.host.E D.R.nV, ∀ γ ∈ GQ D.host.E D.R.nV, g⁻¹ * γ * g ∈ Umax D.host.E D.R.nV → NG.UniRT s D.R.r (s.loc _ (g⁻¹ * γ * g)) → γ = 1 := by
  first | exact @GlobalTheory.NeatUni.exists_trivial_stabiliser | exact GlobalTheory.NeatUni.exists_trivial_stabiliser | (intros; apply GlobalTheory.NeatUni.exists_trivial_stabiliser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexEmbeddingReadingFractionRingOverCoeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexEmbedding_readingFractionRing_over_coeffField : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  first | exact @GlobalTheory.ReadingEmb.exists_complex_emb | exact GlobalTheory.ReadingEmb.exists_complex_emb | (intros; apply GlobalTheory.ReadingEmb.exists_complex_emb <;> assumption)
end

