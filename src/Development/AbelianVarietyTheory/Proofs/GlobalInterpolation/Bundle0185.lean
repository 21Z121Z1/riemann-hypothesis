import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0702
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0176
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.HeckeRamifiedZeroAll
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HarishChandraInputsCombined
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.KapLinked

section Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}

set_option maxHeartbeats 2000000 in

theorem isot_ne_bot_of_rows (hF : GlobalTheory.Published.HarishChandraFinite) (hG : GlobalTheory.Published.GreenCuspidal) (t : RowsT K w Z Wt p0)
    (hM : GlobalTheory.CuspMult.MultEq t.r.z.R.toRealDat) (σ : Fin (w.D Z).what₂.Drows) (i : Fin (w.D Z).R.m) :
    (w.D Z).what₂.isot ((i : ℕ) + 1) ((w.D Z).what₂.ft σ) ≠ ⊥ := by
  have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
    (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) t.grp).2.1
  have hGS : Formalism.L2.DIV.GoodStable t.r.z.Xg := by
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL t.r.z.Xg t.r.z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [t.r.z.good.2, t.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1
  exact GlobalTheory.KapIsotRead.isot_ne_bot_read hF (w.st Z).toD7 _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.z.pins t.r.intersectionNumber_baseChange hM hGS
    (GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_base_ne_zero t.r.z.R.toRealDat t.r.z.F.lv2 t.r.intersectionNumber_baseChange.ok.ok2 hC.lev hC.grp _ hI) σ i

set_option maxHeartbeats 2000000 in

theorem goodTypes_of_rows (t : RowsT K w Z Wt p0) : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes t.r.z.R.toRealDat := by
  have hT : TypesTrue (w.st Z).toD7.ntypes t.r.z.R.C.P t.r.z.R.C.W := by
    rw [t.r.z.lev.C, w.C_eq]
    exact t.grp
  exact GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue t.r.z.pins.char.base.lev hT

end Rows

set_option maxHeartbeats 2000000 in

theorem row_kap_of_row_lam : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) R1.LambdaPositivityAtBundlePoints → RL.At (prmR N S Γ) RL.KappaCondition := by
  intro a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 hL N S Γ h
  obtain ⟨R, hR, h⟩ := h
  refine ⟨R, hR, Row.imp h fun 𝒜 σ s hl => ?_⟩
  have key : AtAll (Bd := Bundle) (fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P) 𝒜 σ := by
    intro eps Fm hc x hx i
    obtain ⟨κ, -, -, hb⟩ := s Fm hc
    refine Built.ind (Bd := Bundle) (R := fun D _ _ b => (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → Formalism.L2.Rows.RowsHoldLam3 b.P →
      Formalism.L2.Rows.RowsHoldKap3 b.P) ?_ (hb x hx i).1 ⟨_, ⟨Fm.params x hx i⟩⟩ (hl Fm hc x hx i)
    intro K β c b _ _ hk
    obtain ⟨q, b', ⟨w⟩, he⟩ := hk
    have e := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => (∃ L : SizeData₂ s.1, Nonempty (ParameterChoice' s.1 L)) →
      Formalism.L2.Rows.RowsHoldLam3 s.2.2.P → Formalism.L2.Rows.RowsHoldKap3 s.2.2.P) he
    refine cast e.symm fun hP hLam => ?_
    have hb' : b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg RPk.P w.y.eq
    change Formalism.L2.Rows.RowsHoldLam3 b'.P at hLam
    change Formalism.L2.Rows.RowsHoldKap3 b'.P
    rw [hb'] at hLam ⊢
    have hM : GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat :=
      GlobalTheory.T.multiplicity_equality_statement a6 a7 a2 a1 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.intersectionNumber_baseChange.ok
        q.x.what₂.r.z.pins.char q.x.what₂.exAt w.y.y.host hP q.B.ccK_top q.x.what₂.r.z.pins.keep.guard (goodTypes_of_rows q.x.what₂)
    exact GlobalTheory.T.divisorEmbedding_kappa_eq_rowsKappa_at_infinitePlace ⟨a3, a4, a5, a1, a2⟩ _ _ _ _ _ w.x.A3 _ w.x.R w.x.F w.x.cG _ w.x.Y w.x.Z _ w.x.pins w.y.intersectionNumber_baseChange hLam
      (isot_ne_bot_of_rows a1 a17 q.x.what₂ hM) q.x.obj.kapR
  exact ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => Ind.ev_of_atAll key Fm (w3_a hc)⟩⟩

end GlobalTheory.Fc.KapLinked

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilUnitaryEntries
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.RL.DefSide

open Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory in

theorem full_rank {eps : ℝ} (Fm : FamP eps) (CH : ℝ) (tie : RealPlaceSecondLayerConditions Fm) (hTu : TuSize Fm) (hCh : ChosenE Fm 3 CH) :
    NuFullF Fm ∧ J.MuRank Fm := by
  have tT := (family_conditions_of_layer_two Fm tie).2.2
  have h := slope_free_branch_family Fm tT freeTT_holds slopeLineT_holds Formalism.L2.GlobalTheoryTheory.LemB.second_branch_all_members
  obtain ⟨hT2, hT5⟩ := Formalism.MainNotions.Wire.family_theorems_two_and_five Fm h.1 h.2.1 (hI_tied Fm tT PI.IntegralAtBasePointLattice.integral_at_t0_lattice)
    (tT.mono fun D u hS ht => Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.hecke_ramified_zero_all D u hS ht) h.2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, cPr, _⟩ := hCh
  exact muRank_items Fm 3 (by norm_num) hT2 hT5 hTu cPr

theorem wts_eq {X X' : Formalism.L2.Col.Fields} (h : X = X') {P : Formalism.L2.Col.Primes X} {P' : Formalism.L2.Col.Primes X'} (hP : HEq P P')
    {R R' : Ranks} (hR : R = R') : Formalism.L2.Col.Wts X P.Word R = Formalism.L2.Col.Wts X' P'.Word R' := by
  subst h; cases hP; subst hR; rfl

def PtE : BdP Bundle := fun D O _ b =>
  (Formalism.L2.Theta.RealTied D ∧ ∃ C : Formalism.L2.Forms.ColsTiedSym D, ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u)) ∧
  Formalism.L2.DIV.ColPins b.C.toS ∧ ∃ W : Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word D.R, HEq b.C.toS.c.W W ∧
    GlobalTheory.ColRows.KerTies b.R.T.ker W b.DH.1.1 b.DH.1.2 ∧
    ∀ CY CT : ℝ, GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) →
      GlobalTheory.ColRows.KerSizes b.R.T.ker W b.DH.1.1 b.DH.1.2 CY CT

theorem ptE_of_wit {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c) (w : BWit q b) : PtE _ _ c b := by
  have hk := b.C.kerTie
  have e : Formalism.L2.Col.Wts _ b.C.c.Pr.Word b.C.c.Rk = Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word (q.w.D q.Z).R :=
    wts_eq hk.1.symm hk.2.2.1 hk.2.1
  have hW : HEq (cast e b.C.c.W) q.B.wts := (cast_heq e _).trans w.cW.1
  refine ⟨⟨q.x.real, GlobalTheory.T.exists_symmetricColumnForms_stepZeroFiniteCharacter q.w.I q.w.ok q.w.pins q.w.l q.Z⟩, w.colPins, cast e b.C.c.W, (cast_heq e _).symm, ?_, ?_⟩
  · exact GlobalTheory.T.kernelCompatibilities_standardKernelData_trueColumns q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ q.x.pin.jets w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2 (b.R.T.ker_sharp _)
  · exact GlobalTheory.ColRows.kerSizes_of_stdKer q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2

theorem ptE_of_linked {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (β : BPt K) (c : ℝ) (b : Bundle β.D β.O c)
    (h : IsLinked p K β c b) : PtE _ _ c b := by
  obtain ⟨q, b', ⟨w⟩, e⟩ := h
  exact Eq.mpr (congrArg (fun y : Σ (D : D7) (O : Obj D), Bundle D O c => PtE y.1 y.2.1 c y.2.2) e) (ptE_of_wit q b' w)

theorem drs_pt (CY CT : ℝ) (hCT : 0 ≤ CT) : ∃ C0 : ℝ, ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Bundle D O c) (C CH : ℝ),
    PtE D O c b → GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) → DV.NprimeDef D O.L → D.NuFull →
      (∀ u, 0 < (D.div.Nu u).rank) → C0 ≤ c → DRS D O c b C CH := by
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.kernel_columns_from_ties CY CT hCT
  refine ⟨C0, fun D O c b C CH hE h1 h2 h3 h4 h5 hN hF hR hc => ?_⟩
  obtain ⟨-, hpin, W, hW, hT, hS⟩ := hE
  intro hok1 hsep hP hI lam0 c0 ce Sw C1 H NuC I _ hII u
  have hZs : (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI).Zs = b.P.Zs := (qS b).zs
  have hS0 : HEq (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI).core.base.toIndefData b.P.S0 := (qS b).s0
  have hS1 : HEq (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI).core.cols.toIndefData b.P.S1 := (qS b).s1
  have hDc : HEq (b.C.toS.c.face (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI).Zs) b.P.Dc :=
    (congr_arg_heq b.C.toS.c.face hZs).trans (heq_of_eq b.C.toS.colTie.1)
  have hw : HEq (I.wU u) u := ((Formalism.L2.DIV.divTieDat3_heq hZs hS0 hS1 hDc hII).2.2 u).trans (b.C.wTie u)
  exact hC0 D O.L _ _ _ _ _ _ O.ex b.R.T b.P b.C.toS W _ _ hpin hW hT (hS CY CT h1 h2 h3 h4 h5) hN hF hR _ _ C CH
    (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI) hZs u lam0 c0 ce c Sw C1 (H u) (I.wU u) (I.eNu u) hw hc

theorem row_df {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) : RL.At p RL.DifferentialCondition := by
  refine RL.At.of_row (p := p) (H := Ind.EvWC (Bd := Bundle) (fun _ => True) fun C CH D O c b => DRS D O c b C CH)
    ⟨fun _ => PtE, RowE.of_all fun _ _ β c b _ _ h => ptE_of_linked β c b h, fun 𝒜 σ s => ?_⟩
  choose c0 hc0 using fun (CY CT : ℝ) => drs_pt CY (max CT 0) (le_max_right _ _)
  refine (Formalism.MainNotions.DIV.closed_Csz_ge_fn (W3 𝒜) fun l => c0 (l.getD 6 0) (l.getD 13 0)).imp ?_
  intro eps Fm CH _ hC hc _
  have hC' : c0 Fm.CYL Fm.CTu ≤ Fm.Csz := hC
  obtain ⟨κ, -, -, hs⟩ := s Fm (w3_a hc)
  have tie : RealPlaceSecondLayerConditions Fm := ⟨Fm.x1 + 1, fun x hx i => (hs x (by linarith) i).2.1⟩
  obtain ⟨CH', hCh⟩ := hc.2.1
  obtain ⟨⟨a1, hF⟩, ⟨a2, hR⟩⟩ := full_rank Fm CH' tie hc.2.2.1 hCh
  obtain ⟨a3, hz⟩ := GlobalTheory.CoreHt.famRowsSizes Fm hc.2.2.1
  refine ⟨0, le_rfl, fun C _ => ⟨max a1 (max a2 a3), fun x hx h0 i => ?_⟩⟩
  have e1 : a1 ≤ x := le_trans (le_max_left _ _) h0
  have e2 : a2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have e3 : a3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨z1, z2, z3, z4, z5⟩ := hz x e3 i ⟨_, (σ Fm (w3_a hc) x hx i).DH.2.1⟩
  exact hc0 Fm.CYL Fm.CTu _ _ _ (σ Fm (w3_a hc) x hx i) C CH (hs x hx i).2 z1 z2 z3 z4 z5 (Fm.nprimeDef x hx i)
    (hF x e1 i) (hR x e2 i) hC'

end GlobalTheory.Fc.RL.DefSide

theorem GlobalTheory.Fc.RL.at_row_df : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) RL.DifferentialCondition :=
  fun _ _ _ _ _ N S Γ => GlobalTheory.Fc.RL.DefSide.row_df (prmR N S Γ)

end
end

