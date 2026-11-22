import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0538
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0645
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0461
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0427
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0477
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0381
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0702
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0096

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BkLawEntries
section
noncomputable section

namespace GlobalTheory.Fc.DivLinked

section Read

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Matrix Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

set_option maxHeartbeats 2000000 in

theorem divisionRows_pairing_vanishes_of_rational_pairing_law
    (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧
      GlobalTheory.Published.CuspRapidDecay) (x : TwIn ex) (hH : Holds x.R x.F) (hB : Rw.BkLaw D)
    (hV : CxData.BtVanish (fc := x.F.fc) (x.R.toCx3 x.F)) : GlobalTheory.Cp.DivRows3G (divisionPairOfAdelicFormsFaceColumnsData x) :=
  (GlobalTheory.Cp.divRows3G_iff _).2 ((rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ x).2.2.2
    ((GlobalTheory.T.divisionCompatible_at_readIdentifications hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.sEE Yd x.JM x.pins hH fun _ _ => x.div.grp).2
      x.mjH ex.idx (hB (GlobalTheory.T.divisionPairing_rational_on_rationalPoints' hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.pins hH)) hV))

end Read

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL}

theorem of_built {R : BdP Bundle} {Q : V4.Slot} {κ : Par}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c), BWit q b → R _ _ c b)
    {D : D7} {O : Obj D} {c : ℝ} {b : Bundle D O c} (hb : GlobalTheory.Fc.Built Q (IsLinked p) κ D O c b) : R D O c b := by
  refine GlobalTheory.Fc.Built.ind (R := R) (fun K β c b _ _ hl => ?_) hb
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => R s.1 s.2.1 c s.2.2) he
  exact cast this.symm (h K q c b' w)

theorem at_atAll {A R : BdP Bundle}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c), BWit q b → A _ _ c b → R _ _ c b)
    (hA : RL.At p fun S L => Row S L (AtAll A)) : RL.At p fun S L => Row S L (AtAll R) := by
  obtain ⟨S, hS, hA⟩ := hA
  refine ⟨S, hS, Row.imp hA fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact of_built (R := fun D O c b => A D O c b → R D O c b) h (t x hx i).1 (H Fm hc x hx i)

section Wit

variable (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
  GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
  {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : Bundle (q.w.D q.Z) q.O c}

include hC

theorem div_of_mi (w : BWit q b) (hB : R3.Rw.BkLaw (q.w.D q.Z))
    (hM : (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) : R1.P_hDivG _ _ c b := by
  have h : (fun r : RPk b.R b.S => (r.B.Q.Rl.toCx3 r.B.Q.F).MIstar2 (r.B.Q.F.eV (r.B.Q.Rl.toCx3 r.B.Q.F).zs) r.B.Q.sEE →
      GlobalTheory.Cp.DivRows3G r.P) (rpkX w.y.y) := fun hM =>
    divisionRows_pairing_vanishes_of_rational_pairing_law hC w.x w.y.intersectionNumber_baseChange hB
      (GlobalTheory.Div.pairing_definite_base_vanish_of_miStar2 _ _ _ _ _ w.x.A3 _ w.x.R w.x.F 1 w.y.intersectionNumber_baseChange.ok w.y.intersectionNumber_baseChange.sep w.x.pins.char
        w.y.intersectionNumber_baseChange.prim w.x.sEE hM)
  rw [← w.y.eq] at h
  exact h hM

end Wit

theorem at_hDivG_of_mi (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules) (h3 : GlobalTheory.Published.CasselmanWallach)
    (h4 : GlobalTheory.Published.HarishChandraFinite) (h5 : GlobalTheory.Published.CuspRapidDecay) (p : Prm hL)
    (hB : ∀ (K : Ctx) (q : WPt p.s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z))
    (hM : RL.At p fun Q L => Row Q L (AtAll fun _ _ _ (b : Bundle _ _ _) =>
      (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) : RL.At p R1.DivisorConditionAtBundlePoints :=
  at_atAll (R := R1.P_hDivG) (fun K q _ _ w h => div_of_mi ⟨h1, h2, h3, h4, h5⟩ w (hB K q) h) hM

theorem at_hDivG_main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ (K : Ctx) (q : WPt (prmR N S Γ).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z)) → RL.At (prmR N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : Bundle _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) → RL.At (prmR N S Γ) R1.DivisorConditionAtBundlePoints :=
  fun _ _ h3 h4 h5 h6 h7 _ _ _ _ hB hM => at_hDivG_of_mi h5 h6 h7 h3 h4 _ hB hM

end GlobalTheory.Fc.DivLinked

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntriesCombinedReal
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.JoinLinked

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem move {D : D7} {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F0 = F0')
    (Φ : ∀ F : (∀ u, Formalism.L2.Forms.Forms0 D u), ∀ P : GlobalTheory.Mem.SRe.SPack D F, GlobalTheory.Mem.SRe.SRest P → Formalism.L2.Theta.GA D (D.sp.Y 0) → ℝ → Prop)
    {P' : GlobalTheory.Mem.SRe.SPack D F0'} {S' : GlobalTheory.Mem.SRe.SRest P'} {t t' : Formalism.L2.Theta.GA D (D.sp.Y 0)} {c c' : ℝ}
    {P : GlobalTheory.Mem.SRe.SPack D F0} {S : GlobalTheory.Mem.SRe.SRest P} (hP : HEq P P') (hS : HEq S S') (ht : HEq t t') (hc : c = c')
    (h : Φ F0' P' S' t' c') : Φ F0 P S t c := by
  subst hF
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq ht
  subst hc
  exact h

theorem schurAll (hH : GlobalTheory.Published.HarishChandraFinite) (hC : GlobalTheory.Published.CuspRapidDecay) (D : D7) :
    Formalism.IndefR.Links.SchurAll D :=
  fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2

section IndefiniteRowSideFullHecke

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation
  Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

theorem join_linked_realization (hR : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (S0 : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (P : SPack D fun u => (Rc.T.cols.forms u).to0)
    (S : SRest P) (hS0 : S0 = S.toSTiesR Rc) (y : RealIn x Rc S0) (c : ℝ) (hPins : RealPins (realTOf y)) (hH : Holds x.R x.F)
    (hSee : SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS)
    (hEv : EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G
      (iotaX P.X P.inst).toMulEquiv y.tS c)
    (hRow : RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j) :
    Nonempty (Formalism.L2.SG.JoinSI.JoinSI Rc S0 (realTOf y)) := by
  subst hS0
  have hRR := (GlobalTheory.Mem.R3.rowLat_ties hR _ _ _ _ _ x.A3 _ x.R x.F x.cG _ x.Y x.Z x.pins hH).1
  exact (GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice D L hT Gi Gl K Yd cX ex x Rc P S y c 1 (schurAll hR.2.2.2.1 hR.2.2.2.2 D) hPins hH hH.ok hH.sep hRR
    (rowConditions_at_companion_from_readings D L hT Gi Gl K Yd cX ex x).2.1 hSee hEv hRow).1

end IndefiniteRowSideFullHecke

section Wit

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation
  Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.SRe

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL}

set_option maxHeartbeats 2000000 in

theorem selJ_of_wit (hR : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : Bundle (q.w.D q.Z) q.O c} (w : BWit q b) (t : b.Comparison₂) : R1.P_selJ _ _ c b := by
  show Nonempty (Formalism.L2.SG.JoinSI.JoinSI (R := b.R) (S := b.S) (Q := b.B.Q))
  have hPins : RealPins (R3.realTOf w.y.y) := by
    have h : (fun r : RPk b.R b.S => RealPins r.B.Q) (rpkB b) := t.pins
    rw [w.y.eq] at h
    exact h
  obtain ⟨sP, sS, hP, hS, hSeq⟩ := w.s
  have hx : w.a.x = w.x := eq_of_heq w.ax
  have hM := GlobalTheory.Mem.R3.StageMove.spectralStage_point_rowPlacement_transfer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w.a _ q.sat
  rw [hx] at hM
  have hF : (fun u => (b.R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 := by
    rw [w.recPin.s.cols]
  have hN := move hF (fun _ P S t c => SeeAt w.x.R.toRealDat w.x.F.lv2 P.X P.inst t ∧
      EvalTieT (MP w.x.R.toRealDat) w.x.R.toRealDat.ν0 w.x.R.toRealDat.fd0 (EP w.x.R.toRealDat w.x.F.lv2) P.X P.G
        (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ w.x.R.toRealDat w.x.Y.eE P.X P.inst P.G t S.j)
    (P := sP) (S := sS) (t := w.y.y.tS) (c := w.y.y.cS) hP hS w.pt.1 w.pt.2 hM
  have hJ := join_linked_realization hR w.x b.R b.S sP sS hSeq w.y.y w.y.y.cS hPins w.y.intersectionNumber_baseChange hN.1 hN.2.1 hN.2.2
  have h : (fun r : RPk b.R b.S => Nonempty (Formalism.L2.SG.JoinSI.JoinSI (R := b.R) (S := b.S) (Q := r.B.Q))) (rpkX w.y.y) := hJ
  rw [← w.y.eq] at h
  exact h

end Wit

section Constructions₂

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL}

theorem of_built {R : BdP Bundle} {Q : V4.Slot} {κ : Par}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c), BWit q b → R _ _ c b)
    {D : D7} {O : Obj D} {c : ℝ} {b : Bundle D O c} (hb : GlobalTheory.Fc.Built Q (IsLinked p) κ D O c b) : R D O c b := by
  refine GlobalTheory.Fc.Built.ind (R := R) (fun K β c b _ _ hl => ?_) hb
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => R s.1 s.2.1 c s.2.2) he
  exact cast this.symm (h K q c b' w)

theorem at_atAll {A R : BdP Bundle}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c), BWit q b → A _ _ c b → R _ _ c b)
    (hA : RL.At p fun S L => Row S L (AtAll A)) : RL.At p fun S L => Row S L (AtAll R) := by
  obtain ⟨S, hS, hA⟩ := hA
  refine ⟨S, hS, Row.imp hA fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact of_built (R := fun D O c b => A D O c b → R D O c b) h (t x hx i).1 (H Fm hc x hx i)

end Constructions₂

theorem at_selJ : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.DiscreteSeriesCover →
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) R1.PeriodAdmissibilityAtBundlePoints →
    RL.At (prmR N S Γ) R1.DecompositionConditionAtBundlePoints → RL.At (prmR N S Γ) RL.Row_tie → RL.At (prmR N S Γ) R1.JSelectionAtBundlePoints :=
  fun _ _ h1 h2 h3 h4 h5 _ _ _ _ _ _ hT =>
    at_atAll (A := HasTie) (R := R1.P_selJ) (fun _ _ _ _ w ht => selJ_of_wit ⟨h1, h2, h3, h4, h5⟩ w (Classical.choice ht)) hT

end GlobalTheory.Fc.JoinLinked

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntryHPAAtParameters
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.RL.PrimAt

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL}

theorem of_wit {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : Bundle (q.w.D q.Z) q.O c} (w : BWit q b) : R1.P_hPA _ _ c b := by
  have h : (fun r : RPk b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (rpkX w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h

theorem row (p : Prm hL) (Q : V4.Slot) : R1.PeriodAdmissibilityAtBundlePoints Q (IsLinked p) := by
  refine RowE.row (R := R1.P_hPA) (RowE.of_all fun κ K β c b _ _ hl => ?_)
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => R1.P_hPA s.1 s.2.1 c s.2.2) he
  exact cast this.symm (of_wit w)

theorem at_linked : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP),
    RL.At (prmR N S Γ) R1.PeriodAdmissibilityAtBundlePoints :=
  fun _ N S Γ => At.of_row (row (prmR N S Γ) _)

end GlobalTheory.Fc.RL.PrimAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntryPointGAtParameters
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.RL

theorem rowE_dcPt_linked {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (Q : V4.Slot) :
    RowE Q (IsLinked p) (fun _ => R1.P_hDcPtG) := by
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => R1.P_hDcPtG s.1 s.2.1 c s.2.2) he
  refine cast h1.symm ?_
  show GlobalTheory.Cp.DcPtG _
  have hP : b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg RPk.P w.y.eq
  rw [hP]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).2.2.1

theorem at_hDcPtG : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP),
    RL.At (prmR N S Γ) R1.DecompositionConditionAtBundlePoints := by
  intro hL N S Γ
  exact At.of_row (RowE.row (rowE_dcPt_linked _ _))

end GlobalTheory.Fc.RL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodFtEntries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.Fc.LabLinked

def Ties (D : D7) : Prop :=
  ∃ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X),
    Formalism.MainNotions.S.AutTie D X.B X.pl ∧ Formalism.L2.SG.RowDict.RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι

def GenPin {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) : Prop :=
  ∀ k, a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
    (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)

set_option maxHeartbeats 2000000 in

theorem typeLab_of_gen (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : GenPin a)
    (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (hrep : HEq a.nt.rep rep) : GlobalTheory.LabPin.TypeLab D rep := by
  have e : ∀ (D' : D7), D' = withLoc a.nt.L →
      (GlobalTheory.SerSys.LabTie D' fun k => @GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩) →
      ∀ rep' : D'.what₂.FT → Formalism.L2.NG.FinTyp D'.host.E D'.R.r, HEq a.nt.rep rep' → GlobalTheory.LabPin.TypeLab D' rep' := by
    rintro _ rfl hl' rep' hr
    obtain rfl := eq_of_heq hr
    refine GlobalTheory.T.rowTruth_of_labelTie hG hZ hDZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.A.lab a.nt.row a.depth hl' ?_
    intro k v
    refine ⟨a.nt.A.grp.kv k v, ?_⟩
    rw [← hp k]
    exact a.nt.A.grp.tg_tame k v
  exact e D a.nt.eq hl rep hrep

section Rows

open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX

set_option maxHeartbeats 1000000 in

theorem ties_at_rows (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {hL : GlobalTheory.Published.LocalLanglandsGL} {cf : CharFrame D} {nch : NChoice D}
    {tp : TupTied D cf nch} {a : NAt hL D cf nch tp} {R : RealDat3 D A3 Ks} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} (r : NRow a R F cG Y) {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u}
    (s : SAt R.toRealDat F.lv2 Y.eE F0)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : GenPin a)
    (hg : GoodFTAll D) : Ties D := by
  have hR := GlobalTheory.Mem.R3.RowFrameParts.main D G Pl0 I0 T A3 Ks R.toRealDat F.lv2 X0 Y
  have hT := typeLab_of_gen hG hZ hDZ a hl hp _ r.rep_eq
  exact ⟨s.P.X, s.P.G, s.S.hI.eHH,
    GlobalTheory.T.constructedSpectralObjects_irreducibilityConditions D G Pl0 T A3.A Ks R.toRealDat F.lv2 Y.eE F0 s Y.PY Y.hF
      (fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) hR.1 hR.2 hT hg⟩

end Rows

theorem lab_of_rows {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
  fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩

set_option maxHeartbeats 1000000 in

theorem ties_at_wit (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) (hp : GenPin q.core.a)
    (hg : GoodFTAll (q.w.D q.Z)) : Ties (q.w.D q.Z) :=
  ties_at_rows hG hZ hDZ (D := (q.w.st q.Z).toD7) q.core.row q.sat (lab_of_rows q.x.what₂) hp hg

theorem ties_of_built (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} (hp : ∀ (K : Ctx) (q : WPt p.s K), GenPin q.core.a) {Q : V4.Slot} {κ : Par}
    {D : D7} {O : Obj D} {c : ℝ} {b : Bundle D O c} (hb : Built Q (IsLinked p) κ D O c b) : GoodFTAll D → Ties D := by
  refine Built.ind (R := fun D _ _ _ => GoodFTAll D → Ties D) ?_ hb
  rintro K β c b - - ⟨q, b', -, e⟩
  have e1 : β.D = q.w.D q.Z := congrArg Sigma.fst e
  show GoodFTAll β.D → Ties β.D
  rw [e1]
  exact ties_at_wit hG hZ hDZ q (hp K q)

theorem row_lab_of_good : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → ∀ k, c.a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨c.a.nt.D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (c.a.nt.D.host.g k) ⟨c.a.nt.D.host.g_prime k⟩)) → RL.At (prmR N S Γ) (fun Q Lk => Row Q Lk (AtAll fun D _ _ _ => GoodFTAll D)) → RL.At (prmR N S Γ) RL.LabelCondition := by
  intro hG hZ hDZ hL N S Γ hN ⟨R, hR, hrow⟩
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s hA eps Fm hc x hx i => ?_⟩
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact ties_of_built hG hZ hDZ (p := prmR N S Γ) (fun K q => hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2) (t x hx i).1 (hA Fm hc x hx i)

theorem row_lab_ev_of_good (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} (hp : ∀ (K : Ctx) (q : WPt p.s K), GenPin q.core.a) :
    RL.At p RL.GoodReductionCondition → RL.At p fun Q Lk => Row Q Lk (Ind.EvW (Bd := Bundle) fun D _ _ _ => Ties D) := by
  intro ⟨R, hR, hrow⟩
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s hA => Closed.imp hA fun Fm _ _ h hc => ?_⟩
  obtain ⟨x0, h⟩ := h hc
  obtain ⟨κ, -, -, t⟩ := s Fm (w3_a hc)
  exact ⟨x0, fun x hx h0 i => ties_of_built hG hZ hDZ hp (t x hx i).1 (h x hx h0 i)⟩

theorem row_lab_labelCondition_of_localLanglands (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (S : SExt) (Γ : GeoP) :
    RL.At (prmR (NE hL) S Γ) (fun Q Lk => Row Q Lk (AtAll fun D _ _ _ => GoodFTAll D)) → RL.At (prmR (NE hL) S Γ) RL.LabelCondition :=
  row_lab_of_good hG hZ hDZ hL (NE hL) S Γ fun _ _ _ _ _ _ _ _ _ _ _ _ _ m => m.zeta

theorem row_lab_of_layer : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → RL.At (prmR N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : Bundle _ _ _) => Formalism.BasicNotions.GoodFTAll D)) → RL.At (prmR N S Γ) RL.LabelCondition :=
  fun hG hZ hDZ hL N S Γ hN =>
    row_lab_of_good hG hZ hDZ hL N S Γ fun K B f T w Z Wt p0 t nch n xd c m =>
      (hN K B f T w Z Wt p0 t nch n xd c m).elim fun e => e.1.zeta

end GlobalTheory.Fc.LabLinked
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealGroupInputsCombined
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.RL.LamLinked

theorem evP_params : EvP fun _ K => ∀ β : BPt K, Nonempty (ParameterChoice' β.D β.O.L) := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨x0, fun K h1 h2 h3 h4 hx β => ?_⟩
  have hsc : β.O.L.sc = K.s := β.sc
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ (by rw [hsc, h4]) (by rw [hsc]; exact hx) hv (GlobalTheory.Plug.hostArith_bpt β)
  exact ⟨N.params⟩

set_option maxHeartbeats 2000000 in

theorem isotRank_of_wit (h1 : GlobalTheory.Published.WeilRepresentationUnitaryPair) (h2 : GlobalTheory.Published.DiscreteSeriesExists)
    (h3 : GlobalTheory.Published.HarishChandraFinite) (h4 : GlobalTheory.Published.CuspRapidDecay)
    (a1 : GlobalTheory.Published.HarishChandraAnalyticity) (a2 : GlobalTheory.Published.DiscreteSeriesClassification) (a5 : GlobalTheory.Published.CuspTraceClass)
    (a6 : GlobalTheory.Published.DixmierMalliavinFactorisation) (a7 : GlobalTheory.Published.FlathFactorisation) (a8 : GlobalTheory.Published.PseudoCoefficientUpq)
    (a9 : GlobalTheory.Published.HarishChandraCharacters) (a10 : GlobalTheory.Published.LanglandsClassification) (a11 : GlobalTheory.Published.LabesseWaldspurger)
    (a12 : GlobalTheory.Published.ZelevinskyPolynomialRing) (a13 : GlobalTheory.Published.GeometricLemma) (hG : GlobalTheory.Published.GreenCuspidal)
    {𝒮 : Slots} {K : Ctx} (q : WPt 𝒮 K) (hH : Formalism.IndefR.Links.HostHyp (q.w.st q.Z).toD7)
    (hp : ∃ L : SizeData₂ (q.w.st q.Z).toD7, Nonempty (ParameterChoice' (q.w.st q.Z).toD7 L)) :
    Formalism.BasicNotions.Rows.IsotRank (q.w.st q.Z).toD7.what₂ := by
  have hGS : Formalism.L2.DIV.GoodStable q.x.what₂.r.z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (q.w.st q.Z).toD7) q.x.what₂.grp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (q.w.st q.Z).B.embLL q.x.what₂.r.z.Xg q.x.what₂.r.z.good.irr fun g => ?_
    apply (q.w.st q.Z).B.embLL.injective
    rw [q.x.what₂.r.z.good.2, q.x.what₂.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hT : TypesTrue (q.w.st q.Z).toD7.ntypes q.x.what₂.r.z.R.C.P q.x.what₂.r.z.R.C.W := by
    rw [q.x.what₂.r.z.lev.C, q.w.C_eq]
    exact q.x.what₂.grp
  have hME := GlobalTheory.T.multiplicity_equality_statement a1 a2 h4 h3 a5 a6 a7 a8 a9 a10 a11 a12 a13 hG q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.intersectionNumber_baseChange.ok
    q.x.what₂.r.z.pins.char q.x.what₂.exAt hH hp q.B.ccK_top q.x.what₂.r.z.pins.keep.guard
    (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue q.x.what₂.r.z.pins.char.base.lev hT)
  exact GlobalTheory.Mem.R3.isotRank_of_multEq h1 h2 h3 h4 _ _ _ _ _ _ _ q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG _ q.x.what₂.r.Y q.x.what₂.r.z.pins
    q.x.what₂.r.intersectionNumber_baseChange hH hGS (GlobalTheory.CuspDec.cuspDecomp h3 h4 _) hME

end GlobalTheory.Fc.RL.LamLinked

namespace GlobalTheory.Fc.RL

set_option maxHeartbeats 2000000 in

theorem at_row_hLamP : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) R1.LambdaPositivityAtBundlePoints := by
  intro h1 h2 h3 h4 a1 a2 a5 a6 a7 a8 a9 a10 a11 a12 a13 hG hL N S Γ
  refine At.of_row (RowE.row (EvP.mono (fun κ K _ H β _ c b hl => ?_) LamLinked.evP_params))
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have e1 := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => Nonempty (ParameterChoice' s.1 s.2.1.L)) he
  have e2 := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => R1.P_hLamP s.1 s.2.1 c s.2.2) he
  refine cast e2.symm ?_
  have hIR := LamLinked.isotRank_of_wit h1 h2 h3 h4 a1 a2 a5 a6 a7 a8 a9 a10 a11 a12 a13 hG q w.y.y.host ⟨_, cast e1 (H β)⟩
  show Formalism.L2.Rows.RowsHoldLam3 b'.P
  rw [show b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x from congrArg RPk.P w.y.eq]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).1
    (GlobalTheory.T.finiteTypes_via_full_heckeAlgebra_eigensystems h1 h2 h3 h4 _ _ _ _ _ w.x.A3 _ w.x.R w.x.F w.x.cG q.O.ex.p0 w.x.Y w.x.Z w.x.pins w.y.intersectionNumber_baseChange w.y.y.host hIR)

end GlobalTheory.Fc.RL
end

