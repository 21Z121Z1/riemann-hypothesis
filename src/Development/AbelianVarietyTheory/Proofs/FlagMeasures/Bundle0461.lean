import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeSizeZ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivIntegral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntClLeEncardMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeProdReal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0455
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0458
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0456
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0457
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowCountsUniformConstantsFamilies
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.RowCounts

theorem uniform_counts : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ c3 cH cS c4 thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
    (∀ C ≥ c3, (OwnEv Fm fun C' Cl x i => ∀ u u',
      VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C)) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cH) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cS) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A c4) := by
  intro hM Cg cb Cu cT CT C0 A
  obtain ⟨C1a, hC1⟩ := GlobalTheory.T.mean_count_primitive_sublattices_over_genus 1 one_pos
  obtain ⟨c3, hC3⟩ := GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT C0 A 3 (max C1a 0) (le_max_right _ _)
  obtain ⟨cH, -, hHH⟩ := GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT C0 A
  obtain ⟨cS, hSW⟩ := GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT C0 A
  obtain ⟨c4, hC4⟩ := GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT C0 A
  refine ⟨c3, cH, cS, c4, 1, fun eps Fm _ hl => ⟨fun C hC => ⟨0, fun x _ i u u' => ?_⟩,
    ⟨0, fun x _ i u u' => ?_⟩, ⟨0, fun x _ i u u' => ?_⟩, ⟨0, fun x _ i u u' => ?_⟩⟩⟩
  · exact hC3 C hC _ _ u u' _ _ hl (GlobalTheory.T.rows_raw_mass_and_genus_mass _ u)
      (hC1 _ (le_max_left _ _) _ _ u u' _ _ Cg cb Cu cT CT C0 A hl)
  · exact hHH _ _ u u' _ _ hl
  · exact hSW _ _ u u' _ _ hl
      (GlobalTheory.T.mean_primitive_corank_one_sublattices_bound _ _ u u' _ _ Cg cb Cu cT CT C0 A (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))
  · exact hC4 _ _ u u' _ _ hl

end GlobalTheory.RowCounts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SeeExJoinPin
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.JPin

set_option maxHeartbeats 4000000 in

theorem seeEx_joinPin : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : RealIn x Rc (S.toSTiesR Rc)) (c : ℝ), Holds x.R x.F → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → SeeEx (realTOf y) ∧ GlobalTheory.Mem.JTop.JoinPin (realTOf y) := by
  intro D L hT Gi Gl K Yd cX ex x Rc P S y c _ hS hE hR
  have hι : y.ιS = (iotaX P.X P.inst).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D P.X P.inst y.ιS).1 y.ιS_eq
  have hinj : Function.Injective x.R.HE.e := x.pins.char.base.models.HE.1
  have hread : ∀ y1, x.Y.eE (D.jEE (x.Z.eRR y1)) = Tw.out (s := twAt D.what₂.embLL x.A3.A.v0) (E := x.R.HE.H)
      ((x.R.toCx3 x.F).iC x.F.cr true x.A3.A.μ0 (cpt x.A3.A.v0.embedding y1)) := by
    intro y1
    have h1 := x.Y.eE_read (D.jEE (x.Z.eRR y1))
    rw [x.Z.jEE y1] at h1
    exact hinj ((PiTensorProduct.lift : Mult.MMap (x.R.MY 0) ≃ₗ[ℂ] _).injective h1).symm
  refine ⟨⟨⟨y.tS, hS.fin, ?_, ?_⟩, c, ?_⟩, x.Y.eE, ?_, ?_⟩
  · show ConjLevel y.tS⁻¹ (JR x.R.toRealDat x.F.lv2) (chiR x.R.toRealDat x.F.lv2) (y.ιS ⁻¹' concreteLevelAdelicSubset P.X)
      (fun k => adelicCharacterOfHidaSetting P.X (y.ιS k))
    rw [hι]
    exact hS.conj
  · exact hS.mat
  · show EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G y.ιS y.tS c
    rw [hι]
    exact hE
  · intro y1 y' h
    obtain rfl := eq_of_heq h
    exact hread y1
  · intro hF
    have hj : Formalism.L2.SG.JoinSI.jOf (S.toSTiesR Rc) hF = S.j :=
      Formalism.L2.SG.JoinSI.jOf_eq (S.toSTiesR Rc) hF S.j fun F => S.rowPin F
    rw [hj]
    exact hR

end GlobalTheory.Mem.JPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpectralStagePointRowPlacementTransfer
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.StageMove

def StageAt {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ) : Prop :=
  SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧
    RowJ R eE P.X P.inst P.G t S.j

set_option maxHeartbeats 1000000 in

theorem stageAt_upd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (k : ℝ) (lam : type_of% R.lam3) (e : type_of% (R.updS k lam).err0) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (h : StageAt R.toRealDat F.lv2 eE P S t c) :
    StageAt ((R.updS k lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 eE P S t c :=
  ⟨⟨h.1.fin, h.1.conj, h.1.mat⟩, h.2.1, h.2.2⟩

set_option maxHeartbeats 1000000 in

theorem spectralStage_point_rowPlacement_transfer : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) (F0 : ∀ u, Formalism.L2.Forms.Forms0 (w.st Z).toD7 u) (s : SAt (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y.eE F0), SeeAt a.x.R.toRealDat a.x.F.lv2 s.P.X s.P.inst s.t ∧ EvalTieT (MP a.x.R.toRealDat) a.x.R.toRealDat.ν0 a.x.R.toRealDat.fd0 (EP a.x.R.toRealDat a.x.F.lv2) s.P.X s.P.G (iotaX s.P.X s.P.inst).toMulEquiv s.t s.c ∧ RowJ a.x.R.toRealDat a.x.Y.eE s.P.X s.P.inst s.P.G s.t s.S.j := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a F0 s
  have h : StageAt (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y.eE s.P s.S s.t s.c := ⟨s.see, s.ev, s.rowJ⟩
  have e := congrArg (fun p => match p with
    | ⟨_, _, _, _, _, _, _, _, _, R, F, _⟩ => ∀ eE : (w.st Z).toD7.what₂.EE →ₗ[ℂ] R.HE.H, HEq eE t.r.Y.eE →
        StageAt R.toRealDat F.lv2 eE s.P s.S s.t s.c) a.pack
  have key : StageAt a.x.R.toRealDat a.x.F.lv2 a.x.Y.eE s.P s.S s.t s.c := by
    refine e.mpr (fun eE he => ?_) _ a.eE
    obtain rfl : eE = t.r.Y.eE := eq_of_heq he
    exact stageAt_upd _ _ _ _ _ _ _ _ _ _ _ _ _ h
  exact key

end GlobalTheory.Mem.R3.StageMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFrames
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.BasePt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) :
    frame F i.castSucc = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem tri_of_adapt {T : D.host.E} (g : GV D) (F G : LFlag (VS D) D.R.rS T) (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h : ∀ a : Fin (D.R.rS + 1), g (frame F a) - frame G a ∈ Xflag G a.val) :
    GlobalTheory.LocOver.Tri D.host.E (frame G) (frame (Formalism.L2.SG.Saturated.mapL g hg F)) := by
  have ex : ∀ b : Fin (D.R.rS + 1), ∃ l : Fin D.R.rS →₀ D.host.E,
      l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.val < b.val} ∧
        Finsupp.linearCombination D.host.E G.fl.e l = g (frame F b) - frame G b := fun b =>
    (Finsupp.mem_span_image_iff_linearCombination D.host.E).1 (h b)
  choose l hl hx using ex
  have hz : ∀ b (i : Fin D.R.rS), ¬ i.val < b.val → l b i = 0 := fun b i hi =>
    (Finsupp.mem_supported' D.host.E (l b)).1 (hl b) i hi
  refine ⟨fun a b => (if a = b then 1 else 0) + (if h : a.val < D.R.rS then l b ⟨a.val, h⟩ else 0), ⟨?_, ?_⟩, ?_⟩
  · intro a b hba
    dsimp only
    rw [if_neg (ne_of_gt hba), zero_add]
    split_ifs with h'
    · exact hz b _ (by show ¬ a.val < b.val; have := Fin.lt_def.1 hba; omega)
    · rfl
  · intro a
    dsimp only
    rw [if_pos rfl]
    split_ifs with h'
    · rw [hz a _ (by simp), add_zero]
    · rw [add_zero]
  · intro b
    rw [Formalism.L2.SG.Saturated.frame_mapL]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true,
      zero_smul, add_zero, frame_castSucc, Fin.eta]
    have e := hx b
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
    rw [e]
    abel

theorem term_at_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 →
      ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → t.G ≠ 0 ∧ ptPN t = toPts w := by
  intro D X Y u u' F F' w hZ hG t Λ hTG
  obtain ⟨g, ⟨hg, h1⟩, ⟨-, h2⟩, -⟩ := hTG
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  have hcell : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨1, 1, fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_lt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩,
      fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_gt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩, ?_⟩
    rw [hZ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨-, hB⟩ := GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D F F' w hT hT' hcell
  obtain ⟨hcell2, hG2⟩ := hB _ _ (tri_of_adapt g (lf D (X.Fu u)) F hg h1) (tri_of_adapt g t.frame F' hg h2)
  replace hcell2 : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w :=
    (congrArg (fun Z => IsInCell (ZhatOM Z) w) (Formalism.L2.SG.Saturated.zhat_mapL g hg (lf D (X.Fu u)) t.frame)).mp hcell2
  replace hG2 : Gval (lf D (X.Fu u)) t.frame = Gval F F' :=
    (Formalism.L2.SG.Saturated.gval_mapL g hg (lf D (X.Fu u)) t.frame).symm.trans hG2
  have hGt : t.G ≠ 0 := by rw [Formalism.L2.SG.Pf.SatGram.gterm_G Y t, hG2]; exact hG
  have hat : t.toTerm.atPt w := ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, fun h0 => hG (hG2.symm.trans h0), hcell2⟩
  have hrel : t.toTerm.relevant := Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' _ _ t.toTerm w hat
  have hsp := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hat, hrel⟩
  have heq := Formalism.L2.SG.Pf.cellPtUnique_of Formalism.L2.SG.Pf.cell_point_uniqueness
    (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u) t.toTerm _ _ hsp hat
  exact ⟨hGt, by show toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) = toPts w; rw [heq]⟩

end GlobalTheory.Unfold.BasePt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThrEAddOneLt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.DsigSize

theorem thrE_add_one_lt {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) :
    Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
  have hn := Formalism.MainNotions.nS_cast D
  have h6 := Formalism.MainNotions.six_le_n D
  rw [← hn] at h6 ⊢
  set n : ℝ := ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) with hnd
  have e2 : Formalism.MainNotions.GapDS.thrE (epsSH D.R) ≤ 4 * n ^ 3 := Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by linarith)
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have hmf : D.R.m ^ 4 ≤ D.R.f := by unfold StandingHypotheses at hH; exact hH.2.2.1
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast le_trans this hmf
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hn19 : 4 * n ^ 3 + 2 < n ^ 19 := by
    have e3 : n ^ 19 = n ^ 3 * n ^ 16 := by ring
    have e4 : (6 : ℝ) < n ^ 16 := by
      have : (6 : ℝ) ^ 16 ≤ n ^ 16 := pow_le_pow_left₀ (by norm_num) h6 16
      nlinarith
    have e5 : 1 ≤ n ^ 3 := one_le_pow₀ (by linarith)
    rw [e3]; nlinarith
  have e6 : n ^ 19 ≤ n ^ 19 * (D.R.f : ℝ) ^ 5 := le_mul_of_one_le_right (by positivity) hf5
  have e7 : n ^ 19 * (D.R.f : ℝ) ^ 5 ≤ (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5) :=
    le_mul_of_one_le_left (by positivity) hCL
  have e8 : Cl * n ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5) := by ring
  rw [e8]; linarith

theorem dsigHC : Formalism.L2.SG.Pf.SzHypFD.DsigHC := by
  intro D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ
  exact GlobalTheory.dsig_eq_fdegHC_of_gap D hT τ _ (Formalism.MainNotions.BridgeLemma.szh_hc hH τ) (Formalism.MainNotions.BridgeLemma.szh_gap hH τ)
    (thrE_add_one_lt hH hCL)

end GlobalTheory.DsigSize
end
end

