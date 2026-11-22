import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0406
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0364
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0509
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0052
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ItSpansPkStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.itSpans_MY_succ : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) := by
  first | exact @_root_.GlobalTheory.Core.Mi.SpanY.itSpans_pk_alt | exact _root_.GlobalTheory.Core.Mi.SpanY.itSpans_pk_alt | (intros; apply _root_.GlobalTheory.Core.Mi.SpanY.itSpans_pk_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IteratesSpanLastStep
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.itSpans_MY_last_MX : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY (D.R.m - 1)) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ItX := by
  first | exact @_root_.GlobalTheory.Core.Mi.SpanX.itSpans_pk_alt | exact _root_.GlobalTheory.Core.Mi.SpanX.itSpans_pk_alt | (intros; apply _root_.GlobalTheory.Core.Mi.SpanX.itSpans_pk_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpBoundOfFactsLargeFamily
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.LargeJumps
theorem jump_bound_of_facts_large_family_alt : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x),
    _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a) := by
  intro eps Fm
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a hF => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  have hA := (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1
  exact _root_.GlobalTheory.JumpStatement.holds_all_alt _ _ (hF.admJ _ hA)
end GlobalTheory.LargeJumps
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairs
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace
variable {D : D7} {c : Comm D} {v : VCom c}
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
def KeepsPairsAlt (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (κ : GA D (D.sp.X 0)) : Prop :=
  ∀ i (g : GL (Fin (D.sp.X 0).rank) a.k), (mt (D.sp.X 0) κ).map (a.o.p i).pr = (a.o.β 0 i).b * g.val * (a.o.β 0 i).b' →
    g • a.o.Q 0 i = a.o.Q 0 i
def TraceAtElement (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (κ : GA D (D.sp.X 0)) : Prop :=
  ∀ i g, IsMatrixInFrameOfXZero (a.G i) κ g → GlobalTheory.RootEx.embX ((a.G i).s + 1) g ∈ (((a.G i).S.T (Fin D.R.t)).lev 0 ((a.G i).s + 1) (Nat.zero_add _)).J
def InLevelGroup (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (κ : GA D (D.sp.X 0)) : Prop :=
  GlobalTheory.FinPl.Moves (D.sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => True) ∧ _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ ∧ _root_.GlobalTheory.FamTrace.TraceAtElement a κ
def LevelAtElement (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (x : GA D (Yc D 0)) : Prop :=
  ∀ i m, (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m → m ∈ (((a.G i).S.T (Fin D.R.t)).lev 0 ((a.G i).s + 1) (Nat.zero_add _)).J
def InLevelGroupOfY (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (x : GA D (Yc D 0)) : Prop :=
  GlobalTheory.FinPl.Moves (Yc D 0) x (a.v.N 0) (a.v.N 0) (fun p => p ∉ a.v.gP) ∧ _root_.GlobalTheory.FamTrace.LevelAtElement a x
end GlobalTheory.FamTrace
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KomWeilUnramStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_data_local_relation_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι), f.RowOK → f.ColOK → v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ShapeOff v o → ∀ t j, j < D.R.m → ∃ μ, IsWeilDatumO f.c.ψ _ _ μ μ ((f.t t).kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v := by
  first | exact @_root_.GlobalTheory.Fam.kom_weil_unram_alt | exact _root_.GlobalTheory.Fam.kom_weil_unram_alt | (intros; apply _root_.GlobalTheory.Fam.kom_weil_unram_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatVNEqOffLevelStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_self_dual_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  first | exact @_root_.GlobalTheory.Fam.latV_N_eq_off_level_alt | exact _root_.GlobalTheory.Fam.latV_N_eq_off_level_alt | (intros; apply _root_.GlobalTheory.Fam.latV_N_eq_off_level_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
section Fit
open GlobalTheory.ChiGrid Formalism.L2.Host
variable {T : Type} {Lc : LevCh D T} {sc : Consts}
end Fit
def LeafConditions (Comparison₂ : TieT) (Q : PropT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, ∀ C, C0 ≤ C → _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ d : FunIn p CF, Comparison₂ p CF d → Q p CF d C CH
def ExistsFunctionIn (Fld : FldT) (Comparison₂ : TieT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => DIVinN Fm →
  _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat → GridFit p G → Fld p CF G W →
    ∃ d : FunIn p CF, d.G = G ∧ Comparison₂ p CF d
def LeafMinimalMass (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun _ _ d C _ => LeafMM d.O C
def LeafUniqueMap (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d _ _ =>
  ∃ ze : Tup p → _, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
    LeafC (p.S false) (d.data ze ∅ fun _ => 0)
def LeafKernel (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun _ _ d _ _ => LeafKer d.O
def LeafFixedPoint (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b
def LeafHeightMapBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ =>
  ∀ vb : Matrix (Fin d.n) (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0)) _,
    vb * (Df p).Pq p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 →
      Formalism.HN.htMap (Pi.basisFun _ (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0))) ((Df p).XQ p.P.A3.fam3.base3.μ0)
        (Pi.basisFun _ (Fin d.n)) d.X' (Matrix.mulVecLin vb) ≤ d.O.bIPa C p.Z.b
def LeafInfinitePlaceBound : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ =>
  ∃ g : InfinitePlace _ → ℝ, (∀ v q, (Df p).Qp p.P.A3.fam3.base3.μ0 q ≠ ⊥ →
      g v ≤ ∑ j, Real.log ((p.S false).lam j p.P.A3.fam3.base3.μ0 q v)) ∧
    -(3 * C * d.O.f * d.O.m * (d.O.N : ℝ) ^ 2 * Real.log p.Z.b) ≤ Formalism.PairingDivisionLocalBalance.meanInf _ g
def LeafUniqueSquareRoot (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafOneSquare d.O (p.S false).μ C p.Z.b
def LeafDensity (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => PrimeCountingSumBound d.O C p.Z.x p.Z.b
def LeafIntegrality (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafINT d.O C p.Z.b
def ArchimedeanCondition (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafARCH d.O C p.Z.b
def LeafThetaBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafTHB d.O C p.Z.x p.Z.b
def LeafWeightBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafWt d.O C p.Z.b
def DescentHeightCondition : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d _ _ => leafHypothesesConst d.O ∧ LatticeConstantBound d.O p.Z.b
def RankGapBound' : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ => DegreeAndSizeBounds d.O C p.Z.b
def RamifiedSumBound' : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ => PrimePowerModuliSumBound d.O C p.Z.b ∧ LeafCS d.O p.Z.b
def DescentPolynomialCondition : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C CH => LeafPol d.O C p.Z.x CH p.Z.b
def ScaleCondition : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p =>
  1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b
def BundleCondition : Prop := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' →
  (Df p).WF ∧ ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false
def ConstantFunctionFits (Fld : FldT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => HasGrid Fld p CF → ∀ C, (p.S false).FUN (p.N C CH)
theorem evPt_and' {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm P) (hQ : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => P x hx i p ∧ Q x hx i p :=
  let ⟨a, ha⟩ := hP
  let ⟨b, hb⟩ := hQ
  ⟨max a b, fun x hx h i p hp => ⟨ha x hx (le_of_max_le_left h) i p hp, hb x hx (le_of_max_le_right h) i p hp⟩⟩
theorem evPt_mono {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm P) (h : ∀ x hx i p, p.PointConditions' → P x hx i p → Q x hx i p) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q :=
  let ⟨a, ha⟩ := hP
  ⟨a, fun x hx h' i p hp => h x hx i p hp (ha x hx h' i p hp)⟩
theorem LeafConditions.mono {Comparison₂ Tie' : TieT} {Q Q' : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q)
    (h' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF) (C CH : ℝ), p.PointConditions' → Tie' p CF d →
      Comparison₂ p CF d ∧ (Q p CF d C CH → Q' p CF d C CH)) : _root_.GlobalTheory.BigTop.Fun.LeafConditions Tie' Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF => (h CF hCF).imp fun Fm CH _ a hN => ?_⟩
  obtain ⟨C0, a⟩ := a hN
  exact ⟨C0, fun C hC => _root_.GlobalTheory.BigTop.Fun.evPt_mono (a C hC) fun _ _ _ p hp b d hd =>
    (h' p CF d C CH hp hd).2 (b d (h' p CF d C CH hp hd).1)⟩
theorem LeafConditions.and {Comparison₂ : TieT} {Q Q' : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q) (h' : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q') :
    _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ fun p CF d C CH => Q p CF d C CH ∧ Q' p CF d C CH := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  refine ⟨max a b, fun CF hCF => ((h CF (le_of_max_le_left hCF)).and (h' CF (le_of_max_le_right hCF))).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1 hN
  obtain ⟨C1, c2⟩ := c.2 hN
  exact ⟨max C0 C1, fun C hC => _root_.GlobalTheory.BigTop.Fun.evPt_mono (_root_.GlobalTheory.BigTop.Fun.evPt_and' (c1 C (le_of_max_le_left hC)) (c2 C (le_of_max_le_right hC)))
    fun _ _ _ _ _ e d hd => ⟨e.1 d hd, e.2 d hd⟩⟩
theorem LeafConditions.of_noTie {Q : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition Q) (Comparison₂ : TieT) : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q :=
  h.mono fun _ _ _ _ _ _ _ => ⟨trivial, id⟩
theorem fun0Fit_of_leaves_alt (Fld : FldT) (Comparison₂ : TieT) (hB : _root_.GlobalTheory.BigTop.Fun.BundleCondition) (hS : _root_.GlobalTheory.BigTop.Fun.ScaleCondition) (hE : _root_.GlobalTheory.BigTop.Fun.ExistsFunctionIn Fld Comparison₂) (h1 : _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass Comparison₂) (h2 : _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap Comparison₂)
    (h3 : _root_.GlobalTheory.BigTop.Fun.LeafKernel Comparison₂) (h4 : _root_.GlobalTheory.BigTop.Fun.LeafFixedPoint Comparison₂) (h5 : _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound Comparison₂) (h6 : _root_.GlobalTheory.BigTop.Fun.LeafInfinitePlaceBound) (h7 : _root_.GlobalTheory.BigTop.Fun.LeafUniqueSquareRoot Comparison₂) (h8 : _root_.GlobalTheory.BigTop.Fun.LeafDensity Comparison₂) (h9 : _root_.GlobalTheory.BigTop.Fun.LeafIntegrality Comparison₂) (h10 : _root_.GlobalTheory.BigTop.Fun.ArchimedeanCondition Comparison₂)
    (h11 : _root_.GlobalTheory.BigTop.Fun.LeafThetaBound Comparison₂) (h12 : _root_.GlobalTheory.BigTop.Fun.LeafWeightBound Comparison₂) (h13 : _root_.GlobalTheory.BigTop.Fun.DescentHeightCondition) (h14 : _root_.GlobalTheory.BigTop.Fun.RankGapBound') (h15 : _root_.GlobalTheory.BigTop.Fun.RamifiedSumBound') (h16 : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition) : _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits Fld := by
  obtain ⟨a, hA⟩ := _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h1 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h2 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h3 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h4 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h5 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h6 _) <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h7 <|
    _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h8 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h9 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h10 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h11 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h12 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h13 _) <|
    _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h14 _) <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h15 _) (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h16 _)
  obtain ⟨b, hE⟩ := hE
  refine ⟨max a b, fun CF hCF => (((hA CF (le_of_max_le_left hCF)).and (hE CF (le_of_max_le_right hCF))).and hS).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1.1 hN
  refine _root_.GlobalTheory.BigTop.Fun.evPt_mono (_root_.GlobalTheory.BigTop.Fun.evPt_and' (_root_.GlobalTheory.BigTop.Fun.evPt_and' (c1 (max C0 1) (le_max_left _ _)) (c.1.2 hN)) c.2) fun x hx i p hp e hG C => ?_
  obtain ⟨⟨e1, e2⟩, s1, s2, s3⟩ := e
  obtain ⟨G, W, g1, g2, g3⟩ := hG
  obtain ⟨d, rfl, hd⟩ := e2 G W g1 g2 g3
  obtain ⟨l1, ⟨ze, z1, z2, l2⟩, l3, ⟨Tf, dF, l4⟩, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16⟩ := e1 d ⟨g2, hd⟩
  obtain ⟨wf, R0, hR⟩ := hB p hp
  have v0 : (d.data ze Tf dF).vmu p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 := by
    show (ze _)⁻¹ • _ = _
    rw [z1, inv_one]
    exact one_smul _ _
  have v1 : ∀ Tf dF t, (d.data (fun _ => 1) Tf dF).vmu t = d.V t := fun _ _ _ => by
    show (1 : _)⁻¹ • _ = _
    rw [inv_one]
    exact one_smul _ _
  have hRR := R0.RR_spec Formalism.DivisionValues.lattice_gluing wf
  refine functional_lower_bound_of_conditions_numeric wf (p.S false) p.Z C CH (d.data ze Tf dF) (max C0 1) (hR ▸ R0.D_pos) (hR ▸ R0.h0) (hR ▸ R0.l1a)
    (hR ▸ R0.l1c) (hR ▸ R0.frames.1) (hR ▸ hRR.1) (hR ▸ hRR.2) (le_max_right _ _) s1 s2 s3 l1 l2 ?_ ?_ ⟨?_, l6⟩ l7 l8 l9 l10
    l11 l13.1 l13.2 l14 l15.1 l15.2 l12 l16
  · have : LinearMap.ker (d.O.vmu _).mulVecLin = _ := l3
    rw [v1] at this
    show LinearMap.ker ((d.data ze Tf dF).vmu _).mulVecLin = _
    rw [v0]
    exact this
  · have := GlobalTheory.finitePlaceBound_inv_rootOfUnity_smul _ ze _ _ _ z2 l4
    simp only [v1] at this
    exact this
  · intro vb hvb
    exact l5 vb (hvb.trans v0)
end GlobalTheory.BigTop.Fun
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevChiDatYtBaseStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stageY_zero_cc_of_mem_zero_set : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ∈ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).CC (_root_.GlobalTheory.BaseChain.com_z W) := by
  first | exact @_root_.GlobalTheory.BaseChain.initial_tuples_mem_stageY_zero_CC | exact _root_.GlobalTheory.BaseChain.initial_tuples_mem_stageY_zero_CC | (intros; apply _root_.GlobalTheory.BaseChain.initial_tuples_mem_stageY_zero_CC <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
variable (Y : Cov p i)
def RowsTAlt : Prop := p.PointConditions' ∧ RecTied D L
def EventuallyAtAllPoints {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p : Pt Fm x hx ι), _root_.GlobalTheory.CovTop.RowsTAlt p → Q x hx ι p
theorem EventuallyAtAllPoints.and {eps : ℝ} {Fm : FamP eps} {Q Q' : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop}
    (h : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm Q) (h' : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm Q') : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x hx ι p => Q x hx ι p ∧ Q' x hx ι p := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  exact ⟨max a b, fun x hx hle ι p hp =>
    ⟨h x hx ((le_max_left _ _).trans hle) ι p hp, h' x hx ((le_max_right _ _).trans hle) ι p hp⟩⟩
def LiftsCondition (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (PP C : ℝ), Prop) : Prop :=
  Closed FamHyp fun Fm _ => ∃ C : ℝ, 0 ≤ C ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x hx ι p => ∀ i, Q Fm x hx ι p i (Fm.parT x hx ι).PP C
def CoversCondition (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (_Y : Cov p i) (PP C : ℝ), Prop) : Prop :=
  _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x hx ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    ∀ Y : Cov p i, GoodCov p i Y → Q Fm x hx ι p i Y PP C
def GramCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => GramAt p i
def LiftRecursive : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => RecAt p i
def LiftTruncation : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => CutAt p i
def LiftBadSet : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => BadAt p i
def LiftLambdaBound : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => LamAt p i C
def SizeCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i PP C => SizeAt p i PP C
def MeasureCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => MeasAt p i C
def LiftRational : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => RatAt p i
def CoreBound' : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => CoreAt p i C
def LiftLowBound : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => LowAt p i C
def AnchorCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => AnchorAt p i C
def LowDefectCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → LowAt p i C
def DeepExistence : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 < (Fm.D x ι).R.m →
  ∃ Y : Cov p i, GoodCov p i Y
def DeepGoodness : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => DeepGoodAt p i Y
def RingCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => RingAt p i Y
def MapsCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => MapsAt p i Y
def CoverRank : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => RkAt p i Y PP
def MinimalGenerator : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => GminAt p i Y PP
def FlatDegreeCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => FlatDegAt p i Y
def FlatnessCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ C => FlatAt p i Y C
def UniformLowerBound : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ C => UAt p i Y C
def SumBoundCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => SumAt p i Y
def CoverDegree : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → DegAt p i Y u1
def ShareCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → ShareAt p i Y PP u1
def HeightCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HeightAt p i Y PP C u1
def CoverHeightSum : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HSAt p i Y PP C u1
def CovolumeBoundOfX : Prop := Closed FamHyp fun Fm CH =>
  ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)
def _root_.GlobalTheory.BigTop.CovolumeBound : Prop := Closed FamHyp fun Fm CH =>
  ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)
end GlobalTheory.CovTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkCommOfLawsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_data_unit_shift_relation_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : ∀ t, (ι → 𝓀[k]ˣ) → (f.t t).Col 0 → (f.t t).Col 0), RamUnitary D → f.c.Is → (∀ t, (f.t t).Is ∧ (f.t t).KBack ∧ (f.t t).TailRd ∧ LiftS o (f.t t) ∧ ReadS o (f.t t) ε (S₀ t)) → o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → (∀ t, Nonempty ((f.t t).Ch 0)) → (∀ t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧ ∀ α y, (f.t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt f t φ) y = (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) → (∀ t, ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt f t φ) → _root_.GlobalTheory.MiTop.LinkCommutes f := by
  first | exact @_root_.GlobalTheory.MiTop.linkComm_of_laws_alt | exact _root_.GlobalTheory.MiTop.linkComm_of_laws_alt | (intros; apply _root_.GlobalTheory.MiTop.linkComm_of_laws_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkZeroOfChartZeroAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem linkZero_of_chartZero_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u), _root_.GlobalTheory.MiTop.ChartAtZeroCondition f → (∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, d.B.lev = f.c.B 0 D.R.rS h₀) → d.b = (show GA D (D.sp.Y 0) from f.g.b 0) → _root_.GlobalTheory.MiTop.LinkVanishes f d := by
  intro D L hT Gi Gl Kc Yd cX ex W u f d hc hl hb n h₀ t φ
  obtain ⟨α₀, h1, h2, h3, -⟩ := hc t
  refine ⟨(h3 φ).1, fun G y v => ?_⟩
  obtain rfl : n = D.R.rS := by
    have : D.R.rS = D.R.m / 2 - 1 := rfl
    omega
  have e : ∀ g : GA D (Yc D 0) → ℂ, trc (Finsupp.single (f.g.b 0) 1) g = rTrans (f.g.b 0) g := fun g => by
    unfold trc
    rw [Finsupp.support_single _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  unfold _root_.GlobalTheory.MiTop.BottomData.per Tup.per Tup.perF
  rw [Finset.sum_eq_single α₀ (fun b _ hb => absurd (h1 b) hb) (by simp)]
  beta_reduce
  rw [h2, (h3 φ).2 y, hb]
  exact besLev_per_congr (hl h₀).symm _ HEq.rfl (heq_of_eq (e _))
end GlobalTheory.MiTop
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocFProdLevelStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_groups_matrix_reading_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ (j : ℕ) (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin (Yc D (j + 1)).rank) (Fin (Yc D j).rank) (Formalism.L2.DIV.kP PP)), omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) y = ∏ i, GlobalTheory.LocMod.StepVec.locF D.R.t j (r_le_Y j) (GlobalTheory.MovedDat.RdAt (G i) (pl i).1) (fun x => (G i).S.P.lam x) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1) (y (pl i).1) := by
  first | exact @_root_.GlobalTheory.MovedDat.locF_prod_level_alt | exact _root_.GlobalTheory.MovedDat.locF_prod_level_alt | (intros; apply _root_.GlobalTheory.MovedDat.locF_prod_level_alt <;> assumption)
end
end

