import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0735
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0702
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0746
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AutomorphicArithmetic.BlochKatoExtensions.PhtCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BareStatementOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0119
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActionReadAtMember
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenLocAt

section Gen

open Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)

theorem liftForm_lvlAct (hok : A3.fam3.Ok3 1) (k : Fin D.R.m) (s : T) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) :
    (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s (lvlAct F k s a x) : A3.A.fam.amb.FL k s) =
      ∑ g : G, a.coeff g • A3.A.fam.amb.opL k s (Sum.inr g) (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x) :=
  GlobalTheory.ClassSumIdentity.lvlE_lvlOp hok.ok2.conj _ ((hok.ok2.lifts k s).hpos _) _ (hok.ok2.lifts k s).act _ _ a ha x

variable (R) in

theorem jV_sum (k : Fin D.R.m) (s : T) (c : G → D.what₂.LL) (v : G → A3.A.fam.amb.FL k s) :
    R.jV k s (∑ g, c g • v g) = ∑ g, D.what₂.embLL (c g) • R.jV k s (v g) :=
  (map_sum (R.jV k s) (fun g => c g • v g) Finset.univ).trans
    (Finset.sum_congr rfl fun g _ => (R.jV k s).map_smulₛₗ (c g) (v g))

variable (R) in

theorem extV_sum (k : Fin D.R.m) (s : T) (c : G → ℂ) (w : G → (R.HV k s).H) (y : GA D (Vc D k)) :
    R.extV k s (∑ g, c g • w g) y = ∑ g, c g • R.extV k s (w g) y := by
  have e := map_sum (R.extV k s) (fun g => c g • w g) Finset.univ
  refine (congrFun e y).trans ((Finset.sum_apply y Finset.univ _).trans (Finset.sum_congr rfl fun g _ => ?_))
  exact congrFun ((R.extV k s).map_smul (c g) (w g)) y

theorem extV_act {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks) (hM : R.IsModels) (hred : R.grp_red_L)
    (k : Fin D.R.m) (s : T) (g : G) {κ : GA D (Vc D k)} (hκ : IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) κ)
    (v : A.fam.amb.FL k s) (y : GA D (Vc D k)) :
    R.extV k s (R.jV k s (A.fam.amb.opL k s (Sum.inr g) v)) y =
      (levChi (Vc D k) (R.βV k) (flagL (R.datVt k s)) κ)⁻¹ • R.extV k s (R.jV k s v) (y * κ) := by
  have e1 := Formalism.IndefR.Eqv.Act.jV_act R hM k s g v _ (Formalism.IndefR.Eqv.Act.red_of_liftV R hred k s g hκ)
  have e2 := Formalism.IndefR.Eqv.Act.ext_g0Act (R.cV k) (hM.cV k) (levEnv (Vc D k) (R.βV k) (R.datVt k s)).ch
    ⟨_, Formalism.IndefR.Eqv.Act.mem_Q_of_liftV R k s g hκ⟩ κ hκ.1 rfl ((R.HV k s).e (R.jV k s v)) y
  have e3 := congrArg (fun f => (R.cV k).ext f y) e1
  have hch : ((((levEnv (Vc D k) (R.βV k) (R.datVt k s)).ch ⟨_, Formalism.IndefR.Eqv.Act.mem_Q_of_liftV R k s g hκ⟩)⁻¹ : ℂˣ) : ℂ) =
      (levChi (Vc D k) (R.βV k) (flagL (R.datVt k s)) κ)⁻¹ := Units.val_inv_eq_inv_val _
  refine (Formalism.IndefR.Eqv.Act.extV_apply R k s _ y).trans (e3.trans (e2.trans ?_))
  exact congrArg₂ (fun (c : ℂ) (w : (R.cV k).W) => c • w) hch (Formalism.IndefR.Eqv.Act.extV_apply R k s _ (y * κ)).symm

theorem actRead_of (hM : R.toRealDat.IsModels) (hred : R.toRealDat.grp_red_L) (hok : A3.fam3.Ok3 1) : ActRead Y := by
  intro s h k a ha κ hκ x y
  have hr : ∀ x', adForm Y (Y.tup s) h k (ratForm Y k s x') =
      R.extV k s (R.jV k s (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x')) := fun x' => Y.mtRead k s h x'
  have e1 : R.jV k s (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s (lvlAct F k s a x)) =
      ∑ g : G, D.what₂.embLL (a.coeff g) •
        R.jV k s (A3.A.fam.amb.opL k s (Sum.inr g) (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x)) :=
    (congrArg (R.jV k s) (liftForm_lvlAct hok k s a ha x)).trans (jV_sum R k s _ _)
  refine (congrFun (hr _) y).trans ((congrFun (congrArg (R.extV k s) e1) y).trans
    ((extV_sum R k s _ _ y).trans (Finset.sum_congr rfl fun g _ => ?_)))
  refine (congrArg (fun w => D.what₂.embLL (a.coeff g) • w) (extV_act R.toRealDat hM hred k s g (hκ g) _ y)).trans ?_
  exact (smul_smul _ _ _).trans (congrArg _ (congrFun (hr x) (y * κ g)).symm)

end Gen

theorem actRead_at : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ =>
    actRead_of t.r.Y t.r.z.pins.char.base.models t.r.z.pins.char.base.grp.red_L t.r.intersectionNumber_baseChange.ok

end GlobalTheory.CenLocAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsReadingTransportLaterHeckeGaloisStageStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicRowsReading_transport_laterHeckeGaloisStage : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I → (∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR) → ∀ (m : Moved (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), m.Copy → m.Coh → ∀ (sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), s.RR = x.s.RR → HEq s.jEE x.s.jEE → (∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd)).coeff (sg.iso g)) → s.cen μ c = x.s.cen μ c0) → ∃ r : ReadPk m s, r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y) := by
  first | exact @GlobalTheory.Mem.R3.Rw.CopyRead.read_copyN | exact GlobalTheory.Mem.R3.Rw.CopyRead.read_copyN | (intros; apply GlobalTheory.Mem.R3.Rw.CopyRead.read_copyN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleAndLamUsedAllStates
section
namespace GlobalTheory.HeightCounting.Up.RowsAtStates

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

set_option maxHeartbeats 2000000 in

theorem parts_lam_overRows : PrN → GlobalTheory.NRows.HypothesesX → OverRows fun _ _ _ _ w Z _ _ z p0 Y => RationalReadingWithoutCongruence z.R z.F p0 Y →
    (∃ L : SizeData₂ (w.st Z).toD7, Nonempty (ParameterChoice' (w.st Z).toD7 L)) → SumRepresentations.adm8 (w.st Z).toD7 ∧ GlobalTheory.NRows.LamUsed (w.st Z).toD7 := by
  intro hN hPX
  refine EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev) fun K _ _ _ _ hHost => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w _ Z Wt hX z p0 Y hHo hEx _ hGrp _ hRd hp
  have hH : Formalism.IndefR.Links.HostHyp (w.st Z).toD7 := (hHost (w.st Z) hO).1
  have hGS : Formalism.L2.DIV.GoodStable z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hN.greenC
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) hGrp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL z.Xg z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [z.good.2, z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hT : TypesTrue (w.st Z).toD7.ntypes z.R.C.P z.R.C.W := by
    rw [z.lev.C, w.C_eq]
    exact hGrp
  have hME := GlobalTheory.T.multiplicity_equality_statement hPX.ana hPX.dsc hN.decay hN.hc hPX.trc hPX.dm hPX.flath hPX.pc hPX.hcc hPX.lc hPX.lw hN.zel
    hN.what₂.geo hN.greenC z.R z.F hHo.ok z.pins.char hEx hH hp B.ccK_top z.pins.keep.guard
    (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue z.pins.char.base.lev hT)
  have hIR : Formalism.BasicNotions.Rows.IsotRank (w.st Z).toD7.what₂ :=
    GlobalTheory.Mem.R3.isotRank_of_multEq hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG _ Y z.pins hHo hH hGS
      (GlobalTheory.CuspDec.cuspDecomp hN.hc hN.decay _) hME
  have h0 := GlobalTheory.T.positive_scalars_without_congruence_lengths hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y hRd z.pins hHo hH
  exact ⟨h0.1 hIR, h0.2⟩

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem parts_lam_allSt : PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ _ _ _ x =>
    SumRepresentations.adm8 (Dof x) ∧ GlobalTheory.NRows.LamUsed (Dof x) := by
  intro hN hPX
  have h1 := GlobalTheory.HeightCounting.Up.RowModel.overRows_allSt (parts_lam_overRows hN hPX)
  have h2 := GlobalTheory.T.exists_sizeData_parameterChoice.2
  refine (StepW.and h1 h2).trans (StepW.of_all fun K B f T w _ _ hh P x => ?_)
  obtain ⟨hA, hB⟩ := hh
  exact hA P x x.r.Z (hB P x).1

end GlobalTheory.HeightCounting.Up.RowsAtStates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicChartLiftHolomorphicPeriodMaps
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

theorem GlobalTheory.ShFam.chart_lift_periods_of_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)) (P : ReciprocityTheory.L2DbarEstimates.V X.dim → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ c'.e y ∈ B ∧ B ⊆ c'.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∃ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), cxPt T.Z q = cxOf e σ hj (c'.e.symm b) ∧ Fu.u i (P b) = q.x := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ g ty Fu X j hj hjo y hy c' hyc
  have := T.Z.jQ_open
  have : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  let L := EuclideanSpace.equiv (Fin X.dim) ℂ
  have hsy := GlobalTheory.TrueCx.TorHolo.isHolTo_symm c'
  have hsj := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hsy j
  have hB₀ := (hsj T.Z.jQ.opensRange 0).1
  set B₀ := {b ∈ c'.e.target | ⊤ ≤ ((c'.e.symm b).1 ≫ j) ⁻¹ᵁ T.Z.jQ.opensRange} with hB₀def
  have hb₀ : c'.e y ∈ B₀ := by
    refine ⟨c'.e.map_source hyc, ?_⟩
    rw [c'.e.left_inv hyc]
    intro s _
    have h1 : y.1 s ∈ openPart j := hy (Set.mem_univ s)
    exact not_not.1 h1
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ T.Z.jQ = (c'.e.symm b).1 ≫ j := fun b hb =>
    ⟨IsOpenImmersion.lift T.Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨(hw _ hb₀).choose⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion T.Z.jQ
    (LocLift.isHolTo_congr (LocLift.isHolTo_mono hsj hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (Limits.pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ Limits.pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← T.Z.jQ_over, ← Category.assoc, hw b hb]
    exact (Category.assoc _ _ _).trans (cxOf e σ hj (c'.e.symm b)).2
  have hB₁ : IsOpen (L.symm ⁻¹' B₀) := hB₀.preimage L.symm.continuous
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := Fu.lift X.dim (L.symm ⁻¹' B₀) (fun x => w (L.symm x) ≫ Limits.pullback.fst _ _) hB₁
    (fun x hx => by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl)
    (LocLift.isHolTo_comp hyh hB₁ L.symm.differentiableOn fun x hx => hx) (L (c'.e y))
    (by simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hb₀)
  refine ⟨i, L ⁻¹' B', fun v => P (L v), hB'.preimage L.continuous, hb', fun v hv => ?_, fun v hv => hP.1 _ hv,
    fun x => (hP.2 x).comp L.differentiableOn fun v hv => hv, fun b hb => ?_⟩
  · have := hsub hv
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    exact this.1
  · have hb1 := hsub hb
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at hb1
    have h2 := hu _ hb
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h2
    have ho : (w b ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd b hb1]
      exact OpenReg.spMap_comp _ _
    obtain ⟨q, hq⟩ : ∃ q : FrPt Xo c (CAt σ), q.x = w b ≫ Limits.pullback.fst _ _ := GlobalTheory.FlagTan.exists_frPt _ ho
    refine ⟨q, Subtype.ext ?_, h2.trans hq.symm⟩
    have h3 : GlobalTheory.AllWt.ptF (S := CAt σ) q = w b :=
      Limits.pullback.hom_ext ((ptF_fst q).trans hq) ((ptF_snd q).trans (hsnd b hb1).symm)
    exact (congrArg (· ≫ T.Z.jQ) h3).trans (hw b hb1)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmChernRootsMulFibrePoint
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GoodMetric.FibreAntisymm
open GlobalTheory.GoodMetric

theorem rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
    (R : MvPolynomial (ι × ℕ) ℝ) :
    rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
  have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
    have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
      funext i; rfl
    rw [e, ← rename_rename, rename_esymm]
  exact AlgHom.congr_fun h R

theorem antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
    (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
  unfold antisymm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul, rename_chernRoots, mul_smul_comm]

theorem prod_Ioi_rev {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
      ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
    intro f
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j; simp
  rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
    ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
  refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
  simp [Fin.rev_lt_rev]

theorem sum_sign_prod_neg_pow {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
      ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
  let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
  have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
    rw [Matrix.det_apply']
    rfl
  have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
    ext j i
    simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
    GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde, ← prod_Ioi_rev]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Fin.rev_rev]
  ring

theorem antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
  have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
      ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
        ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
          ∏ i : Fin (m τ), (-(X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
    intro w
    unfold fibrePoint
    rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [map_pow, map_neg, rename_X]
  unfold antisymm
  rw [Finset.sum_congr rfl fun w _ => hw w]
  rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
          ∏ i : Fin (m τ), (-(X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
  unfold rootDiscr
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))

end GlobalTheory.GoodMetric.FibreAntisymm

namespace GlobalTheory.GoodMetric

theorem antisymm_chernRoots_mul_fibrePoint : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ),
    GlobalTheory.GoodMetric.antisymm (GlobalTheory.GoodMetric.chernRoots m R * GlobalTheory.GoodMetric.fibrePoint m) =
      GlobalTheory.GoodMetric.chernRoots m R * GlobalTheory.GoodMetric.rootDiscr m := by
  intro ι _ m R
  rw [FibreAntisymm.antisymm_chernRoots_mul, FibreAntisymm.antisymm_fibrePoint]

end GlobalTheory.GoodMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanCompatOfLiterature
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.ArchFromLit

theorem archCmp_of_lit : LitLoc → LitAut → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL := by
  intro hLoc hAut hL
  exact
    { pht := GlobalTheory.PhtCompare.phtCmp
      lp := GlobalTheory.T.column_twisted_args_first hAut.art hLoc.chev hLoc.brauer hLoc.conv hLoc.exh hLoc.cos hLoc.bz hL
      cg := GlobalTheory.T.column_twisted_args_second hL hAut.fin hAut.js.1 hAut.cusp }

end GlobalTheory.ArchFromLit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadPlacesSubOfAdmissibleTwist
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

namespace GlobalTheory.LevCmp.BadV

theorem unr_of_twist {R : Ranks} {H : Host R} {S : Set ℕ} {ξ : HChar H.E} (hξ : Chr.IsTwist H S ξ) {p : ℕ} (hp : p.Prime)
    (hS : p ∈ S) (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ξ.UnrAt u := by
  by_contra hn
  obtain ⟨-, h1, -, h2⟩ := hξ.2.2.2 u hn
  have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) ∈ u.asIdeal := Ideal.absNorm_mem _
  by_cases e : Ideal.absNorm u.asIdeal = p
  · exact h2 (e ▸ hS)
  · obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) (p : 𝓞 H.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes h1 hp).2 e)
    exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ hu)))

theorem not_unr_of_delta {R : Ranks} {H : Host R} {p : ℕ} {δ : HChar H.E} (hδ : IsDelta (H := H) p δ)
    (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ¬ δ.UnrAt u := by
  intro hn
  have h15 := (hδ.ine u hu 1).1 fun y hy => by rw [pow_one]; exact hn y hy
  exact absurd h15 (by decide)

theorem unr_of_mul_left {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt u) (h' : (χ * χ').UnrAt u) : χ'.UnrAt u := fun y hy => by
  have e := h' y hy
  rwa [HChar.loc_mul, h y hy, one_mul] at e

theorem unr_of_mul_right {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ'.UnrAt u) (h' : (χ * χ').UnrAt u) : χ.UnrAt u := fun y hy => by
  have e := h' y hy
  rwa [HChar.loc_mul, h y hy, mul_one] at e

theorem badV_sub_gPl_qPl : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → NX.badV (Dof x) i (QOf P v) ⊆ gPl (Dof x) ∪ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) := by
  intro _ hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok
  have hQ : QOf P v = T.Q v := GlobalTheory.HeightCounting.Up.Model.qOf_eq v
  have h2 := P.q.mu.tw v
  intro u hu
  obtain ⟨w', hw'u, hw'⟩ := hu
  by_cases hg : u ∈ gPl (Dof x)
  · exact Or.inl hg
  refine Or.inr ⟨hg, w', hw'u, ?_⟩
  have hmu : ((cfOf x).mu0 j).UnrAt w' :=
    ((cfOf x).isMu0 j).unr w' fun k hk => hg ⟨w', hw'u, k, hk⟩
  intro hun
  have hxi : (T.xiTw f v).UnrAt w' := by
    have hx : (w.I.xi (P.q.W₀.muTw v)).UnrAt w' := unr_of_mul_left hmu hun
    rwa [h2] at hx
  unfold TwDat.xiTw at hxi
  have hpde : B.host.pde ∈ offSet B.toPre := by simp [offSet]
  have hpde' : B.host.pde' ∈ offSet B.toPre := by simp [offSet]
  rcases hw' with hq | hG | hp
  · rw [hQ] at hq
    have hψ : ¬ (T.psi v).UnrAt w' := fun h => ((T.psi_is v).ram w').1 h hq
    have hd : (if B.places.resChar v = B.host.pde then f.del' else f.del).UnrAt w' := by
      split_ifs
      · exact f.isDel'.unr w' fun ho => hψ (unr_of_twist (T.psi_tw v) B.host.pde'_prime hpde' w' ho)
      · exact f.isDel.unr w' fun ho => hψ (unr_of_twist (T.psi_tw v) B.host.pde_prime hpde w' ho)
    exact hψ (unr_of_mul_left hd hxi)
  · exact hg ⟨w', hw'u, hG⟩
  · have hp' : w' ∈ placesOver (Dof x).host.E (if (Dof x).ntw.l i = (Dof x).host.pde then (Dof x).host.pde' else (Dof x).host.pde) := by
      rw [← (Dof x).ntw.pD_eq i]; exact hp
    rw [hl] at hp'
    change w' ∈ placesOver B.host.E (if B.places.resChar v = B.host.pde then B.host.pde' else B.host.pde) at hp'
    split_ifs at hp' hxi
    · exact not_unr_of_delta f.isDel' w' hp'
        (unr_of_mul_right (unr_of_twist (T.psi_tw v) B.host.pde'_prime hpde' w' hp') hxi)
    · exact not_unr_of_delta f.isDel w' hp'
        (unr_of_mul_right (unr_of_twist (T.psi_tw v) B.host.pde_prime hpde w' hp') hxi)

end GlobalTheory.LevCmp.BadV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormCellMultiplicityPosStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedFormCellMultiplicity_pos : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m : ℕ} (δ : Fin m → balForms bar X), 0 < cellMult bar δ := by
  first | exact @GlobalTheory.PolFan.cellMult_pos | exact GlobalTheory.PolFan.cellMult_pos | (intros; apply GlobalTheory.PolFan.cellMult_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BareStatementOfDiscreteSeriesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bare_statement_of_discrete_series : PrN → GlobalTheory.Published.DiscreteSeriesExists → BareK := by
  first | exact @GlobalTheory.HeightCounting.Up.bareStatement_of_known_theorems | exact GlobalTheory.HeightCounting.Up.bareStatement_of_known_theorems | (intros; apply GlobalTheory.HeightCounting.Up.bareStatement_of_known_theorems <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainModelGramContDiffIsUnitStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDomainModelGram_contDiff_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∀ τ, MContDiffAt 2 (fun u => modelGram H Dw (coordOf ix u) τ) w ∧ IsUnit (modelGram H Dw (coordOf ix w) τ).det := by
  first | exact @GlobalTheory.PointChern.modelGram_smooth_isUnit | exact GlobalTheory.PointChern.modelGram_smooth_isUnit | (intros; apply GlobalTheory.PointChern.modelGram_smooth_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalTrivialOfRelativeAmpleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_trivial_of_relative_ample : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), IsProper t.G.hom → RelAmple t.G t.PP.L → GlobalTheory.LN.PolAt t (jK R) → KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic | exact GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic | (intros; apply GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic <;> assumption)
end

