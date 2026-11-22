import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0600
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0134
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0137
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0746
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0602
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0601
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0135
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelectedRealization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0007
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0743
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0136
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0186
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DataOfBWit
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TopVal.TwSet
section Gen
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.SeeSaw.TopLevel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end Gen
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Args
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
end Args
set_option maxHeartbeats 2000000 in
theorem data_of_bWit_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (hw : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX = 1 ∧ (∀ t, (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Q t = q.w.I.Q ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) ∧
      ∀ g, g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)).H ↔ ∀ PP (h : PP ∈ (q.B.primes q.w.px).vGs) (h' : PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg),
        g ⟨PP, h'⟩ ∈ (GlobalTheory.Mem.Col2.TC.Ps q.w.I ⟨PP, h⟩).H := by
  have hu := _root_.GlobalTheory.MiS.Check.used_all_alt (_root_.GlobalTheory.Fam.packB_alt b)
  obtain ⟨x, a, ax, y, -, -, -, -, -, -, -, -, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  subst hx
  obtain ⟨-, -, hl, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → (∀ t, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) (k.P.I.tup t)) →
      (letI := k.B.alg
      k.B.Q.Rl.toRealDat.βX = 1 ∧ (∀ t, k.B.Q.Rl.toRealDat.Q t = q.w.I.Q (k.P.I.tup t)) ∧
      ∀ g, g ∈ (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true).H ↔
        ∀ PP (h : PP ∈ (q.B.primes q.w.px).vGs) (h' : PP ∈ k.B.Q.Rl.toRealDat.Pg),
        g ⟨PP, h'⟩ ∈ (GlobalTheory.Mem.Col2.TC.Ps q.w.I ⟨PP, h⟩).H) := by
    intro k hk
    subst hk
    intro hu
    letI := a.x.grp
    letI := a.x.fin
    letI := a.x.alg
    refine ⟨a.x.pins.keep.beta.2, fun t => ?_, fun g => ?_⟩
    · have h1 := eq_of_heq (hl _ (hu t)).1
      exact (congrArg a.x.R.Q (a.x.Y.tupT_tup t)).symm.trans h1
    · exact (by with_unfolding_all exact (lev_twArgs a g :))
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq hu
set_option maxHeartbeats 2000000 in
theorem levS_iff_cls_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X'), g ∈ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) ↔ ∃ κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1 := by
  intro hL p K q c b hw u t h g
  obtain ⟨hOk, ⟨hPins⟩, -, -, l0, tw, he, ht, -, -, s⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw
  obtain ⟨hβ, hQ, hH⟩ := _root_.GlobalTheory.TopVal.TwSet.data_of_bWit_alt q b hw
  have hPg : (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg = (q.B.primes q.w.px).vGs := Finset.ext (_root_.GlobalTheory.Fam.BundleLev.levTrue_packB_of_bWit q b hw).2.1
  have key : ∀ (Tw : TwForms (q.w.D q.Z)) (t' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes (_root_.GlobalTheory.Fam.packB_alt b).R.T.n.tp (_root_.GlobalTheory.Fam.packB_alt b).R.T.cols Tw),
      Tw = GlobalTheory.Mem.Col2.TC.tw q.w.I q.w.l l0 q.Z → HEq t' tw →
      (g ∈ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) ↔
        ∃ κ : (t'.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1) := by
    rintro _ t' rfl rfl
    exact mem_levS_of_reads q.w.I hOk hPins q.w.l q.Z _ _ (s.what₂ u _ h) _ hβ _ _ hPg (hQ t) _ hH _ _ _ g
  exact key _ _ he ht
end GlobalTheory.TopVal.TwSet
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigHkDatBack
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
section Gen
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (L : LocAll (lay0 (Dof x)))
theorem hkDat_of_hkDat_datL (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {i k Q α Rr} (h : HkDat (datL x L).R (_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l) i k Q α Rr) :
    HkDat x.m.z.R l.rat.In.Sb ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(h.split), (h.offS), (h.odd), (h.le), (h.elt), (h.reps)⟩
theorem eigVec_eW_of_hkDat_good_index (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (i σ k Q α Rr) (hd : HkDat x.m.z.R l.rat.In.Sb i k Q α Rr) (hσ : (Dof x).nd.goodRow σ) (y)
    (hy : y ∈ (Dof x).what₂.isot (i.1 + 1) σ) : EigVec x.m.z.R i k Q Rr (l.rat.In.eig (i.1 + 1) σ k Q) (x.r.Y.mj.eW i y) :=
  (by with_unfolding_all exact (eigAd_iff_eigVec x.r.Y l.rat.In.Sb l.rat.In.eig).mp l.rat.rat.eig i σ k Q α Rr hd hσ y hy)
theorem eigAd_smallPlaceSet_of_yRel (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    EigAd Y (_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l) (_root_.GlobalTheory.HeightCounting.Fin3.localEigenvalueDegree L l) :=
  (eigAd_iff_eigVec _ _ _).2 fun i σ k Q α Rr hd hσ y hy =>
    (by with_unfolding_all exact ((EigVec.congr (v' := ((Y.mj.eW i y))) (eigVec_loc L (_root_.GlobalTheory.HeightCounting.Fin3.eigVec_eW_of_hkDat_good_index l ((i)) ((σ)) k ((Q)) ((α)) ((Rr)) (((_root_.GlobalTheory.HeightCounting.Fin3.hkDat_of_hkDat_datL L l hd))) ((hσ)) ((y)) ((hy))))
      (((hY.eW i y)))) : _))
end GlobalTheory.HeightCounting.Fin3
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmtThetaL
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.Fin3
theorem emtTheta_L_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0)
    (hY : YRel L Y) : EMtTheta Y (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) := by
  intro v i hv y hy n a f h
  have h2 := HEq.trans (heq_of_eq h) (hY.eW i _)
  exact (by with_unfolding_all exact ((l.c.th ((v)) ((i)) ((hv)) ((y)) ((hy)) n ((a)) ((f)) (((eq_of_heq h2)))) : _))
end GlobalTheory.HeightCounting.Fin3
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqZeroOfPkAt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal.Inj
open NumberField IsDedekindDomain
open scoped TensorProduct
theorem eq_zero_of_pkAt_eq_zero_uni {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : Col2.TC B X} {l : I.Laws} {Z : Col2.TC.Later B (I.cols l)}
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    (gP : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t)
    (hz : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x g = 0) : x = 0 := by
  exact eq_zero_of_hasMat (_root_.GlobalTheory.Fam.pk_z W) W.Q.charW.base.models.jX gP t x hz
set_option maxHeartbeats 1000000 in
theorem eq_zero_of_isRes_pkAt_eq_zero : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) (x : (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → _root_.GlobalTheory.TopVal.packageAtPoint (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  intro hL p K q c b hw t φ x hx hz d
  have hx0 : x = 0 := _root_.GlobalTheory.TopVal.Inj.eq_zero_of_pkAt_eq_zero_uni (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b)
    (Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z).2.1 t x hz
  subst hx0
  obtain ⟨x, a, ax, y, -⟩ := hw
  have e : a.x = x := eq_of_heq ax
  subst e
  have h0 := eq_zero_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y →
      ∀ (s : k.P.T) (φ : Frm q.w.I (k.P.I.tup s)), IsRes φ (0 : k.P.A3.A.fam.amb.FR s) → φ = 0 := by
    intro k hk
    subst hk
    exact h0
  rw [key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t φ hx]
  rfl
end GlobalTheory.TopVal.Inj
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsJValSmul
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TopVal.Scalar
section Alg
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms Matrix GlobalTheory.CoefSpace
variable {ι : Type} [Fintype ι] {n : ℕ}
end Alg
section Group
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Forms Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.DefLift GlobalTheory.CoefSpace GlobalTheory.DefiniteMult Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}
end Group
end GlobalTheory.TopVal.Scalar
end
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.TopVal.exists_jVal_smul_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws} {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Formalism.L2.Forms.gramP (I.rec7 l Z) = 1 → ∀ (u : B.Word) (cv : GlobalTheory.TopVal.Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W), _root_.GlobalTheory.TopVal.ValEqvAlt W cv → cv ≠ 0 → ∀ j₀, GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j₀ → ∃ a : ℂ, a ≠ 0 ∧ _root_.GlobalTheory.TopVal.ValuationCompatible W cv (a • j₀) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u cv hcv h0 j₀ hJ
  have hm := W.Q.charW.base.models
  have hr := hJ.range
  rw [GlobalTheory.Core.Rk.Top.sgT_eq_perIn_sgT I l Z u I.mu0] at hr
  have e : (fun τ => ((GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  obtain ⟨a, ha, h⟩ := GlobalTheory.TopVal.Scalar.exists_scalar (D := I.rec7 l Z) (M := (_root_.GlobalTheory.Fam.pk_z W).MX) (θ := (_root_.GlobalTheory.Fam.pk_z W).θ) (c := (_root_.GlobalTheory.Fam.pk_z W).cX)
    (pr := (_root_.GlobalTheory.Fam.pk_z W).prX) hm.inf (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hm.cX hm.prX
    (Formalism.L2.Forms.rankP (I.rec7 l Z)) B.wts.sgTrue B.embLL B.fields.emb
    (fun τ x => DFunLike.congr_fun (B.fields_embC τ) x) cv hcv h0 _ _ _ e j₀ hJ.inj hr hJ.eqv
  refine ⟨a, ha, fun w v => (h w v).trans ?_⟩
  unfold GlobalTheory.TopVal.pairVal
  rw [LinearMap.smul_apply]
  erw [map_smul, map_smul, LinearMap.smul_apply]
  rfl
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsParamsAtMemStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameters_parameterChoice_nonempty : (∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧ AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧ ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt | exact _root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSelectionPairLocalLanglands
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
local macro:max "kq% " e:term:max : term => `((by kexactB $e))
noncomputable section
namespace GlobalTheory.Mem.R3.SelectionPairing
open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.IndefR.AutomorphicEvaluation
section Args
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}
end Args
set_option maxHeartbeats 1000000 in
theorem wp3_ne_bot_and_piece_at_of_multEq (hWR : GlobalTheory.Published.WeilRepresentationUnitaryPair) (hDSE : GlobalTheory.Published.DiscreteSeriesExists)
    (hHCF : GlobalTheory.Published.HarishChandraFinite) (hCRD : GlobalTheory.Published.CuspRapidDecay) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
    (q : WPt p.s K) (hMult : GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) :
    ∀ p', q.x.what₂.r.z.R.EEp3 p' ≠ ⊥ → ∀ i, q.x.what₂.r.z.R.Wp3 i p' ≠ ⊥ ∧
      ∀ v, v ≠ (famT q.x.what₂).A.v0 → q.x.what₂.r.z.R.PartAt q.x.what₂.r.z.F i p' v :=
  GlobalTheory.T.rowPart_forms_and_nonzero_vectors_every_place _ _ _ _ _ _ _ q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG
    (GlobalTheory.LinksInputs.inputs_of_hypotheses hWR hDSE hHCF hCRD _) q.x.what₂.r.z.pins q.x.what₂.r.intersectionNumber_baseChange hMult
    (GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.pins.char 1 q.x.what₂.r.intersectionNumber_baseChange.ok
      (fun k => ⟨_, q.core_data_of_point.a.all.types.O k, q.core_data_of_point.a.all.types.eSer_def k⟩)).1
set_option maxHeartbeats 1000000 in
theorem ev_at_join_pinned {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex) (hR : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R)
    (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (hsP : HEq sP q.saturationAtWeightedPoint.P) :
    EvalTieT (Formalism.L2.SG.RowsJoinPinned.MP q.x.what₂.r.z.R.toRealDat) q.x.what₂.r.z.R.toRealDat.ν0
      q.x.what₂.r.z.R.toRealDat.fd0 (Formalism.L2.SG.RowsJoinPinned.EP q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2) sP.X sP.G
      (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c := by
  have hF0 : (fun u => (R.T.cols.forms u).to0) = (fun u => (q.x.col.C.forms u).to0) := (by with_unfolding_all exact (congrArg (fun (C : type_of% q.x.col.C) u => (C.forms u).to0) hR.s.cols :))
  exact (by with_unfolding_all exact (pack_move (D := (q.w.st q.Z).toD7) (F0 := fun u => (R.T.cols.forms u).to0) (F0' := fun u => (q.x.col.C.forms u).to0)
    ((hF0)) (P := (sP)) (P' := (q.saturationAtWeightedPoint.P)) ((hsP))
    (fun _ P => EvalTieT (Formalism.L2.SG.RowsJoinPinned.MP q.x.what₂.r.z.R.toRealDat) q.x.what₂.r.z.R.toRealDat.ν0
      q.x.what₂.r.z.R.toRealDat.fd0 (Formalism.L2.SG.RowsJoinPinned.EP q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2) P.X P.G
      (Formalism.L2.SG.RowsJoinPinned.iotaX P.X P.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) ((q.saturationAtWeightedPoint.ev)) : _))
theorem nonempty_rXs_of_prmR_none {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {Γ : GeoP} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} (hp : p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ) {K : Ctx}
    (q : WPt p.s K) : Nonempty (RXs q.x.what₂) := by
  subst hp
  exact (by with_unfolding_all exact (Nonempty.intro q.x.rx :))
end GlobalTheory.Mem.R3.SelectionPairing
end
open GlobalTheory.Mem.R3.SelectionPairing in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.R3.SelectionPairing.exists_selection_pair_local_langlands_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (Del h0 : ℕ) (c : ℝ) (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK), ∃ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x ∧ ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns R.T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS ∧ x.F.Zsc = GlobalTheory.Fc.zsc (divisionPairOfAdelicFormsFaceColumnsData x) Del h0 c ∧ HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := (sS.toRealSpectralMatching R).X) (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) (sS.toRealSpectralMatching R).Y.hK (sS.toRealSpectralMatching R).G x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt (sS.toRealSpectralMatching R) hin (x.wd m)) x.bR) ∧ ∃ (κ : ℝ) (sEEc : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX (sS.toRealSpectralMatching R).X)), HEq x.sEE sEEc ∧ 0 < κ ∧ ∀ (v : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))), sEEc v = Tw.mk (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (((1 : ℂ) * (κ : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) (sS.toRealSpectralMatching R).X (sS.toRealSpectralMatching R).G (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) ⟨x.R.HE.e (Tw.out v), hx⟩) ∧ RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2 := by
  intro hDS hHC hCW hWR hDSE hHCF hCRD hGAR hRay hL N Γ p hp hNEb K q hHost hMult R hR sP sS hsP hsS Del h0 c hin
  have hRX : Nonempty (RXs q.x.what₂) := _root_.GlobalTheory.Mem.R3.SelectionPairing.nonempty_rXs_of_prmR_none hp q
  have h := _root_.GlobalTheory.T.exists_square_integrable_columns_of_heq_data _ K q R.T.ker hR.k hRX
  refine h.elim fun Dc h => h.elim fun Sp₀ h => h.elim fun Zsc₀ h => h.elim fun C₀ hC => ?_
  have hcore := selection_group_ambient_tie (K := K) (w := q.w) (Z := q.Z) (Wt := q.x.Wt) (ex := q.O.ex) (t := q.x.what₂)
    ⟨hDS, hHC, hCW, hHCF, hCRD⟩ ((by with_unfolding_all exact (q.x.obj.amb :))) ((by with_unfolding_all exact (q.x.obj.mjH :))) ((by with_unfolding_all exact (q.core_data_of_point.row.grp :)))
    ((by with_unfolding_all exact ((_root_.GlobalTheory.Mem.R3.SelectionPairing.wp3_ne_bot_and_piece_at_of_multEq hWR hDSE hHCF hCRD q hMult) :))) Dc Sp₀ Zsc₀ ((by with_unfolding_all exact (C₀ :))) (sS.toRealSpectralMatching R).X ((by with_unfolding_all exact ((sS.toRealSpectralMatching R).Y.hK :)))
    ((by with_unfolding_all exact ((sS.toRealSpectralMatching R).G :))) ((by with_unfolding_all exact ((_root_.Formalism.IndefR.pwOf_alt (sS.toRealSpectralMatching R) hin) :)))
    ((by with_unfolding_all exact ((Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv :))) ((by with_unfolding_all exact (q.saturationAtWeightedPoint.t :))) q.saturationAtWeightedPoint.c q.saturationAtWeightedPoint.c_pos
    ((by with_unfolding_all exact ((_root_.GlobalTheory.Mem.R3.SelectionPairing.ev_at_join_pinned q R hR sP hsP) :))) q.O.L Del h0 c
  refine hcore.elim fun a h => h.elim fun x h => ?_
  have hc := hC R.T rfl a x h.1 ((by with_unfolding_all exact (h.2.1 :))) ((by with_unfolding_all exact (h.2.2.1 :))) ((by with_unfolding_all exact (h.2.2.2.1 :)))
  refine hc.elim fun C c' => ?_
  refine Exists.intro a (Exists.intro x (And.intro h.1 (Exists.intro C (And.intro c'.1 (And.intro c'.2.1 (And.intro c'.2.2.1
    (And.intro c'.2.2.2.1 (And.intro c'.2.2.2.2 (And.intro ?_ (And.intro ?_ ?_))))))))))
  · exact (by with_unfolding_all exact (h.2.2.2.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.2.2.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.2.2.2.2 :))
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeriesStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLe_of_cuspRapidDecay_artin_rayClassField : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field | exact _root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field | (intros; apply _root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTied
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.RealOfReading
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie
theorem exists_linked_data_of_agreement {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) {cf : CharFrame D} {nch : NChoice D}
    {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp) (hcf : P.cf = cf) (hC : P.C = nch) (htp : HEq P.tp tp)
    {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (hM : P.M = M) (hrep : HEq P.rep rep)
    (ag : GlobalTheory.NJoin.Agree X M rep) (e0 : GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X) :
    ∃ T : _root_.GlobalTheory.NRows.LinkedData hL D, T.P = P ∧ HEq T.X.R X.R := by
  subst hcf
  subst hC
  cases eq_of_heq htp
  subst hM
  cases eq_of_heq hrep
  exact ⟨⟨P, X, ag, e0⟩, rfl, HEq.rfl⟩
end GlobalTheory.HeightCounting.Up.RealOfReading
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GermFactorizationUnitMulEvaluation
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
theorem germ_eq_unit_mul_evaluation_ideal_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : space TF.X Z Y.U la) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) = algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) := by
  intro _ h2 _ _
  refine h2.imp fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, -⟩ := h
  exact ⟨C, hC, x0, fun x hx' hle ι p hp i hi Y hY Z TF la w y T io y' g _ hpt j' hj' =>
    germ_eq_unit_mul_evI_core TF.X Z Y.U la w y T io y' g hpt j' hj'⟩
end GlobalTheory.HSApp
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_local_hom_germ_factorization : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : space TF.X Z Y.U la) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) = algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) := by
  first | exact @_root_.GlobalTheory.HSApp.germ_eq_unit_mul_evaluation_ideal_alt | exact _root_.GlobalTheory.HSApp.germ_eq_unit_mul_evaluation_ideal_alt | (intros; apply _root_.GlobalTheory.HSApp.germ_eq_unit_mul_evaluation_ideal_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodGenericRowsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_parameter_of_reciprocity_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; ∀ χ ∈ a.x.A3.A.X, chiIdem χ * lvlIdem a.x.F.P0 a.x.F.ψ0 ≠ 0 := by
  first | exact @_root_.GlobalTheory.Mem.R3.GenRows.goodGeneric_rows_alt | exact _root_.GlobalTheory.Mem.R3.GenRows.goodGeneric_rows_alt | (intros; apply _root_.GlobalTheory.Mem.R3.GenRows.goodGeneric_rows_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermWCellLastMulMulVecEqOfInWbStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedAt_hPA_prmR : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition := by
  first | exact @_root_.GlobalTheory.Fc.RL.PrimAt.linkedAt_hPA | exact _root_.GlobalTheory.Fc.RL.PrimAt.linkedAt_hPA | (intros; apply _root_.GlobalTheory.Fc.RL.PrimAt.linkedAt_hPA <;> assumption)
end
end

