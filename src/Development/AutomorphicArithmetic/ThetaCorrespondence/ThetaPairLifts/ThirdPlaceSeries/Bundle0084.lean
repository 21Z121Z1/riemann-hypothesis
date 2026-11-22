import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0498
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0075
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0178
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0479
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0097
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RdMemKOOffTwist
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
theorem GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ j hj t₀ J₀ hJ₀ α₀ t J _ i _
  have hjm : j ≤ B.R.m := by omega
  obtain ⟨ε, hε, hε'⟩ := (J.G i).q.above
  have und : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.G i).q.v :=
    GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hε'
  have hv := (GlobalTheory.Mem.Col2.TC.underQ_notMem I hW.tr.ok l u (W.P.I.tup t) (J.G i).q.v
    ⟨J.pl i, (hW.tq.Q t _).1 (J.mem i), und⟩).1
  have hlb := (hJ₀.is.reads j hjm).lb (J₀.ι j α₀)
  have hfr : ∀ e : j = (J.G i).s + 1, ∃ pos, IsStdFr pos (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e) := by
    intro e
    subst e
    exact ⟨_, (ha.stdQ _ _).1 _ _⟩
  obtain ⟨pos, hpos⟩ := hfr (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)
  have key : ∀ g ∈ J₀.A.U j (J₀.ι j α₀),
      GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) g ∈ KO (J.G i).k _ := by
    refine GlobalTheory.LevProd.OffTwist.locHom_mem_KO (J.G i).q _ (rankN (I.rec7 l Z) j hjm) _ hpos (B.T u) hv
      (J₀.A.K j hjm (J₀.ι j α₀)).lev.Lb (fun x hx r => ?_) (fun s => ?_) (σ := sigD _) (J := gramN (I.rec7 l Z) j hjm) _ (fun g hg => ?_)
    · obtain ⟨c, hc, -⟩ := (hlb x).1 hx r
      exact ⟨c, hc⟩
    · refine (hlb _).2 fun r => ?_
      by_cases h : r = s
      · subst h
        refine ⟨(B.T u : ℕ), (Pi.single_eq_same _ _).trans (map_natCast (algebraMap (𝓞 B.host.E) B.host.E) _).symm, fun _ => ⟨_, (l.pr.piT_norm u).symm⟩⟩
      · exact ⟨0, (Pi.single_eq_of_ne h _).trans (map_zero (algebraMap (𝓞 B.host.E) B.host.E)).symm, fun _ => dvd_zero _⟩
    · obtain ⟨κ, hκ⟩ := ((hJ₀.is.U j hjm _ g).1 hg).2
      exact ⟨κ.1, hκ, (J₀.A.K j hjm (J₀.ι j α₀)).lev.Uloc_lev _
        ((((J₀.A.K j hjm (J₀.ι j α₀)).lev.U_eq κ.1).1 κ.2).2 _)⟩
  intro g hg
  exact (GlobalTheory.PenBridge.toSum0_mem_KO_iff _).2 (key g hg)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.BigOn.Exp.TupLe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def AllPtsAlt (Q : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}, PtAt ex Csz → Fin D.R.m → Prop) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts)
    (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz) (j : Fin D.R.m), p.PointConditions' → More p → Q p j
open Classical in
def PlacesCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ ex _} p j => ∀ w : D.what₂.places.Pl, D.plEq w ∈ p.R.twPl →
  IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w) →
  ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ →
  ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w) →
  p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
    (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi →
  SplitSet (p.R.Q (p.R.mu (D.plEq w))) ∧
    (∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) ∧
    idem (p.R.Q (p.R.mu (D.plEq w))) + cA D (idem (p.R.Q (p.R.mu (D.plEq w)))) =
      idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q) +
        cA D (idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q))
open Classical in
def FlatCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)) (ψ : Twist D Circle) (t : p.P.T),
  B.Good → BaseOf (R2 p) j B → ψ.Good → B.admitted ψ.Q → (R2 p).xi t = B.de.chi * ψ.chi →
  idem ((R2 p).Q t) + cA D (idem ((R2 p).Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) →
  ∃ (z : GA D (Vc D j)) (c : ℂ), SuppAt (idem ((R2 p).Q t)) (Vc D j) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime (R2 p) t) c ∧
    (princ B).vecFlat ψ = c • (R2 p).ωP j t (z⁻¹, 1) ((R2 p).vP j t)
def TraceCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (ρ : Setup D.ntw), ρ.Good → RealPin p.R p.cG ρ → ρ.LevelOf D.nexp →
  ∀ (i : D.ntw.Tw) (b : Bool) (ψ : Twist D Circle) (ω : PairRep (Vc D j) (Wc D j)), ψ.Good → (ρ.B i j b).admitted ψ.Q →
    (ρ.B i j b).IsWeil ψ.chi ω → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (series (ρ.B i j b).F ω ((princ (ρ.B i j b)).vecFlat ψ) h P) =
        series (ρ.B i j b).F ω ((ρ.B i j b).vecFlat ψ) h P
def CoefficientCondition' : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ c : ℂ, c ≠ 0 → IsScale p.R p.v₀ B c → ∀ u : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ,
    (∀ τ, (u τ : ((R2 p).MW j (sg0 D p.P.A3.A)).sm τ) = p.v₀ j _ τ) → ∀ O' : Subring ℂ, IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ h ∈ GfC (Vc D j), ∀ v, InCoefLat (R2 p) j h v →
      ∃ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h), (R2 p).ioP j (PiTensorProduct.tprod ℂ u) v = c • P
def SmallnessCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ O O' : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ (h : GA D (Vc D j)), ∀ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h),
      P ∈ Submodule.span O' (B.coefLat (embLL0 D) (labLL0 D) O (finPt (Vc D j) h) : Set (PolF D (Wc D j).rank (Vc D j).rank))
section Units
variable {O K : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
end Units
section Read
variable {D : D7} {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)
  {L : Type} [Field L] [Algebra (D.ntw.O i) L] (e : L →+* ℂ) (he : ∀ c : D.ntw.O i, e (algebraMap _ L c) = ρ.eO i b c)
end Read
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
variable {p w j}
end Point
section Move
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
include hρ
end Move
section Assembly
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem realTw_le_alt (s1 : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition) (s2 : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition) (s3 : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition) (s4 : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition') (s5 : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition) (hr : p.PointConditions') (hm : More p)
    (hL : Links2 p) (hw : D.plEq w ∈ p.R.twPl)
    (hok : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin p.R p.cG ρ) (hlev : ρ.LevelOf D.nexp)
    (hB0 : BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)))
    (e : FractionRing (ex.nch.Oe w) →+* ℂ) (h1 : ∀ x, e (ex.nch.embW w x) = D.what₂.embLL x)
    (h2 : ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a)
    (c1 : ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w))
    (c2 : p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi)
    {ν : ℂ} (hν : IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν) (hR : RatAt p w j hρ ν) {rd : Can p w j} (hc : IsCan p rd) :
    realTw p rd ≤ twLat p w j hρ ν := by
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hK := GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.isKsForm_of_iso (p.nexp.fi j) (p.fw.ks j)
  obtain ⟨Z⟩ := hm.2.2.series
  have hF : Faithful (rdAt p w j hρ ν) := realRd_faithful _ _ _ _ _ _ _ _ _ _ p.nexp p.v₀ ρ hρ _ j _ ν hν.1 hL.2.2.1
    p.charW.base.models.HW (Z.vec j) hK
  obtain ⟨p1, p2, p3⟩ := s1 _ _ _ _ _ _ _ _ _ _ p j hr hm w hw hok ρ hρ hpin c1 c2
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  have hB := hρ.base (ex.nch.twI w) j (ex.nch.sd w)
  obtain ⟨z, cz, hz, hcz, hfl⟩ := s2 _ _ _ _ _ _ _ _ _ _ p j hr hm _ _ ((R2 p).mu (D.plEq w)) hB hB0 ht hadm c2 p3
  have hzf : z ∈ GfC (Vc D j) := GlobalTheory.TwTraceCx.mem_GfC_of_suppAt p1 hz
  have hω : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).IsWeil
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi
      ((R2 p).ωP j ((R2 p).mu (D.plEq w))) := by
    have e0 : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).mu *
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi =
        (R2 p).toLevCh.mu ((R2 p).mu (D.plEq w)) ((j : ℕ) + 1) := by
      rw [Base.mu, hB0.mu0, mul_assoc, ← c2]
      rfl
    rw [Base.IsWeil, e0, hB0.ψ, hB0.eta]
    exact hC.thP.ωP j _
  have hN : IsUnit ((GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w)) : ℕ) : ex.nch.Oe w) := by
    have hcop : Nat.Coprime (D.ntw.l (ex.nch.twI w)) (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
      have := GlobalTheory.NormUnit.coprime_absNorm _ (D.ntw.lPrime _).out P (p2 P hP)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    simpa using (GlobalTheory.NormUnit.isUnit_natCast_of_coprime (D.ntw.O_l _) hcop).map (algebraMap _ (ex.nch.Oe w))
  have hO' : IsCoefRing D.what₂.embLL (labLL D) (imO ex.nch w e) := by
    refine ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => ?_⟩
    obtain ⟨b, hb⟩ := mem_of_ringOfIntegers (O := ex.nch.Oe w) (ex.nch.embW w) a
    exact ⟨b, by rw [RingHom.comp_apply, hb, h1]⟩
  obtain ⟨ν0, c, hs, n, hn, hνc⟩ := hν
  rw [p.phsOne j, map_one, one_mul] at hνc
  have c0 : c ≠ 0 := fun h => ν0 (by rw [h, zero_pow hn] at hνc; exact pow_eq_zero_iff hn |>.1 hνc)
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hs
  refine le_of_comb hρ hc hR hF hK e h1 h2 hN ?_
  rintro x ⟨h, hh, v, hv, hx⟩
  obtain ⟨P, hP, hio⟩ := s4 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 c c0 hs u hu _ hO' h hh v hv
  have hP' := s5 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 _ _ (hρ.isCoefRing (ex.nch.twI w) (ex.nch.sd w)) hO' h P hP
  have hhz : h * z ∈ GfC (Vc D j) := mul_mem hh hzf
  refine ⟨ν⁻¹ * c * cz⁻¹, unitOff_mul (unitOff_root hn ?_) (unitOff_inv hcz),
    series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
      ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).vecFlat
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hνc, inv_mul_cancel₀ (pow_ne_zero _ c0)]
  · clear hP hio
    induction hP' using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨s, h', P', hd, g, hg, a, ea⟩ := series_eq_gen hρ _ j _ hok hω hhz (lat_translate_of_prime hρ _ j _ p1 p2 hz hQ)
      rw [ea]
      exact Submodule.smul_mem _ (⟨_, ⟨algebraMap _ _ a, h2 a⟩⟩ : imO ex.nch w e) (Submodule.subset_span ⟨s, h', P', hd, hg⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
    | smul a y _ hy =>
      rw [show a • y = (a : ℂ) • y from rfl, map_smul]
      exact Submodule.smul_mem _ a hy
  · have e1 : adForm (R2 p) j x (p.v₀ j _) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
        (ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v) :=
      ((congrArg (adForm (R2 p) j x) (funext hu)).symm.trans (hx u)).trans (one_smul _ _)
    have e2 : ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v = (c * cz⁻¹) •
        series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
          ((princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecFlat
            (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P := by
      rw [mul_comm, mul_smul, ← map_smul, ← hio]
      refine Eq.trans ?_ (congrArg (cz⁻¹ • ·) (hB0.series_eq_ser _ _ u (h * z) v)).symm
      rw [hfl]
      funext g
      have e3 := GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class _ _ _ _ _ _ (R2 p) _ hC j ((R2 p).mu (D.plEq w)) z⁻¹ cz (inv_mem hzf) u (h * z) v g
      rw [mul_inv_cancel_right] at e3
      refine Eq.trans ?_ (congrArg (cz⁻¹ * ·) e3).symm
      exact (inv_mul_cancel_left₀ hcz.1 _).symm
    rw [e1, e2, map_smul, s3 _ _ _ _ _ _ _ _ _ _ p j hr hm ρ hρ hpin hlev _ _ _ _ ht hadm hω, smul_smul, mul_assoc]
end Assembly
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHTuCTmin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc
theorem row_hTu_cTmin_alt : (∀ D, MassRatioUnderVolume D) → (∀ D, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2) → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    Row Q Lk fun 𝒜 _ => R1.H_hTu (fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y) 𝒜 := by
  intro hU hG Q Lk
  refine Row.of_sel fun 𝒜 σ s => ?_
  refine Closed.of_class fun Fm _ h hle => ?_
  obtain ⟨κ, -, -, t⟩ := s Fm h.1.1.1
  have tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie := ⟨0, fun x _ hx i =>
    volTie_of_realTied _ (built_val _ _ _ _ _ _ _ _ (t x hx i).1).2.2.2.2.2.2.1.some⟩
  exact StandardLattice.HarishChandraReduction.tuSize_min Fm hle
    (family_property_mono tVol fun D hT => GenusMassVolumes.volume_eq_mass_rank_two D (StandardLattice.volumeMass_of_unfolding D (hU D hT)) (GenusMassVolumes.volume_mass_of_genus_rank D 2 hT (hG D)))
    (Formalism.MainNotions.GappedMultiplicityBounds.explicit_bound_family Fm)
end GlobalTheory.Fc
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowZero
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.Fam.TopLoc.LocalIdempotentDensity
open GlobalTheory.SymBridge Formalism.L2.Col
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
def levelZeroCharacter (hstd : Formalism.L2.Theta.IsStdChar (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ (-1)) (g : Geo (I.rec7 l Z)) (t : W.P.T) :
    RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g t where
  vP := fun _ => 0
  vT := fun _ _ => 0
  sBF := fun _ _ _ => Classical.choice (GlobalTheory.Unf.Inhab.nonempty_stepBF hstd _ _)
  sFB := fun _ _ _ => Classical.choice (GlobalTheory.Unf.Inhab.nonempty_stepFB hstd _ _)
  io := fun _ => 0
  ioT := fun _ _ => 0
theorem isIdemAt_G_pl (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (ha : a.Is) (n : Fin a.n) :
    Formalism.L2.NTheta.IsIdemAt (a.G n).q.e (a.pl n).1 :=
  ((ha.tie (fun t => _root_.GlobalTheory.Fam.TopLoc.LocalIdempotentDensity.levelZeroCharacter W.Q.stdChar a.g t) (fun t => _root_.GlobalTheory.Fam.trivialColumnChoice t)).2.idem n).1
end GlobalTheory.Fam.TopLoc.LocalIdempotentDensity
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def SizeAtAlt : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows (Fm.L x i)
def SettingAtPoint : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i p =>
  GlobalTheory.GLq.ESerTie (Fm.D x i) → HidaSetting (Fm.L x i) p.R.toRealDat p.F.lv2
def CharacterAtPoint (Q : ChP) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p =>
  ∀ (G : Grid p CF) (W : G.Weil) (n : ℕ) (a : SlopeTestRemainingChoices p G W n), a.OK → Q a.ch
theorem SettingAtPoint.atPt (h : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint) {Q : ChP} (hQ : Big Q) : _root_.GlobalTheory.BigTop.Fun.CharacterAtPoint Q := by
  obtain ⟨c, hQ⟩ := hQ
  refine ⟨c, fun CF hCF => h.imp fun {eps} Fm _ _ a => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hQ eps CF hCF
  obtain ⟨x₁, a⟩ := a
  refine ⟨max x₀ x₁, fun x hx hle i p hp G W n b hb => ?_⟩
  exact hx₀ _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _
    (a x hx (le_of_max_le_right hle) i p hp hb.eser) b.ch hb.is b.atScale
end GlobalTheory.BigTop.Fun
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareStOfShareWSt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.ShareOn.Comparison₂
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Tied
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
local instance  (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst
variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst}
variable {P : Type} [Group P] [Finite P]
end Tied
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.ShareOn.Comparison₂
namespace GlobalTheory.ShareOn
theorem shareSt_of_shareWSt_alt : _root_.GlobalTheory.ShareOn.SharedWeightStatement → _root_.GlobalTheory.BigOn.ShareStatement := by
  intro h
  unfold _root_.GlobalTheory.ShareOn.SharedWeightStatement _root_.GlobalTheory.BigOn.ForallTwoRuns _root_.GlobalTheory.BigOn.AtPtsAlt at h
  unfold _root_.GlobalTheory.BigOn.ShareStatement _root_.GlobalTheory.BigOn.ForallRecordObjects
  refine Closed.imp h fun Fm CH _ H => ⟨0, fun c _ _ => ?_⟩
  obtain ⟨x0, hx0⟩ := H
  exact ⟨x0, fun x hx hle i p hp hm r O hR =>
    Comparison₂.leafShareI_of_shareW p hR (hx0 x hx hle i p hp hm r hR.1.ok hR.2)⟩
end GlobalTheory.ShareOn
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWChr
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.PlugPt.side_weight_psi_values_tame_tie : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Formalism.L2.Host.PsiChoiceCompatible (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf p.O.ex.nch (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp ∧ (∀ v, (p.w.D p.Z).what₂.muAt v ≠ (p.w.D p.Z).what₂.mu0 → ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp.psi v).ValuesIn 0 (p.w.D p.Z).what₂.embLL) ∧ GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf.W.om := by
  intro hL 𝒮 ν K p
  refine ⟨p.x.n.chrPsi, ?_, ?_⟩
  · intro v _
    show (p.x.n.tp.psi v).ValuesIn 0 _
    rw [p.x.n.psi]
    exact GlobalTheory.twDat_psi_valuesIn_LL p.B p.T p.x.coh v
  · have h := p.x.what₂.grp
    have hf := (GlobalTheory.Plug.wPt_frame 𝒮 K p).2.1
    show GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z).W.om
    rw [hf]
    exact types_of_true (D := p.w.D p.Z) _ h
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ExpFrame
open Formalism.CohomologicalDescent.DepthNonnegative
section Tests
variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O)
local instance  : Ring (alg O N lam) := Subalgebra.toRing _
end Tests
end GlobalTheory.ExpFrame
end
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)
open GlobalTheory.ExpFrame
namespace GlobalTheory.ExpTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
def InRangeAlt (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i) (_ : Fin (Fm.D x i).R.m) (_ : Par)
    (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → Q Fm x hx i p j P W w
def FrameStatement' : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => FrameAt p j P W w
def GaloisStatement : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => GalAt p j P W w
def SmallnessCondition : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w
end GlobalTheory.ExpTie
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLiftsBijectiveBaseStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l_unif_base_links_rank_of_pt_split : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → (R2 p).LUnif ∧ BaseLinks (R2 p) (F2 p) ∧ RankRows (S2 p) := by
  first | exact @_root_.GlobalTheory.BigOn.SplitRows.uniform_and_base_links_and_rank_of_split_data | exact _root_.GlobalTheory.BigOn.SplitRows.uniform_and_base_links_and_rank_of_split_data | (intros; apply _root_.GlobalTheory.BigOn.SplitRows.uniform_and_base_links_and_rank_of_split_data <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumExpStAltAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SumExpAt
end GlobalTheory.SumExpAt
namespace GlobalTheory.SumExpAt
end GlobalTheory.SumExpAt
namespace GlobalTheory.ExpTie
open GlobalTheory.SumExpAt
open Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
theorem sumExpSt_alt : _root_.GlobalTheory.ExpTie.ExponentSumStatement :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun _ _ _ p _ _ j P W hD _ t w => lIncl_sumExp p j P W hD t w⟩⟩
end GlobalTheory.ExpTie
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieRatOf
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem tieRat_of_alt (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hR : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace) : _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  unfold _root_.GlobalTheory.BigOn.Exp.CompatibilityRational _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hA hR).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j Z => ?_⟩
  obtain ⟨hA', hR'⟩ := hx0 x hx hle i p hp
  have hrow := hR' hm w hw j Z.ρ Z.good Z.pin (levelOf_exportTie Z)
  have hs := Z.scalar ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hrat := hs.rat hrow
  obtain ⟨ν, hn, -⟩ := hrow
  obtain ⟨hok, hcl, -⟩ := hA' hm w hw j
  exact ⟨hs.norm ⟨ν, hn⟩, hrat.1, fun s h P hd => hrat.2.1 _ _ _ hok hcl s h P hd⟩
end GlobalTheory.BigOn.Exp
end
end

