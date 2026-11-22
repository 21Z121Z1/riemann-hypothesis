import Mathlib
import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0006
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Formalism.LocalToGlobal.Divisibility.RecBridgeSel
import Formalism.LocalToGlobal.Divisibility.Bundle0005
import Formalism.LocalToGlobal.GroupLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace GlobalTheory.Fc

open GlobalTheory.Cp

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Hyps (N : FamClass → Prop) (DR : R1.DefT) : Type 1 where
  𝒜 : FamClass
  σ : RawSel Bundle 𝒜
  cT : ℝ → ℝ → ℝ
  hEx : MinkDiv → UpperTheory.Top.ExS 𝒜 cT
  hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm
  hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.IndefR.RowsB ((selB σ) Fm hc x hx h i)
  hTw : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.TieTwRec (Fm.L x i) ((selP σ) Fm hc x hx h i).1.S0.Tw
  hPA : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel σ Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.IndefR.Links.PrimRows3 (selB σ Fm hc x hx h i).Q.Rl (selB σ Fm hc x hx h i).Q.F ∧ (selP σ Fm hc x hx h i).1.A3.fam3.TypesSep3
  hLamP : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.Rows.RowsHoldLam3 ((selP σ) Fm hc x hx h i).1
  hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3G ((selP σ) Fm hc x hx h i).1
  hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      DcPtG ((selP σ) Fm hc x hx h i).1
  hTu : Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm
  hn4 : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev
  hLit : LitThin
  hWu : Formalism.L2.SG.Pf.WuDecayOfGap
  hRF : Formalism.L2.SG.RowsDef.RowsFinDim
  hTF : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3
  c30 : List ℝ → Formalism.MainNotions.S.CountingConstants
  hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A
  sTy : Formalism.L2.SG.RowsPos.TypeP
  sNG : Formalism.L2.SG.RowsPos.RowNGP
  sM : Formalism.L2.SG.RowsPos.RowMainEqP
  sLp : Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨((sel σ) Fm (d3_a hc)).1, fun x hx h i => ((selS σ) Fm (d3_a hc) x hx h i).toSTies⟩)
  sO : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨((sel σ) Fm (d3_a hc)).1, fun x hx h i => ((selS σ) Fm (d3_a hc) x hx h i).toSTies⟩
  h30 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb
  hInstR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank
  selJ : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel σ Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.SG.JoinSI.JoinSI (R := (sel σ Fm hc).2 x hx h i) (S := selS σ Fm hc x hx h i) (Q := (selB σ Fm hc x hx h i).Q)
  jOn : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ((Fm.D x i).what₂.V0 (Fm.D x i).what₂.mu0).map ((Fm.D x i).what₂.iota (Fm.D x i).what₂.mu0) = ⊤
  hMt : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (μ : (Fm.D x i).what₂.Tup) (a : NumberField.RingOfIntegers (Fm.D x i).what₂.LL),
      ∀ y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier, (Fm.D x i).what₂.embLL (a : (Fm.D x i).what₂.LL) • y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier
  rRows : R1.H_rRows DR 𝒜 σ
  aPt0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u
  aPtTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw
  aPer0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)
  aPerTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw
  aP10 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u
  aAtG : Closed (D3 3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1
  aC2 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm
  hServ : ServT (D3 3 𝒜) fun Fm hc => (sel σ) Fm (d3_a hc)
  cIc : ℝ
  hcI : 0 < cIc
  irrC : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f)
  zL : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : ((sel σ) Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) ((selP σ) Fm (d3_a hc) x hx h i).1.A3.A ((selP σ) Fm (d3_a hc) x hx h i).1.P0
          ((selP σ) Fm (d3_a hc) x hx h i).1.ψ0 (((selP σ) Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 ((selP σ) Fm (d3_a hc) x hx h i).1.Zs) k
          ((selP σ) Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec
  tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm
  hU : ∀ D, MassRatioUnderVolume D
  hG : ∀ D, GenusMassVolumes.GenusMassAt D 2
  nRest : N (D3 3 𝒜)

end GlobalTheory.Fc

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Cp

open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Rows

section Col

variable {X : Formalism.L2.Col.Fields} {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 X.K G Pl0 I0 Ty T m} {P1 : Subgroup G} {ψ1 : P1 →* X.Kˣ}

@[reducible] def ColRec3.toS (c : GlobalTheory.Cp.ColRec3 X A3 P1 ψ1) : Formalism.L2.DIV.ColRec3 X A3 P1 ψ1 where
  Pr := c.Pr
  Rk := c.Rk
  W := c.W
  Ch := c.Ch
  sel := c.sel
  Sg := c.Sg
  hX := c.hX
  Lv := c.Lv
  Xg := c.Xg
  m2 := c.m2
  Gc := c.Gc
  mu := c.mu
  cst := c.cst
  Li := c.Li
  hL := c.hL
  hP := c.hP
  Mem := c.Mem
  wd := c.wd
  b := c.b
  hY := c.hY
  Am := c.Am
  hK := c.hK
  hF := c.hF
  hE := c.hE
  ev := c.ev

@[reducible] def ColRec3.ofS (c : Formalism.L2.DIV.ColRec3 X A3 P1 ψ1) : GlobalTheory.Cp.ColRec3 X A3 P1 ψ1 where
  Pr := c.Pr
  Rk := c.Rk
  W := c.W
  Ch := c.Ch
  sel := c.sel
  Sg := c.Sg
  hX := c.hX
  Lv := c.Lv
  Xg := c.Xg
  m2 := c.m2
  Gc := c.Gc
  mu := c.mu
  cst := c.cst
  Li := c.Li
  hL := c.hL
  hP := c.hP
  Mem := c.Mem
  wd := c.wd
  b := c.b
  hY := c.hY
  Am := c.Am
  hK := c.hK
  hF := c.hF
  hE := c.hE
  ev := c.ev

end Col

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

@[reducible] def SquareIntegrableColumnsCompatible.toS {T : TiedDataSK ex} {P : RowSideFamily ex} (K : GlobalTheory.Cp.SquareIntegrableColumnsCompatible T P) : Formalism.L2.DIV.SquareIntegrableColumnsCompatible T P where
  X := K.X
  e := K.e
  c := K.c.toS
  Sp := K.Sp
  colTie := K.colTie
  kerTie := K.kerTie
  wTie := K.wTie
  lvTie := K.lvTie
  sgTie := K.sgTie
  v0 := K.v0
  TU := K.TU
  xiVal := K.xiVal
  trIv := K.trIv
  famEq := K.famEq
  gEq := K.gEq
  plEq := K.plEq
  i0Eq := K.i0Eq
  tEq := K.tEq
  muTie := K.muTie
  ok1 := K.ok1

@[reducible] def SquareIntegrableColumnsCompatible.ofS {T : TiedDataSK ex} {P : RowSideFamily ex} (K : Formalism.L2.DIV.SquareIntegrableColumnsCompatible T P) : GlobalTheory.Cp.SquareIntegrableColumnsCompatible T P where
  X := K.X
  e := K.e
  c := ColRec3.ofS K.c
  Sp := K.Sp
  colTie := K.colTie
  kerTie := K.kerTie
  wTie := K.wTie
  lvTie := K.lvTie
  sgTie := K.sgTie
  v0 := K.v0
  TU := K.TU
  xiVal := K.xiVal
  trIv := K.trIv
  famEq := K.famEq
  gEq := K.gEq
  plEq := K.plEq
  i0Eq := K.i0Eq
  tEq := K.tEq
  muTie := K.muTie
  ok1 := K.ok1

theorem divRows3G_iff (P : RowSideFamily ex) : GlobalTheory.Cp.DivRows3G P ↔ Formalism.L2.DIV.DivRows3G P :=
  ⟨fun h => ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩,
    fun h => ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩⟩

theorem servT_iff (𝒞 : FamClass) (sel : Formalism.L2.TSel 𝒞) : GlobalTheory.Cp.ServT 𝒞 sel ↔ Formalism.L2.G.ServT.ServT 𝒞 sel :=
  ⟨fun h => ⟨h.twU, h.pdv⟩, fun h => ⟨h.twU, h.pdv⟩⟩

end GlobalTheory.Cp

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.AllBundlePointProperties

open GlobalTheory.Fc

def LevelPrimeColumnValuationsClosed (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u

def LevelPrimeColumnValuationsAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => LevelPrimeColumnValuationsClosed 𝒜

def H_aAtG (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1

def ArithmeticConditionAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aAtG 𝒜

structure All (𝒜 : FamClass) : Prop where
  aP10 : LevelPrimeColumnValuationsClosed 𝒜
  aAtG : H_aAtG 𝒜

theorem row_all {Bd : BdT} {Q : V4.Slot} {Lk : LkT Bd}
    (aP10 : LevelPrimeColumnValuationsAtBundlePoints Q Lk) (aAtG : ArithmeticConditionAtBundlePoints Q Lk) :
    Row Q Lk fun 𝒜 _ => All 𝒜 :=
  Row.imp (Row.and aP10 aAtG)
    fun _ _ _ ⟨a0, a1⟩ => ⟨a0, a1⟩

theorem row_of_all {Bd : BdT} {Q : V4.Slot} {Lk : LkT Bd} (h : Row Q Lk fun 𝒜 _ => All 𝒜) :
    LevelPrimeColumnValuationsAtBundlePoints Q Lk ∧ ArithmeticConditionAtBundlePoints Q Lk :=
  ⟨Row.imp h fun _ _ _ t => t.aP10, Row.imp h fun _ _ _ t => t.aAtG⟩

example (𝒜 : FamClass) : LevelPrimeColumnValuationsClosed 𝒜 ↔
    EvC (fun D O => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT O.X O.ex.tw u) 𝒜 := Iff.rfl

example {Bd : BdT} {Q : V4.Slot} (Lk : LkT Bd) (h : Row0 Q LevelPrimeColumnValuationsClosed) (h' : Row0 Q H_aAtG) : LevelPrimeColumnValuationsAtBundlePoints Q Lk ∧ ArithmeticConditionAtBundlePoints Q Lk :=
  ⟨h.row Lk, h'.row Lk⟩

end GlobalTheory.Fc.AllBundlePointProperties

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

open GlobalTheory.Fc

def ReferenceChainEvaluationAdmissible (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u

def ReferenceChainEvaluationAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ReferenceChainEvaluationAdmissible 𝒜

def H_aPtTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw

def TwistedPointAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPtTw 𝒜

def H_aPer0 (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)

def PeriodAtZeroAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPer0 𝒜

def H_aPerTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

def TwistedPeriodAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPerTw 𝒜

def H_tie (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.RealPlaceSecondLayerConditions Fm

def Row_tie {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_tie 𝒜

structure All (𝒜 : FamClass) : Prop where
  aPt0 : ReferenceChainEvaluationAdmissible 𝒜
  aPtTw : H_aPtTw 𝒜
  aPer0 : H_aPer0 𝒜
  aPerTw : H_aPerTw 𝒜
  tie : H_tie 𝒜

theorem row_all {Bd : BdT} {Q : V4.Slot} {Lk : LkT Bd}
    (aPt0 : ReferenceChainEvaluationAtBundlePoints Q Lk) (aPtTw : TwistedPointAtBundlePoints Q Lk) (aPer0 : PeriodAtZeroAtBundlePoints Q Lk) (aPerTw : TwistedPeriodAtBundlePoints Q Lk) (tie : Row_tie Q Lk) :
    Row Q Lk fun 𝒜 _ => All 𝒜 :=
  Row.imp (Row.and aPt0 (Row.and aPtTw (Row.and aPer0 (Row.and aPerTw tie))))
    fun _ _ _ ⟨a0, a1, a2, a3, a4⟩ => ⟨a0, a1, a2, a3, a4⟩

example (𝒜 : FamClass) : H_aPerTw 𝒜 ↔ EvC (fun D O => Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D O.X O.ex.tw) 𝒜 := Iff.rfl

end GlobalTheory.Fc.PeriodEntriesOverColumns

end
end

