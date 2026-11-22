import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtMain
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import ReciprocityTheory.SemistableReduction.Bundle0029
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.LiftSec
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLoc
import Formalism.LocalToGlobal.ProjectiveLattices.LiftRG

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem htConcl_dataOf (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (hne : CompNe Xo c) (hfg : FnFG Xo c) (htr : FnTrdeg Xo c Dd) (hac : FnAlgClosed Xo c)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (het : NZAt h etR) (hta1 : NZAt h ta1R) (hta2 : NZAt h ta2R)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hfn : FnNe Xo c fn) (hconj : FnConj Xo c fn yP)
    (hbdd : LawBdd (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha1 : A1Bigness (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha2 : A2RegularityOrders (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha3' : LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (sel : Fin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).del → Fin np)
    (ha4 : A4Selection (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) sel)
    (hnum : NumOK (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha13 : A13Measurable (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (hH1 : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).FinitePlaceHyp) (hF1d : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).TrivialPlaceHyp)
    (hLAM : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtLAM) (hSup : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtSup)
    (hI2et : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralEstimateTrivialPlace) (hI2be : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralBoundEstimate) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).htOf (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)
      ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13))) :=
  (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).heights (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)
    ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)) hH1 hF1d hLAM hSup hI2et hI2be

section Of

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {Tc : Core D}

theorem htConcl_dataOf_of (hL : LawsCore Tc) (j : ℕ) [Fintype (Comp (Tc.Q.Xo j) Tc.Q.c)]
    [Nonempty (HeightOneSpectrum (𝓞 Tc.Q.c.F))] (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (δ : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Tc.Q.Dw j) → ℤ)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (d N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR D.host.E)
    (wR : Fin (N + 1) → Tc.R j) (jc : Comp (Tc.Q.Xo j) Tc.Q.c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Tc.R j) (n0 : ℕ) (th0R : Fin n0 → Tc.R j) (uF0 : WtR D.host.E)
    (nk : ℕ) (thkR : Fin nk → Tc.R j) (MR : Set (Tc.R j)) (etR ta1R ta2R : Tc.R j)
    (nu : HeightOneSpectrum (𝓞 Tc.Q.c.F) → ℝ)
    (ip : (Tc.Q.c.F →+* ℂ) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → ℂ)
    (wsize : WTZ D.host.E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (C : ((D.host.E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule Tc.Q.c.F (Tc.R j))
    (cls : ∀ (T : CDVR) (ι : Tc.Q.c.F →+* T.Fr), IntFr (Tc.Q.Xo j) Tc.Q.c T ι → Prop) (PY : HeightOneSpectrum (𝓞 Tc.Q.c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : Tc.Q.c.F →+* T.Fr), IntFr (Tc.Q.Xo j) Tc.Q.c T ι → PY la → Prop)
    {rU : ℕ} (U : ∀ σ : Tc.Q.c.F →+* ℂ, Unf (Tc.Q.Xo j) Tc.Q.c σ rU)
    (nuA : HeightOneSpectrum (𝓞 Tc.Q.c.F) → ℝ) (large₂ : SizeData₂ D) (CL AL : ℝ) (ka : WeightFamilies.Wt D j)
    (mx : (Tc.Q.c.F →+* ℂ) → ℝ)

    (hne : CompNe (Tc.Q.Xo j) Tc.Q.c) (hac : FnAlgClosed (Tc.Q.Xo j) Tc.Q.c)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (hetN : NZAt h etR) (hta1N : NZAt h ta1R) (hta2N : NZAt h ta2R)
    (hfn : FnNe (Tc.Q.Xo j) Tc.Q.c fn) (hconj : FnConj (Tc.Q.Xo j) Tc.Q.c fn yP)
    (hbdd : LawBdd (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r))
    (ha1 : A1Bigness (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r))
    (sel : Fin (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc
      np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r).del → Fin np)
    (ha4 : A4Selection (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r) sel)
    (hT : OrdTie h δ cls PY lies) (hTQ : OrdTieQ h δ) (hTQZ : OrdTieQZ h δ)

    (hktr : KapTrdeg (Tc.Q.Xo j) Tc.Q.c d)
    (hD : DivFin (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r))
    (hF : FrShFin (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r) δ)
    (hst : STLoc h (d + Nat.card (FlagVar (Tc.Q.Dw j))) N uL wR jc) (hna : NrmAlong fn yP)
    (hR1 : RegularityR1ValuedPoints (Tc.Q.Xo j) Tc.Q.c C cls PY lies) (hR1Q : RegularityR1Quotient (Tc.Q.Xo j) Tc.Q.c C)
    (hwS : ∀ k, wR k ∈ sec (Tc.Q.Xo j) Tc.Q.c uL.1 uL.2) (hwC : ∀ k, wR k ∈ C uL.1 uL.2) (hwI : ∀ k, IntAlg (wR k))
    (hpS : ∀ k, thpR k ∈ sec (Tc.Q.Xo j) Tc.Q.c uF.1 uF.2) (hpC : ∀ k, thpR k ∈ C uF.1 uF.2) (hpI : ∀ k, IntAlg (thpR k))
    (heS : etR ∈ sec (Tc.Q.Xo j) Tc.Q.c uet.1 uet.2) (heC : etR ∈ C uet.1 uet.2) (heI : IntAlg etR)
    (h1S : ta1R ∈ sec (Tc.Q.Xo j) Tc.Q.c uta1.1 uta1.2) (h1C : ta1R ∈ C uta1.1 uta1.2) (h1I : IntAlg ta1R)
    (h2S : ta2R ∈ sec (Tc.Q.Xo j) Tc.Q.c uta2.1 uta2.2) (h2C : ta2R ∈ C uta2.1 uta2.2) (h2I : IntAlg ta2R)

    (hreg : regular₂ (Tc.Q.Xo j) Tc.Q.c U) (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2)
    (hws : ∀ k, wR k ∈ cusp (Tc.Q.Xo j) Tc.Q.c U uL.1 uL.2) (hetc : etR ∈ cusp (Tc.Q.Xo j) Tc.Q.c U uet.1 uet.2)
    (hnzc : NoCommonZero (Tc.Q.Xo j) Tc.Q.c wR)
    (halg : ∀ la, ∀ v ∈ valSet (Tc.Q.Xo j) Tc.Q.c (algCls (Tc.Q.Xo j) Tc.Q.c) la, 0 ≤ v etR ∧
      (v etR ≠ ⊤ → (⨅ k, v (wR k)) ≤ (nuA la : EReal) + ((cc / (2 * i) : ℝ) : EReal) * v etR))

    (hgt : GenFromTest (Tc.Q.Xo j) Tc.Q.c h)
    (hka : wtZ (wtA ka) ka.n = (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet
      uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive
      tableLineDegreeTwo Prw PO f r).n96 • wtZ uL.1 uL.2)
    (hj : InR D j) (hKey : KeyCore)
    (Xx : (Tc.U j Tc.σ₀).Comp → DataX D.host.E D.R.r) (hX : ∀ k, (Xx k).toData = (Tc.U j Tc.σ₀).X k)
    (M wf : ℝ) (hM : 0 < M)
    (hwf : ∀ k, (∑ τ, ((Tc.U j Tc.σ₀).X k).spread (laU (Tc.U j Tc.σ₀) (wtA ka) ka.n k) τ) ≤ wf) (hwf1 : 1 ≤ wf)
    (hr : 0 < D.R.r)
    (htr : ∀ k, ∀ v ∈ (Xx k).L', herm ((Tc.U j Tc.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ ((Tc.U j Tc.σ₀).X k).Γ, ((Tc.U j Tc.σ₀).X k).χ (laU (Tc.U j Tc.σ₀) (wtA ka) ka.n k) γ = 1 ∧
        ∀ τ : ((Tc.U j Tc.σ₀).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 =
          ((Tc.U j Tc.σ₀).X k).flowMat v τ ((M : ℂ) * τ.1 b))
    (hAA : ∀ k, ∀ a ∈ D.host.AA, ∀ v ∈ (Xx k).L', a • v ∈ (Xx k).Λ)
    (aMax : ℕ) (hPt : ∀ La, LamPtSt Tc j La) (hDeg : LamDegSt Tc.Q.H large₂.logOm) (hInd : LamIndSt)
    (hTie : ∀ k, LamTieSt Tc hL j ka (laOf Xx M wf k) aMax) (hLa1 : ∀ k, 1 ≤ laOf Xx M wf k)
    (hroom : ∀ k, ∀ s : ℕ, s ≤ aMax →
      (pDeg large₂.logOm + (1 / 2) * Real.log (laOf Xx M wf k)) *
          ((s : ℝ) + ((D.R.f * ((Tc.Q.Dw j).p + (Tc.Q.Dw j).q) : ℕ) : ℝ) * ka.n) +
        (s : ℝ) * Real.log ((D.R.r : ℝ) * laOf Xx M wf k) ≤
      WeightFamilies.PP0v D large₂ CL AL * (1 + Real.log ka.size) * ka.size)
    (hprod : ProdInLat hL j ka wR (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude
      uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet
      tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96)
    (hsupL : SupPTGe hL j h fn yP ka)
    (wL : WeightFamilies.Wt D j) (huL : uL = (wtA wL, wL.n)) (hwsz : wsize (wtZ uL.1 uL.2) = wL.size)
    (hlc : LamConst j large₂ CL AL ka PP0' (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka
      ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4
      Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 wL.size)

    (hcx : ValAtCx h yP)
    (hwB : ∀ k, SupBdd (Tc.Q.Xo j) Tc.Q.c fn uL.1 uL.2 (wR k)) (hwN : ∀ k, NZSome h (wR k))
    (hpB : ∀ k, SupBdd (Tc.Q.Xo j) Tc.Q.c fn uF.1 uF.2 (thpR k)) (hpN : ∀ k, NZSome h (thpR k))
    (h1B : SupBdd (Tc.Q.Xo j) Tc.Q.c fn uta1.1 uta1.2 ta1R) (h1N : NZSome h ta1R)
    (h2B : SupBdd (Tc.Q.Xo j) Tc.Q.c fn uta2.1 uta2.2 ta2R) (h2N : NZSome h ta2R)
    (hmx : ∀ σ k, Real.log (supR (Tc.Q.Xo j) Tc.Q.c fn σ uL.1 uL.2 (wR k)) ≤ mx σ)
    (hmxm : meanK mx ≤ Gc * wsize (wtZ uL.1 uL.2))
    (hth : ∀ k, meanK (fun σ => Real.log (supR (Tc.Q.Xo j) Tc.Q.c fn σ uF.1 uF.2 (thpR k))) ≤ Gc * wsize (wtZ uF.1 uF.2))
    (hsa1 : meanK (fun σ => Real.log (supR (Tc.Q.Xo j) Tc.Q.c fn σ uta1.1 uta1.2 ta1R)) ≤
      2 * PI4 * (((d + Nat.card (FlagVar (Tc.Q.Dw j))) : ℕ) : ℝ) * wsize (wtZ uL.1 uL.2))
    (hsa2 : meanK (fun σ => Real.log (supR (Tc.Q.Xo j) Tc.Q.c fn σ uta2.1 uta2.2 ta2R)) ≤
      PI4 * (((d + Nat.card (FlagVar (Tc.Q.Dw j))) : ℕ) : ℝ) * wsize (wtZ uL.1 uL.2))

    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = ((d + Nat.card (FlagVar (Tc.Q.Dw j))) + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2) (hcc : 0 ≤ cc)
    (hnum : NumOK (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r))

    (hH1 : (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np
      thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r).FinitePlaceHyp)
    (hI2et : (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np
      thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r).HeightIntegralEstimateTrivialPlace)
    (hI2be : (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np
      thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r).HeightIntegralBoundEstimate) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl ((dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet
      uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive
      tableLineDegreeTwo Prw PO f r).htOf (axHOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r hne (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) hac hwb hetN hta1N
      hta2N huet huta1 huta2 hfn hconj hbdd ha1 (lawA2_of_data (h := h) (δ := δ) (C := C) (cls := cls) (PY := PY) (lies
      := lies) (fn := fn) (yP := yP) (Dd := (d + Nat.card (FlagVar (Tc.Q.Dw j)))) (N := N) (T := T) (i := i) (g0 :=
      g0) (cc := cc) (uL := uL) (uF := uF) (uka := uka) (ude := ude) (uet := uet) (uta1 := uta1) (uta2 := uta2) (wR
      := wR) (jc := jc) (np := np) (thpR := thpR) (n0 := n0) (th0R := th0R) (uF0 := uF0) (nk := nk) (thkR := thkR)
      (MR := MR) (etR := etR) (ta1R := ta1R) (ta2R := ta2R) (nu := nu) (ip := ip) (wsize := wsize) (DF := DF) (PN :=
      PN) (PQ := PQ) (tableDegreeThreeBase := tableDegreeThreeBase) (PP0' := PP0') (Pd := Pd) (Gc := Gc) (PI4 := PI4) (Pet := Pet) (tableLineDegreeFive := tableLineDegreeFive) (tableLineDegreeTwo
      := tableLineDegreeTwo) (Prw := Prw) (PO := PO) (f := f) (r := r) (hT := hT) (hTQ := hTQ) (hR1 := hR1) (hR1Q := hR1Q) (hwS :=
      hwS) (hwC := hwC) (hwI := hwI) (hpS := hpS) (hpC := hpC) (hpI := hpI) (heS := heS) (heC := heC) (heI := heI)
      (h1S := h1S) (h1C := h1C) (h1I := h1I) (h2S := h2S) (h2C := h2C) (h2I := h2I) (huet := huet) (huta1 := huta1)
      (huta2 := huta2) (heN := hetN) (h1N := hta1N) (h2N := hta2N)) (lawA3'_dataOf (h := h) (hD := hD) (hF := hF))
      sel ha4 hnum (lawA13_of_data h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r (nrmContOff_of h fn yP _ N uL wR jc hst hna hfn (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) hwb))) ((dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r hne (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) hac hwb hetN hta1N
      hta2N huet huta1 huta2 hfn hconj hbdd ha1 (lawA2_of_data (h := h) (δ := δ) (C := C) (cls := cls) (PY := PY) (lies
      := lies) (fn := fn) (yP := yP) (Dd := (d + Nat.card (FlagVar (Tc.Q.Dw j)))) (N := N) (T := T) (i := i) (g0 :=
      g0) (cc := cc) (uL := uL) (uF := uF) (uka := uka) (ude := ude) (uet := uet) (uta1 := uta1) (uta2 := uta2) (wR
      := wR) (jc := jc) (np := np) (thpR := thpR) (n0 := n0) (th0R := th0R) (uF0 := uF0) (nk := nk) (thkR := thkR)
      (MR := MR) (etR := etR) (ta1R := ta1R) (ta2R := ta2R) (nu := nu) (ip := ip) (wsize := wsize) (DF := DF) (PN :=
      PN) (PQ := PQ) (tableDegreeThreeBase := tableDegreeThreeBase) (PP0' := PP0') (Pd := Pd) (Gc := Gc) (PI4 := PI4) (Pet := Pet) (tableLineDegreeFive := tableLineDegreeFive) (tableLineDegreeTwo
      := tableLineDegreeTwo) (Prw := Prw) (PO := PO) (f := f) (r := r) (hT := hT) (hTQ := hTQ) (hR1 := hR1) (hR1Q := hR1Q) (hwS :=
      hwS) (hwC := hwC) (hwI := hwI) (hpS := hpS) (hpC := hpC) (hpI := hpI) (heS := heS) (heC := heC) (heI := heI)
      (h1S := h1S) (h1C := h1C) (h1I := h1I) (h2S := h2S) (h2C := h2C) (h2I := h2I) (huet := huet) (huta1 := huta1)
      (huta2 := huta2) (heN := hetN) (h1N := hta1N) (h2N := hta2N)) (lawA3'_dataOf (h := h) (hD := hD) (hF := hF))
      sel ha4 hnum (lawA13_of_data h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r (nrmContOff_of h fn yP _ N uL wR jc hst hna hfn (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) hwb))))) :=
  htConcl_dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np
    thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne
    (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) hac hwb hetN hta1N hta2N huet huta1
    huta2 hfn hconj hbdd ha1 (lawA2_of_data (h := h) (δ := δ) (C := C) (cls := cls) (PY := PY) (lies := lies) (fn := fn)
    (yP := yP) (Dd := (d + Nat.card (FlagVar (Tc.Q.Dw j)))) (N := N) (T := T) (i := i) (g0 := g0) (cc := cc) (uL :=
    uL) (uF := uF) (uka := uka) (ude := ude) (uet := uet) (uta1 := uta1) (uta2 := uta2) (wR := wR) (jc := jc) (np :=
    np) (thpR := thpR) (n0 := n0) (th0R := th0R) (uF0 := uF0) (nk := nk) (thkR := thkR) (MR := MR) (etR := etR)
    (ta1R := ta1R) (ta2R := ta2R) (nu := nu) (ip := ip) (wsize := wsize) (DF := DF) (PN := PN) (PQ := PQ) (tableDegreeThreeBase :=
    tableDegreeThreeBase) (PP0' := PP0') (Pd := Pd) (Gc := Gc) (PI4 := PI4) (Pet := Pet) (tableLineDegreeFive := tableLineDegreeFive) (tableLineDegreeTwo := tableLineDegreeTwo) (Prw := Prw) (PO
    := PO) (f := f) (r := r) (hT := hT) (hTQ := hTQ) (hR1 := hR1) (hR1Q := hR1Q) (hwS := hwS) (hwC := hwC) (hwI :=
    hwI) (hpS := hpS) (hpC := hpC) (hpI := hpI) (heS := heS) (heC := heC) (heI := heI) (h1S := h1S) (h1C := h1C)
    (h1I := h1I) (h2S := h2S) (h2C := h2C) (h2I := h2I) (huet := huet) (huta1 := huta1) (huta2 := huta2) (heN :=
    hetN) (h1N := hta1N) (h2N := hta2N)) (lawA3'_dataOf (h := h) (hD := hD) (hF := hF)) sel ha4 hnum (lawA13_of_data
    h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0
    nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r (nrmContOff_of h fn yP _ N uL wR jc hst hna hfn (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) hwb)) hH1 (height_F1_of_data h δ
    fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk
    thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r U hreg hTQZ hdL hdE hws
    hetc hnzc hetN huet hcc nuA halg) (htLAM_of hL j h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL
    uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc
    PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r large₂ CL AL ka hgt hka
    (abelian₂.lamw_link Tc hL large₂ j hj ka CL AL siegelSpaceAlgebra_holds hKey ReciprocityTheory.MultiplicativeHeights.Closed.lemmaH Xx hX M wf hM hwf hwf1 hr htr hAA aMax hPt hDeg hInd hTie hLa1 hroom) hprod
    hsupL (by rw [hwsz]; exact hlc)) (htSup_of h δ fn yP (d + Nat.card (FlagVar
    (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip
    wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hfn (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) hcx huta1 huta2
    hwS hwB hwN hpS hpB hpN h1S h1B h1N h2S h2B h2N mx hmx hmxm hth hsa1 hsa2) hI2et hI2be

end Of

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
  (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1)

def parAt : Par D where
  H := hostOfRecord D
  l := l
  c :=
    { F := FO D
      fin := inferInstance
      conj := fun τ a => conj_mem_FO D τ a
      zeta_mem := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).zeta_mem
        have h1 : (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))).M' = l.M' := by
          simp [Level.M', levelG, levelOfPs, hl.1, hl.2]
        rw [h1] at h
        exact h
      le := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).le
        have h1 : KA l = KA (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))) := by
          unfold KA
          rw [hl.2]
          rfl
        rw [h1]
        exact h }
  Dw := datumAtLift D _ (datHolds D)
  Xo := fun j => Classical.choice (hN D.host.E _ (datumAtLift D _ (datHolds D) j) l (datumAtLift_pq_pos D _ (datHolds D) j))
  eO := eOf D hF

theorem parAt_pins : (parAt D hF hz hN l hl).Pins := by
  refine ⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, hl, eOf_spec D hF, fun j hj => ?_⟩
  show IsDatW D j (datumAtLift D _ (datHolds D) j)
  unfold datumAtLift
  rw [dif_pos hj]
  exact isDatW_datumOf D _ j _ _

theorem parAt_pq (j : ℕ) : 1 ≤ ((parAt D hF hz hN l hl).Dw j).p + ((parAt D hF hz hN l hl).Dw j).q :=
  datumAtLift_pq_pos D _ (datHolds D) j

def LevelPb (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∃ l : Level (hostOfRecord D), (l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) ∧
    l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

theorem coreJExists_at (hN1c : N1c) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal)
    (hb : l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)))
    (chiW : ℕ → ((parAt D hF hz hN l hl).c.F →+* ℂ) → (AE D)ˣ →* Circle)
    (L : LawsJRest hN1c (parAt D hF hz hN l hl) (parAt_pq D hF hz hN l hl) chiW) :
    ∃ T : CoreJ D, LawsJ T ∧ T.pb = pb ∧ T.Q = parAt D hF hz hN l hl ∧ HEq T.chiW chiW := by
  have h := lawsJ_coreJOf L (parAt_pins D hF hz hN l hl)
  exact ⟨{ coreJOf L with toCore := { (coreJOf L).toCore with pb := pb } },
    { h with toLawsM := { h.toLawsM with half := ⟨hg, hb⟩ } }, rfl, rfl, HEq.rfl⟩

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveInstSt
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7}

def SpanW {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → B.Cusp j wL) (S : Scal B) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc S.sW wL

variable {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def wNorm (σ : T.Q.c.F →+* ℂ) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (p : FPt (T.U j σ).X) : ℝ :=
  Real.sqrt (∑ k, (((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA wL) wL.n p.1)
    (rdU (T.U j σ) ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) p.1) p.2) ^ 2)

def BigAt (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  NoCommonZero (Xo := T.Q.Xo j) (c := T.Q.c) (fun k => ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j)) ∧
  (∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧
    Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k =>
      evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) /
        evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j)

def ThAt (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  ∃ (e : ℕ) (w' : WeightFamilies.Wt D j) (θ : (recB h.toLawsCore).Cusp j w'),
    wadd wF w' = wsmul e wL ∧
    ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0

def CurveInstSt : Prop :=
  ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF),
    SpanW (recPlus h j hj) G.w S → BigAt h j hj hG G → ThAt h j hj hG G g0 → (recPlus h j hj).NonZeroComp wF g0 →
    Nonempty (CurveModel G la g0)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.EtArch
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Top D} (h : LawsP T)

def EtArch (th tableLineDegreeTwo : ℝ) : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop :=
  fun j i η => ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom →
      lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) *
          ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (wEt D j i)) (wEt D j i).n k)
            (rdU (T.U j σ) η.1 k) x ≤
        Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x - tableLineDegreeTwo))

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LiftModelPf
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain Finset

lemma nval_alg_nonneg {T : CDVR} (x : T.V) : 0 ≤ nval T.V 1 (algebraMap T.V T.Fr x) := by
  by_cases hx : x = 0
  · rw [hx, map_zero, nval_zero]; exact le_top
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (mt (IsDiscreteValuationRing.addVal_eq_top_iff).1 hx)
    have h0 : algebraMap T.V T.Fr x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hx
    rw [nval_of_ne h0, vV_alg_of_addVal hk.symm]
    exact EReal.coe_nonneg.2 (by positivity)

lemma nval_inv_nonneg {T : CDVR} {x : T.Fr} (hx : x ≠ 0) (h0 : vV T.V x = 0) : 0 ≤ nval T.V 1 x⁻¹ := by
  rw [nval_of_ne (inv_ne_zero hx), vV_inv' hx, h0]; simp

lemma toE_nonneg' {w : WithTop ℤ} (h : 0 ≤ w) : 0 ≤ toE w := by
  cases w with
  | top => simp [toE]
  | coe n =>
    simp only [toE]
    have : (0 : ℤ) ≤ n := by exact_mod_cast h
    exact_mod_cast this

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
  {y : PtsG G la → E.Pt' la} (hw : ∀ ζ, FromW ζ (y ζ))

abbrev hsW : ∀ ζ, SecPt ζ (y ζ) := fun ζ => (hw ζ).toSecPt

def IW : Ideal (LamL (hsW hw)) := Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
  ιW (hsW hw) (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w))

def RGW : Subring (LamL (hsW hw)) :=
  stabSub (hdL_zero (hsW hw)) (hdW_mul (hsW hw)) (intSub (fun ζ => (hsW hw ζ).T) (evL (hsW hw))) ⊓
    appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw)

theorem ιW_Jid {z : ↥(Frac0 (xplus X E hM) la G.w)} (hz : z ∈ Jid (xplus X E hM) la G.w) :
    ιW (hsW hw) (z : Lw (xplus X E hM) la G.w) ∈ IW hw := by
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Ideal.subset_span ⟨i, rfl⟩
  | zero => rw [ZeroMemClass.coe_zero, map_zero]; exact Ideal.zero_mem _
  | add x z _ _ hx hz => rw [Subalgebra.coe_add, map_add]; exact Ideal.add_mem _ hx hz
  | smul a x _ hx => rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]; exact Ideal.mul_mem_left _ _ hx

theorem RGW_hd (β : Idx D j G.N →₀ ℕ) (r : LamL (hsW hw)) (hr : r ∈ RGW hw) : hdL (hsW hw) β r ∈ RGW hw :=
  ⟨stabSub_hd _ _ _ β hr.1, appSub_hd (hdL_zero (hsW hw)) (hdW_mul (hsW hw)) (ιW (hsW hw)) _ _
    (fun β x => hasse (xplus X E hM) la G.w β x) (hdW_ι (hsW hw))
    (fun β f hf => (mem_Frac0 _ _ _).2 (hasse_mem_Hfr _ _ _ ((mem_Frac0 _ _ _).1 hf) β)) β hr.2⟩

theorem RGW_int (ζ : PtsG G la) (r : LamL (hsW hw)) (hr : r ∈ RGW hw) :
    0 ≤ nval (hsW hw ζ).T.V 1 (evL (hsW hw) ζ r) :=
  stabSub_le _ _ _ hr.1 ζ

theorem iterHd_ιW (l : List (Idx D j G.N →₀ ℕ)) (x : Lw (xplus X E hM) la G.w) :
    iterHd (hdL (hsW hw)) l (ιW (hsW hw) x) =
      ιW (hsW hw) (l.foldr (fun β z => hasse (xplus X E hM) la G.w β z) x) := by
  induction l with
  | nil => rfl
  | cons β l ih => rw [iterHd_cons, ih, hdW_ι]; rfl

theorem stab_of_hdInt {x : Lw (xplus X E hM) la G.w} (hx : HdIntAt (hsW hw) x) :
    ιW (hsW hw) x ∈ stabSub (hdL_zero (hsW hw)) (hdW_mul (hsW hw))
      (intSub (fun ζ => (hsW hw ζ).T) (evL (hsW hw))) := fun l ζ => by
  show 0 ≤ nval (hsW hw ζ).T.V 1 (evL (hsW hw) ζ (iterHd (hdL (hsW hw)) l (ιW (hsW hw) x)))
  rw [iterHd_ιW, evW_ι]
  exact hx l ζ

theorem app_of_mem (f : ↥(Frac0 (xplus X E hM) la G.w)) :
    ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) ∈
      appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw) :=
  fun n => ⟨f, f.2, by rw [sub_self]; exact Ideal.zero_mem _⟩

theorem evL_inv (ζ : PtsG G la) {u : LamL (hsW hw)} (hu : IsUnit u) :
    evL (hsW hw) ζ ↑hu.unit⁻¹ = (evL (hsW hw) ζ u)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, hu.val_inv_mul, map_one]

theorem inv_app {g0 : B.Cusp j wF} (C : CurveModel G la g0) (d : ↥(Frac0 (xplus X E hM) la G.w))
    (hd : ∀ ζ, (hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0) :
    (↑(isUnit_of_lift_ne (hsW hw) hd).unit⁻¹ : LamL (hsW hw)) ∈
      appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw) := by
  obtain ⟨b, hb⟩ := (isUnit_toOsK_of_lift hw C d hd).exists_right_inv
  obtain ⟨v, rfl⟩ := toOsK_surjective (xplus X E hM) la G.w b
  have hz : (1 - d * v : ↥(Frac0 (xplus X E hM) la G.w)) ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_sub, map_one, map_mul, hb, sub_self]
  have h := ιW_Jid hw hz
  push_cast at h
  exact appSub_inv _ _ _ d.2 v.2 h _

theorem inv_RG {g0 : B.Cusp j wF} (C : CurveModel G la g0) (d : ↥(Frac0 (xplus X E hM) la G.w))
    (hd : ∀ ζ, (hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0 ∧
      vV (hsW hw ζ).T.V ((hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w)) = 0)
    (hdi : HdIntAt (hsW hw) (d : Lw (xplus X E hM) la G.w)) :
    (↑(isUnit_of_lift_ne (hsW hw) (fun ζ => (hd ζ).1)).unit⁻¹ : LamL (hsW hw)) ∈ RGW hw := by
  refine ⟨stabSub_inv _ _ _ _ (stab_of_hdInt hw hdi) (fun ζ => ?_), inv_app hw C d (fun ζ => (hd ζ).1)⟩
  show 0 ≤ nval (hsW hw ζ).T.V 1 (evL (hsW hw) ζ _)
  rw [evL_inv, evW_ι]
  exact nval_inv_nonneg (hd ζ).1 (hd ζ).2

theorem mem_RG_of {g0 : B.Cusp j wF} (C : CurveModel G la g0) (f d : ↥(Frac0 (xplus X E hM) la G.w))
    (hd : ∀ ζ, (hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0 ∧
      vV (hsW hw ζ).T.V ((hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w)) = 0)
    (hfi : HdIntAt (hsW hw) (f : Lw (xplus X E hM) la G.w)) (hdi : HdIntAt (hsW hw) (d : Lw (xplus X E hM) la G.w)) :
    ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) *
      ↑(isUnit_of_lift_ne (hsW hw) (fun ζ => (hd ζ).1)).unit⁻¹ ∈ RGW hw :=
  (RGW hw).mul_mem ⟨stab_of_hdInt hw hfi, app_of_mem hw f⟩ (inv_RG hw C d hd hdi)

end Formalism.L2.Pj
end
end

