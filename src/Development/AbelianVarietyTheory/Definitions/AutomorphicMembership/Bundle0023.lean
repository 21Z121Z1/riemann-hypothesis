import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ValTransOfEq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Generic

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {N : Type} [AddCommGroup N] [Module ℂ N] {P P' : Submodule ℂ N}
  {ip : N → N → ℂ} {j : X ≃ₗ[ℂ] P}

theorem hilbTie_ofEq (e : P = P') (h : HilbTie P ip j) : HilbTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) := fun x y => h x y

theorem projTie_ofEq {Y : Type} {f : Y → X} {g g' : Y → N} (e : P = P') (h : ProjTie P ip j f g) (hg : ∀ y, g' y = g y) :
    ProjTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) f g' := fun x y => (h x y).trans (congrArg (ip (j x)) (hg y).symm)

omit [NormedAddCommGroup X] [InnerProductSpace ℂ X] in

theorem le_of_eqs {Q Q' : Submodule ℂ N} (e : P = P') (e' : Q = Q') (h : P ≤ Q) : P' ≤ Q' := e ▸ e' ▸ h

theorem val_trans_ofEq (e : P = P') (x : X) : ((j.trans (LinearEquiv.ofEq _ _ e)) x).1 = (j x).1 := rfl

theorem map_incl {Q Q' : Submodule ℂ N} {Z : Type} (e : P = P') (e' : Q = Q') (h : P ≤ Q) (j : X ≃ₗ[ℂ] P) {f : Q → Z} (f' : Q' → Z)
    (hf : ∀ v, f' (LinearEquiv.ofEq _ _ e' v) = f v) (y : X) :
    f' (Submodule.inclusion (le_of_eqs e e' h) ((j.trans (LinearEquiv.ofEq _ _ e)) y)) = f (Submodule.inclusion h (j y)) := by
  subst e e'
  exact hf (Submodule.inclusion h (j y))

end Generic

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A} {tupT : a.D.what₂.Tup → T}
  {hm : 0 < a.D.R.m} {hTop : TopMultH R}

def stepB (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : spCC c F tupT hm hTop l μ (k + 1)) : (toChainReal R F tupT hm hTop).Amb k :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioC l ((μ)) k ((v))).1 : _))

theorem stepB_eq (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) :
    stepB c l μ k (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v) =
      ((toChainReal R F tupT hm hTop).ioC l μ k v).1 := (ioCB_eq c l μ k v)

def topB (l : Bool) (μ : a.D.what₂.Tup) (v : spCCX c F tupT hm hTop l μ) : (toChainReal R F tupT hm hTop).Amb (a.D.R.m - 1) :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioX l ((μ)) ((v))).1 : _))

theorem topB_eq (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) :
    topB c l μ (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v) =
      ((toChainReal R F tupT hm hTop).ioX l μ v).1 := (ioXB'_eq c l μ v)

section Rows

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {X : RowSide a.D EE} {l : Bool}

def rowIds (I : RowIds X (toChainReal R F tupT hm hTop) l) : RowIds (rowSide c X) (chainB c.to F tupT hm hTop) l :=
  @RowIds.mk c.to.D EE _ _ _ (rowSide c X) (chainB c.to F tupT hm hTop) l
    ((by with_unfolding_all exact ((I.jE.trans (LinearEquiv.ofEq _ _ (congrFun (spEEc_eq c F tupT hm hTop) l))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) => (I.jM μ h j h1 h2).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) => (I.jX μ h).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ))) :)))
    ((I.prt))

set_option maxHeartbeats 800000 in

theorem rowSideReal_tr {I : RowIds X (toChainReal R F tupT hm hTop) l} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE}
    {ty : Fin n → a.D.what₂.FT} (H : RowSideReal X (toChainReal R F tupT hm hTop) l I bs ty) :
    RowSideReal (rowSide c X) (chainB c.to F tupT hm hTop) l (rowIds c I) bs ((ty)) := by
  refine @RowSideReal.mk _ _ _ _ _ _ _ _ _ _ _ _ ?parY ?lvl ?lvlP ?lvlX ?ee ?mult ?multX ?io0 ?io0X ?io ?ioTop ?ft ?prt_disj
  case parY =>
    exact (H.parY)
  case lvl =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (spEEc_eq c F tupT hm hTop) l) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) 0) (H.lvl μ hμ))
  case lvlP =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) =>
      le_of_eqs (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) j) (H.lvlP μ hμ j h1 h2))
  case lvlX =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) (H.lvlX μ hμ))
  case ee =>
    kexactB (hilbTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) H.ee)
  case mult =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) =>
      hilbTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (H.mult μ hμ j h1 h2))
  case multX =>
    kexactB (fun (h : 1 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) =>
      hilbTie_ofEq (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (H.multX h μ hμ))
  case io0 =>
    kexactB (fun (h : 2 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) (H.io0 h μ hμ (okB_imp c ok)) fun y =>
        map_incl (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (0 + 1))
          (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (0 + 1)) (H.lvlP μ hμ 1 le_rfl (by omega))
          (I.jM μ hμ 1 le_rfl (by omega)) (stepB c l μ 0) (stepB_eq c l μ 0) y)
  case io0X =>
    kexactB (fun (h : a.D.R.m = 1) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) (H.io0X h μ hμ (okB_imp c ok)) fun y =>
        congrArg (cast (congrArg (toChainReal R F tupT hm hTop).Amb (show a.D.R.m - 1 = 0 by omega)))
          (map_incl (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ)
            (H.lvlX μ hμ) (I.jX μ hμ) (topB c l μ) (topB_eq c l μ) (cast (congrArg (X.Mult μ) h.symm) y)))
  case io =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) (j : ℕ) (h1 : 1 ≤ j)
        (h2 : j + 1 ≤ a.D.R.m - 1) =>
      projTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (H.io μ hμ (okB_imp c ok) j h1 h2) fun y =>
        map_incl (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (j + 1))
          (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (j + 1)) (H.lvlP μ hμ (j + 1) (by omega) h2)
          (I.jM μ hμ (j + 1) (by omega) h2) (stepB c l μ j) (stepB_eq c l μ j) y)
  case ioTop =>
    kexactB (fun (h : 2 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (a.D.R.m - 1)) (H.ioTop h μ hμ (okB_imp c ok)) fun y =>
        map_incl (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ)
          (H.lvlX μ hμ) (I.jX μ hμ) (topB c l μ) (topB_eq c l μ) y)
  case ft =>
    kexactB (fun σ => cast (congrArg (· ∈ I.prt (ty σ)) (val_trans_ofEq (j := I.jE) (congrFun (spEEc_eq c F tupT hm hTop) l) (bs σ)).symm) (H.ft σ))
  case prt_disj =>
    exact (H.prt_disj)

end Rows

variable {hinj : ∀ i t, Function.Injective (R.extV i t)}

variable (F tupT hm hTop hinj) in

def spWc : type_of% (toLiftReal R F tupT hm hTop hinj).Wc := ((liftB c.to F tupT hm hTop hinj).Wc)

variable (F tupT hm hTop hinj) in

theorem spWc_eq : (toLiftReal R F tupT hm hTop hinj).Wc = spWc c F tupT hm hTop hinj := (lift_Wc c.to F tupT hm hTop hinj)

variable (F tupT hm hTop hinj) in

def spMultW : type_of% (toLiftReal R F tupT hm hTop hinj).MultW := ((liftB c.to F tupT hm hTop hinj).MultW)

variable (F tupT hm hTop hinj) in

theorem spMultW_eq : (toLiftReal R F tupT hm hTop hinj).MultW = spMultW c F tupT hm hTop hinj := (lift_MultW c.to F tupT hm hTop hinj)

def liftIds (I : LiftIds (toLiftReal R F tupT hm hTop hinj)) : LiftIds (liftB c.to F tupT hm hTop hinj) :=
  @LiftIds.mk c.to.D (chainB c.to F tupT hm hTop) (liftB c.to F tupT hm hTop hinj)
    ((by with_unfolding_all exact ((fun i : Fin a.D.R.m => (I.jMj i).trans (LinearEquiv.ofEq _ _ (congrFun (spWc_eq c F tupT hm hTop hinj) i))) :)))
    ((I.jMt)) ((I.prtW))

theorem liftTie_tr {I : LiftIds (toLiftReal R F tupT hm hTop hinj)} (H : LiftTie (toLiftReal R F tupT hm hTop hinj) I) :
    LiftTie (liftB c.to F tupT hm hTop hinj) (liftIds c I) := by
  refine @LiftTie.mk _ _ _ _ ((H.hol)) (kc% (fun i => hilbTie_ofEq (congrFun (spWc_eq c F tupT hm hTop hinj) i) (H.mj i))) ((H.mt)) ?_ (kc% H.isot) ((H.prtW_disj)) ((H.lamP))
  kexactB (cast (congrArg₂ (fun (P : type_of% (toLiftReal R F tupT hm hTop hinj).MultW) (Q : type_of% (toLiftReal R F tupT hm hTop hinj).Wc) =>
    ∀ μ (hμ : Used0 a.D μ) (i : Fin a.D.R.m) (x : a.D.what₂.Mt μ (i + 1)) (w : (toLiftReal R F tupT hm hTop hinj).AmbW i),
      Lift.IsThetaP ((toLiftReal R F tupT hm hTop hinj).measV μ i) ((toLiftReal R F tupT hm hTop hinj).fdV μ i)
        ((toLiftReal R F tupT hm hTop hinj).thW μ i) ((toLiftReal R F tupT hm hTop hinj).ptW μ i) ((toLiftReal R F tupT hm hTop hinj).ioK i)
        ((toLiftReal R F tupT hm hTop hinj).Amt μ i) ((toLiftReal R F tupT hm hTop hinj).thC μ i) → w ∈ P i →
      w ∘ₗ (toLiftReal R F tupT hm hTop hinj).embK i = (toLiftReal R F tupT hm hTop hinj).thC μ i (I.jMt μ hμ i x) →
      (toLiftReal R F tupT hm hTop hinj).eW i ∘ₗ w ∈ Q i →
      (I.jMj i (a.D.what₂.thetaP μ (i + 1) x)).1 = (toLiftReal R F tupT hm hTop hinj).eW i ∘ₗ w)
    (spMultW_eq c F tupT hm hTop hinj) (spWc_eq c F tupT hm hTop hinj)) (kc% H.theta))

theorem recTied_tr {X0 : BaseLevelRowSide a.D} {Ish : RowIds (RowSide.sharp a.D) (toChainReal R F tupT hm hTop) true}
    {Iz : RowIds X0.s (toChainReal R F tupT hm hTop) false} {IL : LiftIds (toLiftReal R F tupT hm hTop hinj)} {K : ColReal a.D}
    (H : RecTied a.D X0 (toChainReal R F tupT hm hTop) Ish Iz (toLiftReal R F tupT hm hTop hinj) IL K) :
    RecTied c.to.D (baseLevelRowSideTransport c X0) (chainB c.to F tupT hm hTop) ((rowIds c Ish)) ((by with_unfolding_all exact @rowIds B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz)) (liftB c.to F tupT hm hTop hinj)
      (liftIds c IL) (colReal c K) :=
  @RecTied.mk _ _ _ _ _ _ _ _ ((rowSideReal_tr c H.sharp)) ((by with_unfolding_all exact @rowSideReal_tr B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz (@Rows.Data.D0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.onb0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.ft0 (@Late.D B C a).R (@Late.D B C a).what₂) (@RecTied.base (@Late.D B C a) X0 (@toChainReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop) Ish Iz (@toLiftReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop hinj) IL K H))) (liftTie_tr c H.lift)
    (@ColTieR.mk _ _ _ ((H.col.tup)) ((H.col.xi0)) ((H.col.bu)))

def mjTie (x : MjTie R F) : @MjTie c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) :=
  @MjTie.mk c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) ((x.eW))
    ((by with_unfolding_all exact ((cast (congrArg (fun W : type_of% R.Wat => ∀ i, LinearMap.range (x.eW i) =
      (W i (sg0 a.D A) (R.levL F false (sg0 a.D A))).comap (R.HW i (sg0 a.D A)).e) (wat_eq c.to R)) x.eW_range) :)))
    ((x.eW_norm)) ((x.eW_lat))

end Chain

end GlobalTheory.Mem.R3.Tr

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.VolumeLeOfTrivialFirstPair
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {s : ℕ}

theorem volume_le_of_trivial_first_pair (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1))
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW) (j : Fin m) (t : T) :
    X.goodPartComplexPoints (cvOf3 A3 P0 ψ0 P1 ψ1) false j t ≤ X.goodPartComplexPoints (cvOf3 A3 ⊥ 1 P1 ψ1) false j t := by
  have H := lift_hypotheses_of_unitary hok hK (cvOf3 A3 P0 ψ0 P1 ψ1) (fun _ _ _ _ => rfl) hJ hU hG j t
  have e0 := lift_good_part_complex_eq_range_family H (cv := cvOf3 A3 P0 ψ0 P1 ψ1) (b := false) (ℓ := A3.fam3.F.lvlA P0 ψ0) rfl
  have e2 := lift_good_part_complex_eq_range_family H (cv := cvOf3 A3 ⊥ 1 P1 ψ1) (b := false) (ℓ := A3.fam3.F.lvlA ⊥ 1) rfl
  have e1 : goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ = idemOf A3.fam3.F.X :=
    goodAt_bot A3.fam3.F.X _
  rw [e1] at e2
  exact e0.le.trans ((H.range_le A3.fam3.F.X P0 ψ0⁻¹).trans e2.ge)

theorem exists_crd (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 ⊥ 1 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW) (j : Fin m) (t : T) (w : X.W j)
    (hw : LinearMap.adjoint (X.θ' j t) w ∈ X.goodPartComplexPoints (cvOf3 A3 ⊥ 1 P1 ψ1) false j t) :
    ∃ c, lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t) c = LinearMap.adjoint (X.θ' j t) w := by
  have hrat := lift_rationality_of_equivariance (Dc := Dc) (Sp := Sp) (Zsc := Zsc) hok hK hJ hRZ hU hG false j t
  have hu := hrat.ge (Submodule.mem_inf.2 ⟨⟨w, rfl⟩, hw⟩)
  refine (Submodule.span_le (p := LinearMap.range (lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)))).2 ?_ hu
  rintro _ ⟨x, rfl⟩
  exact ⟨cpt A3.fam3.base3.v0.embedding x, (X.jL_toL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t x).symm⟩

theorem range_w0C_le (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW)
    (hL0 : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0)
    (hA : X.ThmAop false) (hW : X.PartsW false) (hp : ∀ j t p v, 0 < X.lam j t p v) (j : Fin m) (t : T) :
    LinearMap.range (X.w0C false j) ≤ LinearMap.range (X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t) := by
  have hup := upper_level_lift_at_lower_type hok hK hJ hU hG hL0 j t
  refine (hW j).2.ge.trans (iSup_le fun p w hw => ?_)
  obtain ⟨c, hc⟩ := exists_crd (Dc := Dc) (Sp := Sp) (Zsc := Zsc) hok hK (fun j t x y => hJ j t x y) hRZ hU hG j t w
    (volume_le_of_trivial_first_pair hok hK hJ hU hG j t (hup ⟨w, hw.2, rfl⟩))
  have hl : ((X.lam j t p A3.fam3.base3.v0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hp j t p _).ne'
  have h1 : X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t c = ((X.lam j t p A3.fam3.base3.v0 : ℝ) : ℂ) • w :=
    (X.tC_eq _ false j t c).trans ((congrArg (X.θ' j t) hc).trans (hA j t p w hw))
  refine ⟨((X.lam j t p A3.fam3.base3.v0 : ℝ) : ℂ)⁻¹ • c, (map_smul _ _ _).trans ?_⟩
  rw [h1, smul_smul, inv_mul_cancel₀ hl, one_smul]

end Level

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 2000000 in

theorem pHecke (h : R.PHecke (bare3 _ P0 ψ0 P1 ψ1)) : (dat3 f μ R mu tw).PHecke (bare3 _ P0 ψ0 P1 ψ1) := by
  obtain ⟨⟨hE, h1⟩, hW, h2⟩ := h
  exact ⟨⟨fun t => hE (f t), fun t => h1.intw (f t), h1.comm, h1.parts⟩,
    fun j t => hW j (f t), fun j t => h2.intw j (f t), h2.comm, h2.parts⟩

set_option maxHeartbeats 2000000 in

theorem liftOnto (h : R.PHecke (bare3 _ P0 ψ0 P1 ψ1))
    (ho : ∀ hW, HeckeIntertwiningLifts (A3.comap id (f μ)) (R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)) hW →
      U2.OntoC (A3.comap id (f μ)) (R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)) P0 ψ0 P1 ψ1 hW) :
    ∀ hW, HeckeIntertwiningLifts (A3.comap f μ) ((dat3 f μ R mu tw).toCx3 (bare3 _ P0 ψ0 P1 ψ1)) hW →
      U2.OntoC (A3.comap f μ) ((dat3 f μ R mu tw).toCx3 (bare3 _ P0 ψ0 P1 ψ1)) P0 ψ0 P1 ψ1 hW := by
  classical
  intro hW' h'
  obtain ⟨hW0, h0⟩ := h.2
  let hW : ∀ j t, ((A3.comap id (f μ)).liftI j t).OpIx → Module.End ℂ ((R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)).W j) :=
    fun j => Function.update (hW0 j) (f μ) (hW' j μ)
  have e : ∀ j, hW j (f μ) = hW' j μ := fun j => Function.update_self _ _ _
  have hh : HeckeIntertwiningLifts (A3.comap id (f μ)) (R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)) hW := by
    refine ⟨fun j t => ?_, fun j => ?_, fun j p => ?_⟩
    · by_cases ht : t = f μ
      · subst ht
        intro i u
        rw [e j]
        exact h'.intw j μ i u
      · have e' : hW j t = hW0 j t := Function.update_of_ne ht _ _
        rw [e']
        exact h0.intw j t
    · exact (e j).symm ▸ h'.comm j
    · exact (h'.parts j p).trans (congrArg (fun z => Formalism.L2.Col.eigSum z _) (e j).symm)
  intro j
  have := ho hW hh j
  exact (e j) ▸ this

set_option maxHeartbeats 2000000 in

theorem pLevW {s : ℕ} (hok : (A3.comap id (f μ)).fam3.Ok3 s) (hs : (A3.comap id (f μ)).fam3.TypesSep3)
    (hC : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (h : PrimRows3 R (bare3 _ P0 ψ0 P1 ψ1)) :
    (dat3 f μ R mu tw).PLevW (bare3 _ P0 ψ0 P1 ψ1) := by
  have hR := complex_data_conditions_base_level_of_primitive_links hok hs hC h
  intro j
  have h1 := range_w0C_le hok hR.kFormL hR.jIsoL hR.ratZ hR.gUnitL hR.gEquivL hR.lower_level_lift_type hR.thmAop hR.partsW h.posScal.2 j (f μ)
  have h2 := h.levW j
  apply le_antisymm
  · exact le_inf (h1.trans (le_iSup_of_le μ le_rfl)) (h2.le.trans inf_le_right)
  · refine le_trans (inf_le_inf_right _ (iSup_le fun t => ?_)) h2.ge
    exact le_iSup_of_le (f t) le_rfl

set_option maxHeartbeats 4000000 in

theorem primRows3 {s : ℕ} (hok : (A3.comap id (f μ)).fam3.Ok3 s) (hs : (A3.comap id (f μ)).fam3.TypesSep3)
    (hC : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (h : PrimRows3 R (bare3 _ P0 ψ0 P1 ψ1)) :
    PrimRows3 (dat3 f μ R mu tw) (bare3 _ P0 ψ0 P1 ψ1) where
  heckeR t := h.heckeR (f t)
  heckeL j t := h.heckeL j (f t)
  hecke := pHecke mu tw h.hecke
  gUnit := h.gUnit
  gEquiv := ⟨fun t => h.gEquiv.1 (f t), fun j t => h.gEquiv.2 j (f t)⟩
  block := ⟨fun t => h.block.1 (f t), fun j t => h.block.2 j (f t)⟩
  rowTest := by
    obtain ⟨N, ψ, h1, h2⟩ := h.rowTest
    exact ⟨N, ψ, h1, fun t => h2 (f t)⟩
  liftTest j := by
    obtain ⟨N, ψ, h1, h2⟩ := h.liftTest j
    exact ⟨N, ψ, h1, fun t => h2 (f t)⟩
  liftTestB j := by
    obtain ⟨N, ψ, h1, h2, h3⟩ := h.liftTestB j
    exact ⟨N, ψ, h1, fun t => h2 (f t), h3⟩
  liftOnto := liftOnto mu tw h.hecke h.liftOnto
  pos b := by
    cases b
    · exact h.pos false
    · exact h.pos true
  posScal := ⟨h.posScal.1, fun i t => h.posScal.2 i (f t)⟩
  levE := h.levE
  h2P := ⟨h.h2P.1, fun t => h.h2P.2 (f t)⟩
  thmB := pThmB mu tw h.thmB
  sumE := h.sumE
  unif := h.unif
  mLat := h.mLat
  levW := pLevW mu tw hok hs hC h
  thmA i t := h.thmA i (f t)
  sumW := h.sumW
  scalConj := h.scalConj
  dimParts := h.dimParts

set_option maxHeartbeats 2000000 in

theorem intersectionNumber_baseChange (hf : Function.Injective f) (hC : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (h : Holds R (bare3 _ P0 ψ0 P1 ψ1)) :
    Holds (dat3 f μ R mu tw) (bare3 _ P0 ψ0 P1 ψ1) where
  prim := primRows3 mu tw h.ok h.sep hC h.prim
  aux := ⟨exAt (A := A3.A) mu tw h.aux.ex, h.aux.conj, h.aux.levelW, h.aux.integral⟩
  ok := (A3.comap id (f μ)).fam3.comap_ok_of_injective h.ok hf μ
  sep := h.sep

end GlobalTheory.Mem.R3.Res

end
end

