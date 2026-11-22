import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0595
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0129
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0958
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0594
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0083
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0127
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPins
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.SelC
section Gen
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)
end Gen
section Main
variable {B : Base} {X : PreX B.toPre} {I : TC B X}
variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
  {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
  {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX}
def squareIntegrableColumnsOfKernel (hOk : (famC I hX U Xg tr).fam3.Ok3 1) (T : _root_.Formalism.L2.TiedDataSKAlt ex) (hS : I.StdKer l Z T.ker)
    (Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs))
    (R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp)
    (htup : R.I.tup = ixOf I U) (hw : ∀ u, R.I.wU u = u) : _root_.Formalism.L2.DIV.SquareIntegrableColumns T R.extendedDatum where
  X := B.fields
  e := B.tauLL
  c := colRecK h hp l Z ht hJ hX U Xg tr T.ker
  Sp := Sp
  colTie := ⟨rfl, HEq.rfl⟩
  kerTie := by
    obtain ⟨h1, h2, h3⟩ := tup_heq ht U T.ker.X hS.X_eq T.ker.Pr T.ker.sel T.ker.S T.ker.tup T.ker.cst T.ker.idx hS.Pr hS.sel hS.S hS.tup
      hS.cst hS.idx
    rw [← htup] at h1 h2 h3
    exact ⟨hS.X_eq, rfl, hS.Pr.symm, hS.Ch.symm, hS.sel.symm, heq_of_eq hS.S.symm, h1, h2, h3, hS.m2.symm, hS.glob.symm, hS.amb.symm, rfl,
      hS.word.symm⟩
  wTie := fun u => heq_of_eq (hw u)
  lvTie := rfl
  sgTie := rfl
  v0 := InfinitePlace.mk B.embLL
  TU := tuOf I U
  xiVal := xiValOf I
  trIv := tr
  famEq := HEq.rfl
  gEq := rfl
  plEq := rfl
  i0Eq := rfl
  tEq := rfl
  muTie := fun _ => rfl
  ok1 := hOk
section Pins
variable {h hp l Z ht hJ hX U Xg tr} {hOk : (famC I hX U Xg tr).fam3.Ok3 1} {T : _root_.Formalism.L2.TiedDataSKAlt ex} {hS : I.StdKer l Z T.ker}
  {Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)}
  {R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp}
  {htup : R.I.tup = ixOf I U} {hw : ∀ u, R.I.wU u = u}
theorem lamOfCol_colK_eq_lamTrue : _root_.Formalism.L2.DIV.lamOfCol_alt (_root_.GlobalTheory.Mem.R3.SelC.squareIntegrableColumnsOfKernel h hp l Z ht hJ hX U Xg tr hOk T hS Sp R htup hw) = fun u i τ => B.wts.lamTrue u i τ := by
  funext u i τ
  exact congrArg (B.wts.lamTrue u i) (eq_of_heq ((cast_heq _ _).trans (iT_heq l Z hS τ)))
theorem colPins_colK' : _root_.Formalism.L2.DIV.ColumnCharactersCompatible (_root_.GlobalTheory.Mem.R3.SelC.squareIntegrableColumnsOfKernel h hp l Z ht hJ hX U Xg tr hOk T hS Sp R htup hw) where
  grpTie := HEq.rfl
  psTie := ⟨HEq.rfl, HEq.rfl⟩
  pointCharacterEq := ⟨HEq.rfl, HEq.rfl⟩
  wOk := (base_fields_primes_ok B X).2.2.1
  chOk := h.ch_ok
  hcTie := fun u τ => heq_of_eq (congrArg (B.hcW u) (eq_of_heq ((cast_heq _ _).trans (iT_heq l Z hS τ))))
  wtTie := by
    rw [_root_.GlobalTheory.Mem.R3.SelC.lamOfCol_colK_eq_lamTrue]
    exact ⟨_, _, wtTie_base I l Z T.ker⟩
  xgTie := fun χ => @mem_iff_XgE _ _ _ _ _ _ _ _ (_) B.embLL R.I.eG _ Xg hOk.ok2.irr R.tied.div.grp.e0 χ
  qNF := fun t => of_forall_ix ht (fun _ _ L => GlobalTheory.QNF.IdxMatNF L) (RcHyp.idxMatNF_of_isTw I h ht) t
  columnEvaluationOk := ⟨rowG_ok (Pr := B.primes X) B.wts I.Ch I.sel _ hX I.Ps (Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := B.fields) (S := I.S) I.sel), fun u => by
    have H := exists_read_fam (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr
      I.Ps hOk.ok2 B.embLL (rowG_ok (Pr := B.primes X) B.wts I.Ch I.sel _ hX I.Ps (Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := B.fields) (S := I.S) I.sel))
      (A := (I.rec7 l Z).what₂.Amb) ((I.rec7 l Z).eMt u) R.I.tup R.tied.div.tup.mu0 R.tied.div.tup.inj R.I.jA
      (fun t => (R.tied.div.sharp.forms t).li) (fun t => (R.tied.div.sharp.forms t).span) R.Zs
    exact H⟩
end Pins
end Main
set_option maxHeartbeats 1000000 in
theorem exists_rowsKC_colPins_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL))
    (tr : TrI B X) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z))
    (Kc : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX),
    (famC I hX U Xg tr).fam3.Ok3 1 → ∀ (T : _root_.Formalism.L2.TiedDataSKAlt ex), I.StdKer l Z T.ker →
    ∀ (Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)) (P : Formalism.L2.Rows.RowSideFamily ex),
    P.Gp = Gc B X → HEq P.grp (inferInstance : Group (Gc B X)) → P.Pl0 = PlS B X → P.I0 = PlI B X → P.T = TupU I U →
    HEq P.A3 (famC I hX U Xg tr) → HEq P.P0 (lev0 I) → HEq P.ψ0 (chr0 I) → HEq P.Ps (lev1 I) → HEq P.ψs (chr1 I) →
    HEq P.I.tup (ixOf I U) → (∀ u, HEq (P.I.wU u) u) →
    ∀ Zs : DefSub (famC I hX U Xg tr).fam3.amb3, HEq P.Zs Zs → HEq P.Dc ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs) →
    HEq P.Sp (Sp Zs) →
    ∃ K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P, _root_.Formalism.L2.DIV.ColumnCharactersCompatible K ∧ HEq K.c (colRecK h hp l Z ht hJ hX U Xg tr T.ker) ∧ HEq K.Sp Sp ∧ HEq K.c.W B.wts ∧
      HEq (fun Zs => K.c.face Zs) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face ∧ HEq K.c.Xg Xg := by
  intro B X I h hp l Z ht hJ hX U Xg tr L hT Gi Gl Kc Y cX ex hOk T hS Sp P
  obtain @⟨Gp, grp, fin, Pl0, I0, Tt, A3, P0, ψ0, Ps, ψs, Zs', S0, S1, Dc, Sp', C, NuC, J, JA, JM, tied⟩ := P
  intro e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 Zs e13 e14 e15
  dsimp only at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  subst e1 e3 e4 e5
  obtain rfl := eq_of_heq e2
  obtain rfl : fin = fintype_GLs B.fields.E (B.primes X).vGs B.R.r := Subsingleton.elim _ _
  cases e6
  cases e7
  cases e8
  cases e9
  cases e10
  cases e13
  cases e14
  cases e15
  exact ⟨_root_.GlobalTheory.Mem.R3.SelC.squareIntegrableColumnsOfKernel h hp l Z ht hJ hX U Xg tr hOk T hS Sp ⟨Zs, S0, S1, C, NuC, J, JA, JM, tied⟩ (eq_of_heq e11) fun u => eq_of_heq (e12 u),
    _root_.GlobalTheory.Mem.R3.SelC.colPins_colK', HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
end GlobalTheory.Mem.R3.SelC
end
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.Mem.R3.SelC
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
set_option maxHeartbeats 1000000 in
theorem jA_row_alt {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) (r : RXs t) (pin : ColPin w)
    (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (w.D Z) 𝔞 → χ 𝔞 = w.I.chi 𝔞) (a : w.I.ι) (ha)
    (j : (Fin (rDim (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩) → B.LL) → Z.W.Amb a)
    (hj : SameOn (r.all.jA a) j) (Zs : DefSub (famT t).fam3.amb3)
    (F : Fin (((famT t).side3 (lev1 w.I) (chr1 w.I) Zs).nV ⟨w.I.tup a, ha⟩) → B.LL) :
    ∃ z : GlobalTheory.Core.Ht2.RowsK w.I a,
      z.1 = ((colRecC w.ok w.pins w.l Z pin.isTw pin.jets χ hχ t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).ev Zs ⟨w.I.tup a, ha⟩ F).1.1 ∧
      j ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩).mulVec F) = r.e a (Df.toCx w.I t.hX a z) := by
  obtain ⟨z, ⟨F', hF', e1, e2⟩, e3⟩ := r.crd a ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩).mulVec F)
  have e4 := evC_res_lvl (X := B.fields) (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel t.hX (InfinitePlace.mk B.embLL)
    (tuOf w.I (usedOf w.I T Wt)) t.r.z.Xg ∅ (xiValOf w.I) t.r.z.tr (TC.Ps w.I) t.r.intersectionNumber_baseChange.ok.ok2 Zs ⟨w.I.tup a, ha⟩ F
  have e5 := LinearEquiv.injective _ (eq_of_heq (e1.trans (heq_of_eq e4.symm)))
  refine ⟨z, ?_, (hj.2 _ _ fun i i' e => congrArg _ (Fin.ext e)).symm.trans e3⟩
  rw [e2]
  exact congrArg Subtype.val e5
variable {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
set_option maxHeartbeats 1000000 in
theorem exists_readC_wU_eq_id (t : RowsT K w Z Wt ex.p0) (r : RXs t) (pin : ColPin w) (k : Formalism.L2.Ker.KerEntTied ex) (Sp Zsc) :
    ∃ C : ReadC t.r.z.R (reFace t.r.z.F
      (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr k).face Sp Zsc) ex.p0 t.r.Y,
      C.wU = fun u => u := by
  choose e he hn using exists_eNu w.ok w.l Z t.hX w.l0
  refine ⟨{ wU := fun u => u
            bij := Function.bijective_id
            eNu := e
            NuC := fun u => (Z.V.div.Nu u).L.comap ((e u).toLinearMap.restrictScalars (𝓞 B.LL))
            nu := fun u => ⟨(Submodule.map_comap_eq_of_surjective (f := (e u).toLinearMap.restrictScalars (𝓞 B.LL)) (e u).surjective _).symm, he u⟩
            pt := fun u s x F => ?_ }, rfl⟩
  have key : ∀ (a : w.I.ι) (s : TupU w.I (usedOf w.I T Wt)) (_ : w.I.tup a = s.1)
      (j : (Fin (rDim (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) s) → B.LL) → Z.W.Amb a) (_ : SameOn (r.all.jA a) j)
      (Zs : DefSub (famT t).fam3.amb3) (F : Fin (((famT t).side3 (lev1 w.I) (chr1 w.I) Zs).nV s) → B.LL),
      B.embLL (((colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr k).face Zs).Pt u s x F) =
        Z.W.perCol u a (Z.V.jN u (e u x)) (j ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) s).mulVec F)) := by
    rintro a ⟨τ, ha⟩ (rfl : w.I.tup a = τ) j hj Zs F
    obtain ⟨z, hz, e1⟩ := _root_.GlobalTheory.Mem.R3.SelC.jA_row_alt t r pin k.χ (ker_chi_eq w.I w.l Z k) a ha j hj Zs F
    rw [e1]
    exact face_pt w.ok w.pins w.l Z pin.isTw pin.jets k.χ (ker_chi_eq w.I w.l Z k) t.hX w.l0 r.e r.eMt0 r.eMtTw _ _ _ Zs u a ha x _
      (hn u x) F z hz
  exact key (t.r.Y.tup s) s ((congrArg w.I.tup (t.r.tup_ix s)).trans (tup_ixOf w.I s)) (t.r.Y.jA s) (r.jA_use s) _ F
set_option maxHeartbeats 400000 in
theorem args_pinned_heq_zsOf_mem_eq (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) :
    (a.x.G = Gc B w.px ∧ HEq a.x.grp (inferInstance : Group (Gc B w.px)) ∧ a.x.Pl0 = PlS B w.px ∧ a.x.I0 = PlI B w.px ∧
      a.x.T = TupU w.I (usedOf w.I T Wt) ∧ HEq a.x.A3 (famC w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr)) ∧
    (HEq a.x.F.P0 (lev0 w.I) ∧ HEq a.x.F.ψ0 (chr0 w.I) ∧ HEq a.x.F.P1 (lev1 w.I) ∧ HEq a.x.F.ψ1 (chr1 w.I) ∧ HEq a.x.F.Dc a.Dc ∧
      HEq a.x.F.Sp a.Sp) ∧
    ∃ Zs : DefSub (famT t).fam3.amb3, HEq (zsOf a.x.R a.x.F) Zs ∧ HEq (a.x.F.Dc (zsOf a.x.R a.x.F)) (a.Dc Zs) ∧
      HEq (a.x.F.Sp (zsOf a.x.R a.x.F)) (a.Sp Zs) ∧ (a.x.F.Dc (zsOf a.x.R a.x.F)).Mem = (a.Dc Zs).Mem :=
  ⟨by kexactB (@pack_heq (w.st Z).toD7 _ _ a.pack).1, by kexactB (@pack_heq (w.st Z).toD7 _ _ a.pack).2.1,
    zsOf ((t.r.z.R.updS t.r.z.R.kap a.lam).withErr a.err) (reFace t.r.z.F a.Dc a.Sp a.Zsc),
    by kexactB (@pack_heq (w.st Z).toD7 _ _ a.pack).2.2⟩
set_option maxHeartbeats 400000 in
theorem exists_square_integrable_columns_of_data (t : RowsT K w Z Wt ex.p0) (pin : ColPin w) (S : _root_.Formalism.L2.TiedDataSKAlt ex) (hS : TC.StdKer w.I w.l Z S.ker)
    (a : TwArgs ex t) (hD : a.Dc = (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face)
    (hw : HEq a.x.C.wU fun u : B.Word => u) :
    ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns S (divisionPairOfAdelicFormsFaceColumnsData a.x), HEq (fun Zs => C.c.face Zs) a.x.F.Dc ∧ HEq C.Sp a.x.F.Sp ∧ HEq C.c.W B.wts ∧
      HEq C.c.Xg t.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, g11, g12⟩, Zs, g13, g14, g15, g16⟩ := _root_.GlobalTheory.Mem.R3.SelC.args_pinned_heq_zsOf_mem_eq t a
  obtain ⟨Sp, hSp⟩ : ∃ Sp : ∀ Zs, SPer ((colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face Zs),
      HEq a.Sp Sp ∧ ∀ Zs, HEq (a.Sp Zs) (Sp Zs) := by
    have key : ∀ Dc : type_of% a.Dc, a.Dc = Dc → ∃ Sp : ∀ Zs, SPer (Dc Zs), HEq a.Sp Sp ∧ ∀ Zs, HEq (a.Sp Zs) (Sp Zs) := by
      rintro _ rfl
      exact ⟨a.Sp, HEq.rfl, fun _ => HEq.rfl⟩
    exact (key (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face hD)
  have e1 := congrFun hD Zs
  have e2 : (a.x.F.Dc (zsOf a.x.R a.x.F)).Mem = B.Word := by kexactB g16.trans (congrArg DefCols.Mem e1)
  have e3 : HEq a.x.Y.tup (ixOf w.I (usedOf w.I T Wt)) := by kexactB a.tup.trans (heq_of_eq (funext t.r.tup_ix))
  have e4 : ∀ u, HEq (a.x.C.wU u) u := fun u => heq_app e2 hw u
  have e5 := g14.trans (heq_of_eq e1)
  have e6 := g15.trans (hSp.2 Zs)
  obtain ⟨C, c1, -, c3, c4, c5, c6⟩ := _root_.GlobalTheory.Mem.R3.SelC.exists_rowsKC_colPins_alt w.I w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr
    L hT Gi Gl Kc Yd cX ex t.r.intersectionNumber_baseChange.ok S hS Sp (divisionPairOfAdelicFormsFaceColumnsData a.x) ((h1)) ((h2)) ((h3)) ((h4)) ((h5))
    ((h6)) ((h7)) ((h8)) ((h9)) ((h10)) ((e3)) ((e4)) Zs ((g13))
    ((e5)) ((e6))
  have d1 := (heq_of_eq hD.symm).trans g11.symm
  refine ⟨_root_.GlobalTheory.Cp.SquareIntegrableColumns.ofS C, HEq.trans (b := (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face)
    ?_ ?_, ?_, ?_, ?_, ?_⟩
  · exact (c5)
  · exact (d1)
  · kexactB c3.trans (hSp.1.symm.trans g12.symm)
  · exact (c4)
  · exact (c6)
  · exact (c1)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem square_integrable_columns_of_witnesses : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex), KPin q t → Nonempty (RXs q.x.what₂) → ∃ Dc Sp₀ Zsc₀, ∃ C₀ : ReadC q.x.what₂.r.z.R (reFace q.x.what₂.r.z.F Dc Sp₀ Zsc₀) q.O.ex.p0 ((q.x.what₂.r.Y)), ∀ (T : _root_.Formalism.L2.TiedDataSKAlt q.O.ex), T.ker = t → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → a.Dc = Dc → HEq x.C.wU C₀.wU → HEq x.C.eNu C₀.eNu → ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS := by
  intro 𝒮 K q t hk ⟨r⟩
  obtain ⟨C₀, hC⟩ := _root_.GlobalTheory.Mem.R3.SelC.exists_readC_wU_eq_id (ex := q.O.ex) q.x.what₂ r q.x.pin t (fun _ => ⟨ℂ, inferInstance, inferInstance, fun _ => 0, ⊥⟩)
    q.x.what₂.r.z.F.Zsc
  refine ⟨_, _, _, C₀, fun S hS a x hx hD hw _ => ?_⟩
  subst hS
  cases hx
  exact _root_.GlobalTheory.Mem.R3.SelC.exists_square_integrable_columns_of_data (ex := q.O.ex) q.x.what₂ q.x.pin S hk.std a hD (hw.trans (heq_of_eq hC))
end GlobalTheory.Mem.R3.SelC
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrsFMemGlintRedVEq
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
namespace GlobalTheory.Fam.LevelFrames
set_option maxHeartbeats 1000000 in
theorem frsF_mem_glint_redV_eq_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (j : ℕ), j + 1 ≤ B.R.m → ∀ (β : J.Ch₀ j) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
    Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1 ∧
    ∀ x ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N j) P.1, Formalism.L2.Col.redV P.1 (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P x) = Formalism.L2.Col.redV P.1 x := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ n t J hJ j hj β P hP
  letI := GlobalTheory.Mem.Col2.starE B
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  refine ⟨?_, fun x hx => redV_eq_of_near (fun r s => ?_) hx⟩
  · have e : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P = (J.A.p0 j β).1.1.deco.1.liftFr ⟨P.1, hPv⟩ :=
      dif_pos hPv
    have h := (GlobalTheory.TopStep.liftFr_spec (J.A.p0 j β).1.1.deco.2 ⟨P.1, hPv⟩).1
    have hN := (hJ.is.base j (by omega) β).2
    rw [e]
    intro x
    refine Iff.trans ?_ (h x)
    exact Iff.of_eq (congrArg (fun N => _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N) hN.symm)
  · rcases hj.eq_or_lt with h | h
    · exact _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ P hPv h β r s
    · have key := MidLoc.frame_cong hW.tr.ok (J.A.p0 j β).1.1 (hJ.std j h β ▸ (hJ.is.base j (by omega) β).1) P hPv r s
      rwa [if_congr Fin.ext_iff rfl rfl] at key
end GlobalTheory.Fam.LevelFrames
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTailStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclF_of_family_facts_and_bound_at_two_three : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C : ℝ) (CT : ℕ), 0 ≤ C → TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm → ConclF Fm := by
  first | exact @_root_.GlobalTheory.NLinkClose.main_alt_alt | exact _root_.GlobalTheory.NLinkClose.main_alt_alt | (intros; apply _root_.GlobalTheory.NLinkClose.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InGeoGeoHalfStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inGeo_half_of_ratHyp0 : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p → ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m), RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j → InGeo (geoHalf p) := by
  first | exact @_root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 | exact _root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 | (intros; apply _root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointOfFamAllQ
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
theorem joint_of_famAllQ_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.FamilyAllConditions W → _root_.GlobalTheory.MiTop.FamilyServedCondition W → _root_.GlobalTheory.MiTop.JointCondition W := by
  intro hCusp hHC D L hT Gi Gl Kc Yd cX ex W hFam hServ
  obtain ⟨z, hz, hzc, hu⟩ := hFam
  refine ⟨z, hz, hzc, fun u => ?_⟩
  obtain ⟨f, d, hPin, hLaws, hZ, hTail, hDown, hOnto, hComm, hRat⟩ := hu u
  have hMain : MainX f.t := GlobalTheory.T.seesawTransportRelations_of_familyLaws hCusp hHC D _ _ f.t hLaws
  obtain ⟨U, r, c, hr, hU, hc, hRel⟩ :=
    _root_.GlobalTheory.MiTop.rel_of_links_alt W u f d hLaws.tup hMain hZ hTail hDown hOnto hComm hRat hServ
  exact ⟨d, U, r, c, hPin, hr, hU, hc, hRel⟩
end GlobalTheory.MiTop
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapTStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_kap_le_and_lenT_mul_le_sqrt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => Real.log (kap p i) ≤ 2 * (Fm.L x ι).sc.L ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt (Fm.L x ι).sc.b := by
  first | exact @_root_.GlobalTheory.CovTop.CovSz.kapT_alt | exact _root_.GlobalTheory.CovTop.CovSz.kapT_alt | (intros; apply _root_.GlobalTheory.CovTop.CovSz.kapT_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LawsRescStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_family_final_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), (a.fam row col).RowOK → (a.fam row col).ColOK →
    ∀ t (F : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) (w₀ : VTup ((a.fam row col).t t)) (s : ∀ j, (col t).Ch j → ℂ),
    (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) → F.Pins w₀ →
    (∀ p, p ∈ w₀.Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F)) →
    QLaw a.v (GlobalTheory.QTw.resc w₀ s) ∧ QLast a.v (GlobalTheory.QTw.resc w₀ s) ∧ QFin a.v (GlobalTheory.QTw.resc w₀ s) := by
  first | exact @_root_.GlobalTheory.QColLaws.laws_resc_alt | exact _root_.GlobalTheory.QColLaws.laws_resc_alt | (intros; apply _root_.GlobalTheory.QColLaws.laws_resc_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftGapsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_antitone_boundary' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => 1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  first | exact @_root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ | exact _root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ | (intros; apply _root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LineIdealAtTStatement
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
theorem _root_.GlobalTheory.T.placed_bessel_pair_vector_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP.under (𝓞 D.host.F) ≠ v) → ((((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f'.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v)) := by
  first | exact @_root_.GlobalTheory.MiTop.line_ideal_atT_alt | exact _root_.GlobalTheory.MiTop.line_ideal_atT_alt | (intros; apply _root_.GlobalTheory.MiTop.line_ideal_atT_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MidLocFac
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MidLoc
theorem mid_locFac_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 2 < B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat n j hj hj2
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain ⟨c, H⟩ : ∃ c, j + 1 + c = (a.G n).s := ⟨(a.G n).s - (j + 1), by omega⟩
  have hR := (ha.tie (fun t => (nonempty_rowCh (_root_.GlobalTheory.Fam.complexLevelStructure W) hW.pk.bot.hyp.2.2.2.1.chain u a.g t).some)
    fun t => (nonempty_colCh (D := I.rec7 l Z) u _).some).2
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.Fam.MidLoc.locXi_eq_mul_midXi_alt hW ha hR n (_root_.GlobalTheory.T.true_geometry_line_choice_value W hW u a _ _ hR n) j c H hj
  exact ⟨C, hC0, fun t J hJ α γ => ⟨_root_.GlobalTheory.Fam.MidLoc.intermediateXiValue a n j c H, _root_.GlobalTheory.Fam.MidLoc.midXi_isLocFac' ha hat hR n j c H, hC t J hJ α γ⟩⟩
end GlobalTheory.Fam.MidLoc
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParametersScaleRankGapBoundsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_dimension_log_bound' : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → |(ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| * (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) - (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) τ : ℝ)|) + (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) + ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd (Fm.D x ι).host.E| ≤ C * unitE p := by
  first | exact @_root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds | exact _root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds | (intros; apply _root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatAtUpperStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_ratAt_le_mul_unitE : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) → Closed FamHyp fun Fm _ => ∃ K : ℝ, 0 ≤ K ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun _ _ _ p => ∀ i, 0 < ratAt p i ∧ Real.log (ratAt p i) ≤ K * unitE p := by
  first | exact @_root_.GlobalTheory.CovTop.MeasRd.ratAt_upper_alt | exact _root_.GlobalTheory.CovTop.MeasRd.ratAt_upper_alt | (intros; apply _root_.GlobalTheory.CovTop.MeasRd.ratAt_upper_alt <;> assumption)
end
end

