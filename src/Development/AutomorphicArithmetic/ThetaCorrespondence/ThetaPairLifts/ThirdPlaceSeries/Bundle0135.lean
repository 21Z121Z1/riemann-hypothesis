import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0598
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0075
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0129
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0130
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0731
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0720
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseUpperBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0376
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CosetLevelEqOfReads
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLevTyp
section Main
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
set_option maxHeartbeats 2000000 in
theorem cosetIn_p0_eq_of_reads (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 1 = B.R.m) {t t' : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.Reads)
    (α : J.Ch j) {J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'} (hJ' : J'.Reads) (α' : J'.Ch j) (w : (B.primes X).vGs) :
    cosetIn (J.A.p0 j (J.ι j α)) ⟨w.1, Finset.mem_union_left _ w.2⟩ =
      cosetIn (J'.A.p0 j (J'.ι j α')) ⟨w.1, Finset.mem_union_left _ w.2⟩ := by
  obtain ⟨n, hn⟩ := a.pl.surjective ⟨w.1, (hW.lev.2.1 _).2 w.2⟩
  have hP : w.1 = (a.pl n).1 := by rw [hn]
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain rfl : j = (a.G n).s + 1 := by omega
  have hint : ∀ x : B.fields.E, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt w.1 x := by
    have hR := (ha.tie (fun t => (TopLocFac.nonempty_rowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g hTr.pinX.std t).some)
      fun t => (TopLocFac.nonempty_colCh _ _).some).2
    rw [hP]
    exact (GlobalTheory.LocMod.PinEx.place_facts _ (hR.idem n).1).2.1
  have hqv : HeightOneSpectrum.valuation B.fields.E w.1 (Formalism.L2.Col.qOf w.1 : B.fields.E) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨i, g1, -, -, g4, -⟩ := GlobalTheory.SeeSaw.LevelData.type_prime w.2
    exact GlobalTheory.AtTypeExists.valuation_norm w.1 (g1 ▸ g4)
  obtain ⟨e, he⟩ := exists_xOrd B.R ((a.G n).s + 1)
  have key : ∀ {t : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (_ : J.Reads) (α : J.Ch ((a.G n).s + 1)), ∃ z : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1)),
      cosetIn (J.A.p0 _ (J.ι _ α)) ⟨w.1, Finset.mem_union_left _ w.2⟩ =
        {z' | z' - z ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N ((a.G n).s + 1)) w.1} ∧
      ∀ r, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (z (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k] := by
    intro t J hJ α
    refine ⟨_, (coset_at (J.A.p0 _ (J.ι _ α)) hj ((J.A.p0 _ (J.ι _ α)).repY_mem hj) w).1, fun c => ?_⟩
    have hF := _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2 hj (J.ι _ α)
    have hq := TopFrames.intAt_q_mul (A := J.A) ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2 hj (J.ι _ α)
    have hco := hJ.cosG n α e he c
    have hfr : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ α)).1.1 ⟨w.1, Finset.mem_union_left _ w.2⟩ =
      (J.A.p0 _ (J.ι _ α)).1.1.deco.1.liftFr w := dif_pos w.2
    rw [hfr] at hF hq
    generalize (J.A.p0 _ (J.ι _ α)).1.1.deco.1.liftFr w = f at hF hq ⊢
    generalize Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2 = y at hq hco ⊢
    have h1 := (hint _).2 (TopFrames.intAt_sub_of_near hqv hF hq (e c))
    rw [LinearEquiv.apply_symm_apply, map_sub] at h1
    have h2 : _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y (e c)) - (a.G n).S.y0 (Fin B.R.t) c ∈ 𝒪[(a.G n).k] := hco
    have h3 := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at h3
  obtain ⟨z, hz, h1⟩ := key hJ α
  obtain ⟨z', hz', h1'⟩ := key hJ' α'
  have hd : z - z' ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N ((a.G n).s + 1)) w.1 := by
    refine GlobalTheory.TopStep.mem_stdAt.2 fun i => ?_
    obtain ⟨r, rfl⟩ := e.surjective i
    have h := sub_mem (h1 r) (h1' r)
    rw [sub_sub_sub_cancel_right, ← map_sub] at h
    exact (hint _).1 h
  rw [hz, hz']
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have := add_mem h hd
    rwa [sub_add_sub_cancel] at this
  · intro h
    have := sub_mem h hd
    rwa [sub_sub_sub_cancel_right] at this
set_option maxHeartbeats 2000000 in
theorem mem_UAd_iff_of_not_plF (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 1 = B.R.m) [NeZero (B.R.N j)] {t : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t}
    (hJ : J.Reads) (β : J.Ch₀ j) (v : HeightOneSpectrum (𝓞 B.host.F)) (hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal)
    (hv : ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v) (x : TC.GA B (B.R.N j)) (hxU : x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j))
    (hx : ∀ w, w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) w) x = 1) :
    x ∈ (J.A.K j (show j ≤ B.R.m by omega) β).lev.U ↔
      x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
      (GlobalTheory.Mem.Col2.MemChart.chG (X := B.fields) (Formalism.L2.Col.colLevSym I.Ch j) (GlobalTheory.Mem.Col2.MemChart.bar (J.A.p0 j β))) := by
  have hm : j ≤ B.R.m := by omega
  obtain ⟨c, rfl⟩ := (hJ.is.reads j hm).onto β
  have h6 := (TrueColsTest.kStd_spec X u (B.R.N j)).2.1 v hT
  have hk : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (J.A.kb j (J.A.chOf j c)) = 1 := by
    obtain ⟨k₀, h, -, h1, h2, h3, -⟩ := hJ.pen j hj (J.A.chOf j c)
    have h5 := TopFrames.finM_map_prV _ (rankN (I.rec7 l Z) j hm) h3 hv
    refine Units.ext ?_
    have h7 := (hJ.is.kA j hm (J.A.chOf j c)).2.1
    rw [h2, GlobalTheory.AdForm.Model.finM_mul, h1] at h7
    have h8 : (J.A.kb j (J.A.chOf j c)).1.map (Formalism.UG.prV (E := B.host.E) v) = 1 := by
      rw [← h7]
      refine Matrix.map_mul.trans ?_
      have h6' : (TC.kStd X u (B.R.N j)).1.map (Formalism.UG.prV (E := B.host.E) v) = 1 := congrArg Units.val h6
      exact (congrArg₂ (fun x y : Matrix (Fin (B.R.N j)) (Fin (B.R.N j))
        (B.host.E ⊗[B.host.F] v.adicCompletion B.host.F) => x * y) h6' h5).trans (one_mul _)
    exact h8
  have h1 : ∀ P ∈ I.Q (W.P.I.tup t), x.1.map (GlobalTheory.Mem.Col2.adAt B.host.F P) = 1 := fun P hP => by
    refine GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV P (hx _ fun h => hv ?_)
    obtain ⟨i, hi⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
    exact ⟨i, (((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i).trans (congrArg _ hi)).trans h⟩
  refine (mem_lev_iff I hW.tr.ok hW.tr.tw l.pr u _ j hj (hJ.is.reads j hm) c x hxU (commute_of_off hx hk)
    (commute_of_off hx h6) h1).trans ?_
  have hb : GlobalTheory.Mem.Col2.MemChart.bar (show PtAt B.R I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) u j from
      (I.stp u (W.P.I.tup t) j).rep c) = GlobalTheory.Mem.Col2.MemChart.bar (J.A.p0 j (J.A.chOf j c)) := funext fun w =>
    (cos_iff_bar hj w (GlobalTheory.Mem.Col2.MemChart.hqG l.pr w.1 w.2) _ _).1 (congrFun (hJ.is.rep j hm c).2 _)
  exact Iff.of_eq (congrArg (fun C => x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
    (GlobalTheory.Mem.Col2.MemChart.chG (X := B.fields) (Formalism.L2.Col.colLevSym I.Ch j) C)) hb)
end Main
set_option maxHeartbeats 2000000 in
theorem uloc_le_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' v → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' v _ hTv hv hv'
  have hm : j ≤ B.R.m := by omega
  haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
  obtain ⟨hPins⟩ := hW.tr.pins
  have hg1 : gramN (I.rec7 l Z) j hm = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hW.tr.ok hPins l Z).2.2.2 j hm).1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hm) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := by rw [hg1]; rfl
  refine GlobalTheory.stepLevel_uloc_le_of_agree _ _ {w | w ≠ v} (fun x hx hxU => ?_) v (fun h => h rfl)
  have hxA : x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := eU ▸ (((J.A.K j hm (J.ι j α)).lev.U_eq x).1 hxU).1
  have hb : GlobalTheory.Mem.Col2.MemChart.bar (J.A.p0 j (J.ι j α)) = GlobalTheory.Mem.Col2.MemChart.bar (J'.A.p0 j (J'.ι j α')) := funext fun w =>
    (cos_iff_bar hj w (GlobalTheory.Mem.Col2.MemChart.hqG l.pr w.1 w.2) _ _).1 (_root_.GlobalTheory.PenLevTyp.cosetIn_p0_eq_of_reads hW ha hTr j hj hJ α hJ' α' w)
  have h1 := (_root_.GlobalTheory.PenLevTyp.mem_UAd_iff_of_not_plF hW ha hTr j hj hJ (J.ι j α) v hTv hv x hxA hx).1 hxU
  rw [hb] at h1
  exact (_root_.GlobalTheory.PenLevTyp.mem_UAd_iff_of_not_plF hW ha hTr j hj hJ' (J'.ι j α') v hTv hv' x hxA hx).2 h1
end GlobalTheory.PenLevTyp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAtTypeTopStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_pair_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 1 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  first | exact @_root_.GlobalTheory.Fam.TopLoc.loc_top_common_alt | exact _root_.GlobalTheory.Fam.TopLoc.loc_top_common_alt | (intros; apply _root_.GlobalTheory.Fam.TopLoc.loc_top_common_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsParamsAtMem
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2
open Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField GlobalTheory.EX GlobalTheory.EX.OB
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SizePar
theorem exists_params_atMem_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L) := by
  refine (evG_of_ev GlobalTheory.PrimIn.AtData.ev_params).imp fun K _ _ _ _ hK => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B f T hO _ _ _ _ w Z Wt p0 t nch n xd c _ _ _ => ?_⟩
  obtain ⟨L, -, -, hp, -⟩ := hK (w.st Z) hO t.etaF fun v hv j h1 h2 => by
    have key : ∀ v', (w.D Z).what₂.muAt v' = (w.D Z).what₂.mu0 → v' ∉ Wt := by
      intro v' he hw
      have he' : (w.st Z).W.muAt v' = (w.st Z).C.mu0 := he
      rw [t.mu.on v' hw] at he'
      have h1 := t.mu.tw v'
      rw [he', t.mu.mu0] at h1
      exact (TwFin.tw_fin B f T).2.1 v' h1.symm
    change (w.D Z).what₂.Aj j v = 0
    replace hv : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 := hv
    have a := t.untw v (key v hv) j h1 h2
    have b := t.untw _ (key _ (((w.D Z).what₂.muAt_conj v).trans hv)) j h1 h2
    unfold Formalism.BasicNotions.Rows.Data.Aj
    rw [hv, a.1, a.2, b.1]
    rfl
  exact ⟨L, hp⟩
end GlobalTheory.HeightCounting.Up.SizePar
namespace GlobalTheory.HeightCounting.Up.SizePar
end GlobalTheory.HeightCounting.Up.SizePar
namespace GlobalTheory.HeightCounting.Up.SizePar
theorem exists_params_alt :
    (∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧
      AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧
        ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) :=
  ⟨_root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_atMem_alt, exists_params_allSt⟩
end GlobalTheory.HeightCounting.Up.SizePar
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPinsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_integrable_columns_of_heq_data : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex), KPin q t → Nonempty (RXs q.x.what₂) → ∃ Dc Sp₀ Zsc₀, ∃ C₀ : ReadC q.x.what₂.r.z.R (reFace q.x.what₂.r.z.F Dc Sp₀ Zsc₀) q.O.ex.p0 ((q.x.what₂.r.Y)), ∀ (T : _root_.Formalism.L2.TiedDataSKAlt q.O.ex), T.ker = t → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → a.Dc = Dc → HEq x.C.wU C₀.wU → HEq x.C.eNu C₀.eNu → ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS := by
  first | exact @_root_.GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses | exact _root_.GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses | (intros; apply _root_.GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeries
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseCmp
open GlobalTheory.FlatVecSum (princ princ_good)
section Real
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle}
  {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ}
end Real
section Coef
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}
end Coef
section Move
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
end Move
section Read
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {X : Type} (rd : M →ₛₗ[eK] (X → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end Read
end GlobalTheory.BaseCmp
namespace GlobalTheory.BigOn.Exp
open Formalism.MainNotions.DIV.Cons Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.BaseCmp
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem core_of_rows_alt (hr : p.PointConditions') : GlobalTheory.Hk3.Core p.R.toRealDat p.F.lv2 :=
  have hc := RealDat3.characterisation_of_weak p.charW hr.exAt
  ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
theorem exists_series_alt (hr : p.PointConditions') (hm : RecTies p) (hw : D.plEq w ∈ p.R.twPl) {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ}
    (hf : Fit p w j hρ ν) (O' : Subring ℂ) (hO' : ∀ a : 𝓞 D.what₂.LL, D.what₂.embLL a ∈ O') {ω φ}
    (hk : IsKernel p.R.toRealDat j (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc (D.plEq w)))
      (GlobalTheory.OnTies.placesOver p.R.toRealDat (p.R.mu (D.plEq w)) (ownAt D (D.plEq w))) ω φ) {x}
    (hx : x ∈ seriesSet p.R.toRealDat j p.P.P0 p.P.ψ0⁻¹ 1 ω φ) :
    ∃ (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) (ζ : ℂ) (n : ℕ),
      IsIntegral ℤ (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ n * ζ) ∧
      P ∈ Submodule.span O' {Q | ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q} ∧
      ν⁻¹ • adForm p.R.toRealDat j x (p.v₀ j _) = ζ • ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P := by
  classical
  have hC := _root_.GlobalTheory.BigOn.Exp.core_of_rows_alt hr
  have hp := hf.pin
  set i := ex.nch.twI w with hi
  set b := ex.nch.sd w with hb
  have hB := hρ.base i j b
  have hBo := baseOf_of_realPin hρ hp i j b
  have hl : D.ntw.l i = Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := (ex.nch.twI_l w).trans (GlobalTheory.Mem.Top.Bl.resChar_eq_plc D w)
  have hpD : ∀ P, P ∈ D.ntw.pD i ↔ ((ownAt D (D.plEq w) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := fun P => by
    rw [← Finset.mem_coe, D.ntw.pD_eq, hl]
    rfl
  have hQ : GlobalTheory.OnTies.placesOver p.R.toRealDat (p.R.mu (D.plEq w)) (ownAt D (D.plEq w)) = (ρ.B i j b).de.Q :=
    Finset.ext fun P => by
      rw [(placesAt hw hρ hp).1 P, GlobalTheory.OnTies.placesOver, Finset.mem_filter, hpD]
  obtain ⟨χ, ξR, hK⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D _ _ _ _ _ p.R.toRealDat _ hC j _ hw p.charW.tup.mu_on ω φ hk
  rw [hQ] at hK
  have hN : ownAt D (D.plEq w) ≠ 0 := by
    unfold ownAt
    split_ifs
    exacts [D.host.pde'_prime.ne_zero, D.host.pde_prime.ne_zero]
  obtain ⟨k, hkf, c, m, hc, H⟩ := exists_trace_eq hC p.qGuard (GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j)) hB hBo hK
    (hl ▸ hp.delta i j b) ⟨_, fun P h => (((placesAt hw hρ hp).1 P).1 h).1⟩ hN
    (fun P h => (hpD P).1 (((placesAt hw hρ hp).1 P).1 h).2) p.P.P0 p.P.ψ0⁻¹ ((p.R.eG.trans p.cG).trans (ρ.eG i j b))
    (fun g P h h' a c => by
      have e := hp.grp i j b (p.cG (p.R.eG g)) P h h' a c
      rw [MulEquiv.symm_apply_apply] at e
      exact e)
    (mem_level_iff hm hf.level i j b)
    (fun u hu => by
      refine (level_chi hm hρ hf.level i j b u hu).1.trans ?_
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀])
    (hρ.weil_base i j b)
  obtain ⟨h, hh, y, hy, hx⟩ := hx
  obtain ⟨hy', hs⟩ := H h y hy
  obtain ⟨hν, c₀, ⟨gramR, c0R, c0L, hT, u, hu, hsc⟩, n₀, hn₀, hpow⟩ := hf.norm
  rw [p.phsOne, map_one, one_mul] at hpow
  have hc₀ : c₀ ≠ 0 := fun h0 => hν (pow_eq_zero_iff hn₀ |>.1 (by rw [hpow, h0, zero_pow hn₀]))
  obtain ⟨cc, hcc, hbij, -⟩ := GlobalTheory.CoefExtC.exists_extC_bijective_unique D _ _ _ _ p.T p.R.toRealDat _ p.κ p.v₀ hC ⟨p.fw⟩ j _ _
    (p.O j) (p.pins j).2
  obtain ⟨-, -, hval, -⟩ := GlobalTheory.CoefLatConj.exists_coef_scale D _ _ _ _ p.T p.R.toRealDat _ p.κ p.v₀ p.O hC ⟨p.fw⟩ hr.ioExt j
    (p.pins j) cc hcc u hu _ hB hBo
  have hmem := mem_span_coefLat hC hBo ⟨gramR, c0R, hT⟩ (p.R.ioP j (PiTensorProduct.tprod ℂ u))
    (fun z => by obtain ⟨z, rfl⟩ := hbij.2 z; exact hval z) hc₀ hsc (ρ.eO i b).range O' hO' hy'
  obtain ⟨s, h', T, ζ, hζ, hT1, hT2⟩ := exists_move hρ i j b (mul_mem hh hkf)
  obtain ⟨-, n, hc1, -⟩ := hc
  have hN' : ((ownAt D (D.plEq w) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN
  refine ⟨s, h', T (c₀⁻¹ • p.R.ioP j (PiTensorProduct.tprod ℂ u) ((((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m) • y)),
    (c₀ / ν) * c * ζ * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹, n + m, ?_, ?_, ?_⟩
  · have h1 : IsIntegral ℤ (c₀ / ν) := isIntegral_of_root ⟨n₀, hn₀, by rw [div_pow, hpow, div_self (pow_ne_zero _ hc₀)]⟩
    rw [show ((ownAt D (D.plEq w) : ℕ) : ℂ) ^ (n + m) * (c₀ / ν * c * ζ * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) =
      c₀ / ν * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ n * c) * ζ by rw [pow_add]; field_simp]
    exact (h1.mul hc1).mul (isIntegral_of_root hζ)
  · have h1 := Submodule.mem_map_of_mem (f := T.restrictScalars O') hmem
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨Q, hQ, rfl⟩
    exact hT2 Q hQ
  · have e : p.v₀ j (sg0 D p.P.A3.A) = fun τ => (u τ : (p.R.MW j (sg0 D p.P.A3.A)).sm τ) := funext fun τ => (hu τ).symm
    rw [e, hx u, one_smul, hs u]
    change ν⁻¹ • c • ρ.theta i j b _ _ = _
    rw [hT1, map_smul, map_smul, map_smul]
    simp only [Setup.theta, map_smul, smul_smul]
    congr 1
    field_simp
theorem realBase_le_baseLat_of_fit_can (hr : p.PointConditions') (hm : RecTies p) (hw : D.plEq w ∈ p.R.twPl) {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ}
    (hf : Fit p w j hρ ν) {rd : Can p w j} (hcan : IsCan p rd) : realBase p rd ≤ baseLat p w j hρ ν := by
  obtain ⟨-, e, he1, he2⟩ := hf.adapted
  obtain ⟨Z⟩ := hm.series
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ _ j _ ν hf.norm.1 hr.prim.unif
    p.charW.base.models.HW (Z.vec j) hK
  have hL : ∀ c : D.ntw.O (ex.nch.twI w), e (algebraMap _ (FractionRing (ex.nch.Oe w)) c) =
      ρ.e (ex.nch.twI w) (ex.nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)),
      IsScalarTower.algebraMap_apply _ (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w), he2, hρ.ek_e]
    rfl
  set Ψ := readExt (rdAt p w j hρ ν) e hL with hΨ
  have hint : ∀ a : 𝓞 D.what₂.LL, ∃ o : ex.nch.Oe w, algebraMap _ (FractionRing (ex.nch.Oe w)) o = ex.nch.embW w a := fun a =>
    exists_of_integral e (N := 1) (n := 0) (by simp) (by
      rw [pow_zero, one_mul, he1]
      exact map_isIntegral_int _ a.isIntegral_coe)
  have hrd : ∀ y, Ψ (rd y) = ν⁻¹ • adForm p.R.toRealDat j y (p.v₀ j _) := fun y => by
    obtain ⟨y, rfl⟩ := (p.nexp.fi j).e.surjective y
    change Ψ (rd ((p.nexp.fi j).e y)) = ν⁻¹ • evW p.nexp p.v₀ j y
    obtain ⟨n, β, hβ, -, -, -, hs⟩ := hK
    have hy : y ∈ Submodule.span D.what₂.LL (Set.range β) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      refine (congrArg Ψ (hcan ⟨β a, hβ a⟩)).trans ?_
      rw [hΨ, readExt_tmul, map_one, one_smul]
      refine (realRd_tmul p.nexp p.v₀ hρ _ j _ ν _ _).trans ?_
      congr 1
      exact mul_right_eq_self₀.2 (Or.inl (map_one (ρ.e _ _)))
    | zero => rw [map_zero, map_zero, smul_zero]; exact (congrArg Ψ rd.map_zero).trans Ψ.map_zero
    | add u v _ _ hu hv => rw [map_add, map_add, smul_add, ← hu, ← hv, ← Ψ.map_add]; exact congrArg Ψ (rd.map_add _ _)
    | smul c u _ hu =>
      rw [map_smul, evW_smul, smul_comm, ← hu, ← he1, hΨ, ← readExt_smul]
      exact congrArg _ (rd.map_smulₛₗ _ _)
  let O' : Subring ℂ := (e.comp (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)))).range
  have hser : ∀ s h, ∀ P ∈ Submodule.span O' {Q | ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q},
      ∃ t ∈ baseLat p w j hρ ν, Ψ t = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P := fun s h P hP => by
    induction hP using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨f, e1⟩ := hf.rat.1 s h Q hQ
      refine ⟨_, Submodule.subset_span ⟨f, ⟨s, h, Q, hQ, e1⟩, rfl⟩, ?_⟩
      rw [← e1, hΨ]
      exact (readExt_tmul _ e hL 1 f).trans (by rw [map_one, one_smul])
    | zero => exact ⟨0, zero_mem _, Ψ.map_zero.trans (LinearMap.map_zero _).symm⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨t, m1, e1⟩ := h1
      obtain ⟨t', m2, e2⟩ := h2
      exact ⟨t + t', add_mem m1 m2, by rw [Ψ.map_add, e1, e2]; exact (LinearMap.map_add _ _ _).symm⟩
    | smul a Q _ h1 =>
      obtain ⟨t, m1, e1⟩ := h1
      obtain ⟨_, o, rfl⟩ := a
      refine ⟨o • t, Submodule.smul_mem _ o m1, ?_⟩
      rw [← algebraMap_smul (FractionRing (ex.nch.Oe w)) o t, hΨ, readExt_smul, ← hΨ, e1]
      exact (LinearMap.map_smul _ _ _).symm
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ thetaBase p.R.toRealDat j p.P.P0 p.P.ψ0⁻¹ 1 (D.plEq w) (ownAt D (D.plEq w)) at hx
  change rd x ∈ baseLat p w j hρ ν
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, φ, hk, hx⟩ := hx
    obtain ⟨s, h, P, ζ, n, hζ, hP, e1⟩ := _root_.GlobalTheory.BigOn.Exp.exists_series_alt hr hm hw hf O'
      (fun a => by obtain ⟨o, ho⟩ := hint a; exact ⟨o, by rw [RingHom.comp_apply, ho, he1]⟩) hk hx
    obtain ⟨t, ht, e2⟩ := hser s h P hP
    rcases exists_scalar_of_readExt _ e hL hF (x := rd x) (t := t) (ζ := ζ) (((hrd x).trans e1).trans (congrArg _ e2.symm)) with
      h0 | ⟨a, ha, h0⟩
    · exact h0 ▸ zero_mem _
    · obtain ⟨o, rfl⟩ := exists_of_integral e (isUnit_ownAt ex.nch w) (ha ▸ hζ)
      rw [h0, algebraMap_smul]
      exact Submodule.smul_mem _ o ht
  | zero => exact rd.map_zero ▸ zero_mem _
  | add u v _ _ hu hv => exact rd.map_add u v ▸ add_mem hu hv
  | smul a y _ hy =>
    obtain ⟨o, ho⟩ := hint a
    have e1 : rd (a • y) = o • rd y := by
      rw [← algebraMap_smul (FractionRing (ex.nch.Oe w)) o, ho]
      exact rd.map_smulₛₗ (a : D.what₂.LL) y
    exact e1 ▸ Submodule.smul_mem _ o hy
theorem baseLe_of_cusp_decay_and_ray_class_field : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ :=
  fun _ _ _ => _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun _ _ _ _ _ hr hm _ hw _ _ _ _ _ hf hcan => _root_.GlobalTheory.BigOn.Exp.realBase_le_baseLat_of_fit_can hr hm.2.2 hw hf hcan
end GlobalTheory.BigOn.Exp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000
section Slot
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ)
def OriginData (K : Ctx) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) {D : D7} (Wt : Set B.places.Pl) (nch : NChoice D) : Prop :=
  ∃ (P : Pre2 K w) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), (ListSt cDep x ∧ SatU P) ∧ Wt = P.Wt ∧ Kept l.c.ch nch
def extensionWithOrigin : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep K B f T w Z Wt p0 t nch n xd c ×
  PLift (_root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch)
def GeometricNormExtension : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)
def SpectralFiniteness : Prop := AllSt fun K _ _ _ w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (S : SExt) (Γ : GeoP), (ListSt cDep x ∧ SatU P) →
  ∃ (Z : w.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch
def SecondNonvanishing : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s K B f T w
end Slot
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
def FirstStageExists : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x') ∧ SameGal (Dof x) (Dof x')
def ThirdStageExists : Prop := AllSt fun _ B _ T _ _ x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (s : B.places.Pl → (Dof x).ntw.Tw),
  (∀ v, ∃ b, ReadsAt (D := Dof x) (s v) b v) → (∀ v, s (B.places.conj v) = s v) →
  ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi, c.ch.twI = s
def MoveToBase : Prop := StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' →
  HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ →
  ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x' → SameGal (Dof x) (Dof x') →
    ∃ x'' : St P', Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x''
end GlobalTheory.HeightCounting.Up
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InfWtEqInfOf
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
namespace GlobalTheory.LocInfWt
theorem infWt_eq_infOf_alt : ∀ (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), _root_.GlobalTheory.HeightCounting.HeckeOpenStatements D M tup → ∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam := by
  intro D M tup hH i a τ lam hd hw
  obtain ⟨P, -⟩ := D.naut.pt_surj i (Classical.arbitrary (D.nd.X i))
  rw [D.nbc.embAV_inf i P, hH.emb i P,
    hH.au.wt (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (hH.av.rep i P) a hd]
  exact hH.au.infW (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 a τ lam hw
end GlobalTheory.LocInfWt
end
end

