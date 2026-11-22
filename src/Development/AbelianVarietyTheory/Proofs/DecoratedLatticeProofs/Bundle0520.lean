import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0509
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.QLevMid

set_option maxHeartbeats 2000000 in

theorem level_at_place : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (pk W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (chrK W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((pk W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT t PP hP E hRes j d hd hj x hxK
  obtain ⟨⟨N, hSD⟩, hPg⟩ := GlobalTheory.T.true_pack_twist_place_property W hW t PP hP j hj
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frame j d hd
  have hloc := (a.Q PP ⟨t, hP⟩).gl_loc j d hd x
  obtain ⟨hG, hSt, hOff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  have hRed := GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ (a.Q PP ⟨t, hP⟩).compl _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  obtain ⟨hι, hrep⟩ := GlobalTheory.T.completion_smallIntegers_in_prime_dense _ _ PP _ _ _ (a.Q PP ⟨t, hP⟩).compl (a.Q PP ⟨t, hP⟩).unif
  have hSt' := hSt.2 hxK

  have hQ : ∀ PP' ∈ (pk W).Q t, PP'.under (𝓞 (I.rec7 l Z).host.F) = PP.under (𝓞 (I.rec7 l Z).host.F) → PP' = PP :=
    fun PP' hP' h => hW.pk.sel PP' PP ⟨t, hP'⟩ ⟨t, hP⟩ h
  obtain ⟨hmem, hchi⟩ := GlobalTheory.T.mem_twistPlaceLevel_single_place_character _ _ ((pk W).βY j) (I.rec7 l Z).R.r (I.rec7 l Z).R.t j (r_le_Y j) (pk W).Pg ((pk W).Q t) (lvP W) (pk W).chi ((pk W).xiR t) PP hP hPg hQ _ hG hOff
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hC1 := GlobalTheory.T.reductionBlockTriangular_iff_mem_parahoricLevel _ _ PP _ hι (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η _ e he x hxK _ (hRed hSt')
  have hC2 := GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet _ _ PP _ hι hrep (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η ((pk W).xiR t PP) hRes _ e he x
  rw [← hr] at hC1 hC2
  refine ⟨hmem.trans ⟨fun h => hC1.1 h.2, fun h => ⟨hSt', hC1.2 h⟩⟩, fun hx => ?_⟩
  exact (hchi hSt').trans (congrArg Units.val (hC2 hx _ (hRed hSt') (hC1.2 hx)))

end GlobalTheory.QLevMid

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinLaw

theorem combAt_aconv {D : D7} {S T : HSp D} (P : GlobalTheory.FinPl.Pl D → Prop) :
    ∀ l : List (WO S T →₀ ℂ), (∀ e ∈ l, GlobalTheory.FinPl.CombAt P e) → GlobalTheory.FinPl.CombAt P (aconv l) := by
  intro l
  induction l with
  | nil =>
    intro _ u hu i j
    have h0 : aconv ([] : List (WO S T →₀ ℂ)) = Finsupp.single 0 1 := rfl
    rw [h0, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu
    simpa using (GlobalTheory.FinPl.idAt D P).zero_mem
  | cons e l ih =>
    intro hl u hu
    have e1 : aconv (e :: l) = aconv [e, aconv l] := by
      apply AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := WO S T)
      rw [GlobalTheory.QValOuter.aconv_cons, GlobalTheory.QValOuter.aconv_pair]
    rw [e1] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.QValOuter.mem_support_aconv_pair _ _ hu
    intro i j
    rw [Matrix.add_apply]
    exact Ideal.add_mem _ (hl e List.mem_cons_self a ha i j)
      (ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) b hb i j)

theorem comb_aconv_cons {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : WO S T →₀ ℂ)
    (l : List (WO S T →₀ ℂ)) (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum]
  have hG0 : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have hGa : ∀ u (a b : ℂ), (a + b) • heisO ψ S T u f = a • heisO ψ S T u f + b • heisO ψ S T u f :=
    fun u a b => add_smul _ _ _
  show (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).sum
    (fun u a => a • heisO ψ S T u f) = _
  rw [Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finsupp.sum_single_index (hG0 _), GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (h x hx y hy)]

theorem comb_aconv_map {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {r : ℕ} (p : Fin r → GlobalTheory.FinPl.Pl D)
    (hp : Function.Injective p) (E : Fin r → WO S T →₀ ℂ) (hE : ∀ a, GlobalTheory.FinPl.CombAt (· = p a) (E a))
    (f : WO S T → ℂ) :
    ∀ L : List (Fin r), L.Nodup → comb ψ S T (aconv (L.map E)) f = L.foldr (fun a g => comb ψ S T (E a) g) f := by
  intro L
  induction L with
  | nil => intro _; exact GlobalTheory.LevelComb.comb_single_zero ψ f
  | cons a L ih =>
    intro hL
    rw [List.map_cons, comb_aconv_cons, ih hL.of_cons, List.foldr_cons]
    intro x hx y hy
    refine GlobalTheory.DisjComb.symplO_disj (P := (· = p a)) (P' := fun v => ∃ b ∈ L, v = p b) ?_ (hE a x hx) ?_
    · rintro _ rfl ⟨b, hb, hab⟩
      exact (List.nodup_cons.1 hL).1 (hp hab ▸ hb)
    · exact combAt_aconv _ (L.map E) (fun e he => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
        exact fun u hu => GlobalTheory.DisjComb.mxAt_mono (fun v hv => ⟨b, hb, hv⟩) (hE b u hu)) y hy

theorem eQ_comb_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ Ψ, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ → ∀ i, ∃ f, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f ∧ comb c.ψ _ _ (w.eQ j) Ψ = comb c.ψ _ _ ((F.Q i).eL j) f := by
  intro D c v t w F hc hv hP j hj Ψ hΨ i
  have hI := fun P P' hd => GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V j) (c.V (j + 1)) P P' hd
  have hca : ∀ a, GlobalTheory.FinPl.CombAt (· = (F.Q a).q.v) ((F.Q a).eL j) := by
    intro a u hu r q'
    have := (F.Q a).hs
    exact (GlobalTheory.FinPl.FrameLat.idem_iff (F.Q a).q _).2 (((F.Q a).eL_at j ((F.Q a).s - j) (by omega)).1 u hu r q')
  have hdisj : ∀ a b : Fin F.r, a ≠ b → ∀ p, p = (F.Q a).q.v → ¬ p = (F.Q b).q.v := fun a b hab p ha hb =>
    hab (hP.inj (ha.symm.trans hb))
  let g : Fin F.r → (WO (c.V j) (c.V (j + 1)) → ℂ) → (WO (c.V j) (c.V (j + 1)) → ℂ) :=
    fun a f => comb c.ψ _ _ ((F.Q a).eL j) f
  have hfold : comb c.ψ _ _ (w.eQ j) Ψ = (List.finRange F.r).foldr g Ψ := by
    rw [hP.eQ j hj, List.ofFn_eq_map]
    exact comb_aconv_map c.ψ (fun a => (F.Q a).q.v) hP.inj (fun a => (F.Q a).eL j) hca Ψ _ (List.nodup_finRange _)
  refine ⟨((List.finRange F.r).erase i).foldr g Ψ, ?_, ?_⟩
  · have h0 : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) Ψ :=
      GlobalTheory.GSuppComb.vac_mono (fun p hp => by rw [hp]; exact (hP.places _).2 ⟨i, rfl⟩) hΨ
    have key : ∀ l : List (Fin F.r), (∀ a ∈ l, a ≠ i) →
        GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) (l.foldr g Ψ) := by
      intro l
      induction l with
      | nil => intro _; exact h0
      | cons a l ih =>
        intro hl
        exact ((hI (· = (F.Q a).q.v) (· = (F.Q i).q.v) (hdisj a i (hl a List.mem_cons_self))).2.1 _ (hca a)).2 _ _ _
          (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    exact key _ fun a ha => ((List.nodup_finRange F.r).mem_erase_iff.1 ha).1
  · rw [hfold]
    exact GlobalTheory.GSuppComb.foldr_extract g i (fun a ha x => (hI _ _ (hdisj a i ha)).1 _ _ (hca a) (hca i) x) _ Ψ
      (List.mem_finRange i)

theorem local_scalar_law : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ), (ofSplit q).IsComp χS μS → (ofSplit q).IsComp χT μT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ (e : WO S T →₀ ℂ) (Φ : Matrix Y Y' k → ℂ), Φ ∈ SB (Matrix Y Y' k) → (ofSplit q).IsCombAt ψ FS FT e Φ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∀ g gk h hk, (ofSplit q).IsLoc FS g gk → (ofSplit q).IsLoc FT h hk → ∀ z : ℂ, (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ = z • Φ → ω (g, h) (comb ψ S T e f) = z • comb ψ S T e f := by
  intro D k _ _ _ _ q hU ψ ψk hψ hch hcond S T χS χT ω hω μS μT cS cT Y Y' _ _ _ _ FS FT LS LT hLS hLT hFS hFT e Φ hΦ
    hcomb f hf g gk h hk hg hh z hz
  obtain ⟨Tm, hTm, hTO⟩ :=
    (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D k q hU Y Y' S T FS FT ψ ψk hψ hch hcond LS LT hLS hLT hFS hFT).2 f hf
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  let Φs : SB (Matrix Y Y' k) := ⟨Φ, hΦ⟩
  have e1 : Tm Φs = comb ψ S T e f := by rw [hcomb.2 Tm hTm O Φs hO rfl, hTO O hO]
  have e2 := GlobalTheory.T.weilDatum_localModel_formula D k (ofSplit q) ψ S T χS χT ω hω μS μT cS cT Y Y' FS FT Tm hTm g gk h hk hg hh Φs (z • Φs)
    (by rw [Submodule.coe_smul]; exact hz.symm)
  rw [← e1, e2, map_smul]

theorem om_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ ζ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k)
    (Φ : Matrix b a k → ℂ) :
    om (μ * ζ) g h Φ = ((ζ (Matrix.GeneralLinearGroup.det g) : ℂ) *
      (((ζ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ)) • om μ g h Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val]
  ring

variable {D : D7}

theorem isComp_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ χ' : (AE D)ˣ →* Circle} {μ μ' : kˣ →* ℂˣ} (h : p.IsComp χ μ) (h' : p.IsComp χ' μ') :
    p.IsComp (χ * χ') (μ * μ') := fun x a ha => by
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Circle.coe_mul, h x a ha, h' x a ha]

theorem isComp_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ μ) : p.IsComp χ⁻¹ μ⁻¹ := fun x a ha => by
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv, h x a ha]

theorem place_law (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t)
    (hc : c.Is) (ht : t.Is) (hv : v.Is) (hP : F.Pins w) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r)
    (cc : ℕ) (hcc : j + 1 + cc = (F.Q i).s + 1) (x : GL ((F.Q i).X (j + 1) ⊕ Fin cc) (F.Q i).k)
    (hx : x ∈ ((F.Q i).T.lev (j + 1) cc hcc).J) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ →
      GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
      t.om j (1, (F.Q i).gl (j + 1) cc hcc x) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧
        t.om (j + 1) ((F.Q i).gl (j + 1) cc hcc x, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) =
          a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  have hs := (F.Q i).hs
  obtain ⟨d, rfl⟩ : ∃ d, cc = d + 1 := ⟨cc - 1, by omega⟩
  have hjd : j + (d + 1) = (F.Q i).s := by omega
  have hjd' : j + 1 + d = (F.Q i).s := by omega
  obtain ⟨χz, hV, hW, hV', hW'⟩ := hP.mid j σ h
  obtain ⟨ζ, hζ⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit (F.Q i).q) χz
  refine ⟨(((F.Q i).T.lev (j + 1) (d + 1) hcc).lam ⟨x, hx⟩ : ℂ) * (((ζ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ),
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _), fun Ψ₁ Ψ₂ h₁ h₂ => ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf, hfe⟩ := eQ_comb_at_place D c v t w F hc hv hP j (by omega) Ψ₁ h₁ i
    rw [hfe]
    have hw := (t.sBF j (σ + 1) h).weil
    rw [(ht.sBF j (σ + 1) h).1] at hw
    have hmu := isComp_inv _ ((F.Q i).mu j (by omega)).1
    rw [inv_inv] at hmu
    have cS : (ofSplit (F.Q i).q).IsComp (t.sBF j (σ + 1) h).χV (((F.Q i).T.mu (j + 1))⁻¹ * ζ) := by
      rw [hV]; exact isComp_mul _ hmu hζ
    have cT : (ofSplit (F.Q i).q).IsComp (t.sBF j (σ + 1) h).χW ((F.Q i).T.mu (j + 1))⁻¹ := by
      rw [hW]; exact hmu
    have h1 : (ofSplit (F.Q i).q).IsLoc ((F.Q i).FY j (d + 1 + 1) (by omega)) 1 1 := by
      have := (F.Q i).gl_loc j (d + 1 + 1) (by omega) 1
      rwa [map_one] at this
    refine local_scalar_law D (F.Q i).k (F.Q i).q (F.Q i).unit c.ψ (F.Q i).ψk hc.std (F.Q i).char (F.Q i).cond _ _ _ _ (t.om j) hw _ _ cS cT _ _
      ((F.Q i).FY j (d + 1 + 1) (by omega)) ((F.Q i).FY (j + 1) (d + 1) (by omega)) (v.N j) (v.N (j + 1))
      (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) ((F.Q i).latY j (d + 1 + 1) (by omega))
      ((F.Q i).latY (j + 1) (d + 1) (by omega)) ((F.Q i).eL j) ((F.Q i).T.Phi j (d + 1) hjd)
      ((F.Q i).reg.1 j (d + 1) hjd) ((F.Q i).eL_at j (d + 1) hjd) f hf 1 1 _ x h1 ((F.Q i).gl_loc _ _ _ x) _ ?_
    rw [map_one, map_one, Units.val_one, one_smul, mul_inv, inv_inv, om_twist, ((F.Q i).laws.1 j (d + 1) hjd).2 ⟨x, hx⟩,
      smul_smul]
    congr 1
    simp only [map_one, MonoidHom.inv_apply, inv_one, Units.val_one, one_mul, inv_inv, mul_inv, Units.val_inv_eq_inv_val]
    ring
  · obtain ⟨f, hf, hfe⟩ := eQ_comb_at_place D c v t w F hc hv hP (j + 1) (by omega) Ψ₂ h₂ i
    rw [hfe]
    have hw := (t.sFB j σ h).weil
    rw [(ht.sFB j σ h).1] at hw
    have hmu := isComp_inv _ ((F.Q i).mu (j + 1) (by omega)).1
    rw [inv_inv] at hmu
    have cS : (ofSplit (F.Q i).q).IsComp (t.sFB j σ h).χV ((F.Q i).T.mu (j + 1 + 1))⁻¹ := by
      rw [hV']; exact hmu
    have cT : (ofSplit (F.Q i).q).IsComp (t.sFB j σ h).χW (((F.Q i).T.mu (j + 1 + 1))⁻¹ * ζ) := by
      rw [hW']; exact isComp_mul _ hmu hζ
    have h1 : (ofSplit (F.Q i).q).IsLoc ((F.Q i).FY (j + 1 + 1) d (by omega)) 1 1 := by
      have := (F.Q i).gl_loc (j + 1 + 1) d (by omega) 1
      rwa [map_one] at this
    refine local_scalar_law D (F.Q i).k (F.Q i).q (F.Q i).unit c.ψ (F.Q i).ψk hc.std (F.Q i).char (F.Q i).cond _ _ _ _ (t.om (j + 1)) hw _ _
      cS cT _ _ ((F.Q i).FY (j + 1) (d + 1) (by omega)) ((F.Q i).FY (j + 1 + 1) d (by omega)) (v.N (j + 1))
      (v.N (j + 1 + 1)) (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) (by omega))
      ((F.Q i).latY (j + 1) (d + 1) (by omega)) ((F.Q i).latY (j + 1 + 1) d (by omega)) ((F.Q i).eL (j + 1))
      ((F.Q i).T.Phi (j + 1) d hjd') ((F.Q i).reg.1 (j + 1) d hjd') ((F.Q i).eL_at (j + 1) d hjd') f hf _ x 1 1
      ((F.Q i).gl_loc _ _ _ x) h1 _ ?_
    rw [inv_inv, ((F.Q i).laws.1 (j + 1) d hjd').1 ⟨x, hx⟩, smul_smul]
    congr 1
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

theorem inverse_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ → t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧ t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  intro D c v t w F hc ht hv _ hP j σ h k hk
  refine Subgroup.iSup_induction (fun i => GlobalTheory.QuotientFiniteLevel.locK F j σ h i)
    (C := fun k => ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ →
      GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
      t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧
        t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)
    (show k ∈ ⨆ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i from hk) ?_ ?_ ?_
  · intro i k hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hk
    exact place_law D c v t w F hc ht hv hP j σ h i _ _ x hx
  · refine ⟨1, one_ne_zero, fun Ψ₁ Ψ₂ _ _ => ⟨?_, ?_⟩⟩
    · rw [show ((1 : GA D (c.V j)), (1 : GA D (c.V (j + 1)))) = 1 from rfl, map_one, inv_one, one_smul]; rfl
    · rw [show ((1 : GA D (c.V (j + 1))), (1 : GA D (c.V (j + 1 + 1)))) = 1 from rfl, map_one, one_smul]; rfl
  · rintro x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
    refine ⟨a * b, mul_ne_zero ha hb, fun Ψ₁ Ψ₂ h₁ h₂ => ⟨?_, ?_⟩⟩
    · have e : ((1 : GA D (c.V j)), x * y) = (1, x) * (1, y) := by simp
      rw [e, map_mul, Module.End.mul_apply, (hyb Ψ₁ Ψ₂ h₁ h₂).1, map_smul, (hxa Ψ₁ Ψ₂ h₁ h₂).1, smul_smul, mul_inv,
        mul_comm b⁻¹]
    · have e : (x * y, (1 : GA D (c.V (j + 1 + 1)))) = (x, 1) * (y, 1) := by simp
      rw [e, map_mul, Module.End.mul_apply, (hyb Ψ₁ Ψ₂ h₁ h₂).2, map_smul, (hxa Ψ₁ Ψ₂ h₁ h₂).2, smul_smul, mul_comm b a]

end GlobalTheory.QFinLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreNormalizingFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChainTw

open GlobalTheory.LFun in

theorem dv_center_of_isSplit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (a t : ℕ) :
    dv E a (a + t) v ((t : ℂ) / 2) =
      (∏ n ∈ Finset.Ioc t (a + t), (1 - (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ n)⁻¹))⁻¹ := by
  have hI : Finset.Icc (t + 1) (t + a) = Finset.Ioc t (a + t) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have he : etaU E v = 1 := by unfold etaU; exact if_pos hv
  rw [dv_center, hI, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [locL, etaFam_of_unram (isUnram_of_isSplit h2 hv), he, one_pow, eulerFac_singleton, Units.val_one, one_mul,
    npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem dSfun_twist_restore : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ a : ℕ, GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) ≠ 0 ∧ GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ((D.R.t : ℂ) / 2) = GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) * ((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ) := by
  intro D c w hw a
  classical
  obtain ⟨hS, hQS₀, hinj, hsplit, -⟩ := GlobalTheory.T.chainTwistPlaces_split_unramifiedQuotients D c w hw
  have ht : 0 < ((D.R.t : ℂ) / 2).re := by
    have h3 := D.R.three_m_lt_t
    have h1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 1 ≤ D.R.t)
    simp only [Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  set s : ℂ := (D.R.t : ℂ) / 2 with hs_def
  set f : HeightOneSpectrum (𝓞 D.host.F) → ℂ := fun v => GlobalTheory.LFun.dv D.host.E a (a + D.R.t) v s with hf
  set Qv : Finset (HeightOneSpectrum (𝓞 D.host.F)) := w.Q.image fun PP => PP.under (𝓞 D.host.F) with hQv
  have h0 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ w.S₀}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv w.S₀ a (a + D.R.t) ht).multipliable.hasProd
  have h1 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ht).multipliable.hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := (Qv : Set (HeightOneSpectrum (𝓞 D.host.F)))) (f := f)).1
    (Finset.hasProd Qv f)
  have hmem : ∀ v, v ∈ Qv ↔ ∃ PP ∈ w.Q, PP.under (𝓞 D.host.F) = v := fun v => by simp [hQv]
  have hsplitf : Set.mulIndicator {v | v ∉ w.S₀} f =
      Set.mulIndicator {v | v ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} f * Set.mulIndicator (Qv : Set _) f := by
    funext v
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_ofPred_eq, Finset.mem_coe]
    by_cases hq : v ∈ Qv
    · obtain ⟨PP, hPP, rfl⟩ := (hmem _).1 hq
      have hc : PP.under (𝓞 D.host.F) ∈ c.S := (hS _).2 (Or.inr ⟨PP, hPP, rfl⟩)
      simp [hQS₀ PP hPP, hc, hq]
    · by_cases h0' : v ∈ w.S₀
      · have hc : v ∈ c.S := (hS _).2 (Or.inl h0')
        simp [h0', hc, hq]
      · have hc : v ∉ c.S := fun hc => ((hS _).1 hc).elim h0' fun hx => hq ((hmem _).2 hx)
        simp [h0', hc, hq]
  rw [hsplitf] at h0
  have key : GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) s =
      GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) s * ∏ v ∈ Qv, f v :=
    h0.unique (h1.mul h2)
  have hloc : ∀ PP ∈ w.Q, f (PP.under (𝓞 D.host.F)) = ((zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ)⁻¹ := by
    intro PP hPP
    obtain ⟨hsp, hN, -⟩ := hsplit PP hPP
    show GlobalTheory.LFun.dv D.host.E a (a + D.R.t) (PP.under (𝓞 D.host.F)) ((D.R.t : ℂ) / 2) = _
    rw [dv_center_of_isSplit D.sp.cm.deg2 hsp, hN, zinv]
    push_cast
    rfl
  have hprod : ∏ v ∈ Qv, f v = (((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ)) : ℂ)⁻¹ := by
    rw [hQv, Finset.prod_image (fun x hx y hy h => hinj hx hy h), Finset.prod_congr rfl hloc,
      Finset.prod_inv_distrib]
    push_cast
    rfl
  have hne : GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) s ≠ 0 := GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ ht
  rw [hprod] at key
  have hZ : (((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ)) : ℂ) ≠ 0 := by
    intro h0
    apply hne
    rw [key, h0, _root_.inv_zero, mul_zero]
  refine ⟨hne, ?_⟩
  rw [key, mul_assoc, inv_mul_cancel₀ hZ, mul_one]

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twVec' : TwVec' := by
  intro B X I hOk hPins l Z u a Ch A hA ψ θ x vac c₀ hX k _ _ _ _ ι p β Q hStd J hPl j hj α γ cT hReps e he
  have hjm : j ≤ B.R.m := Nat.le_of_succ_le hj
  have hL0 : ∀ z, z ∈ (x j).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs j hjm).2.2
  have hL1 : ∀ z, z ∈ (x (j + 1)).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs (j + 1) hj).2.2
  have hvac := hX.vc j (by omega)
  have hS0 : ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL0 z
  have hS1 : ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL1 z
  have hV : Vac ψ _ _ (x j).L (x (j + 1)).L (fun v => ∃ i, v = (p i).v) (vac j) := by
    refine ⟨hvac.2.theta, ?_⟩
    have hle : latO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) (fun v => ∃ i, v = (p i).v) ≤ stdHom _ _ := by
      rw [hS0, hS1]
      apply AddSubgroup.closure_mono
      rintro w ⟨a, ha, -, rest⟩
      exact ⟨a, ha, fun _ h => absurd trivial h, rest⟩
    exact ⟨fun u hu => hvac.2.lat.1 u (hle hu), fun e' he' u hu hh => hvac.2.lat.2 e' he' u (hle hu) hh⟩
  have hO := hReps.2 (vac j) hV
  obtain ⟨eq, heq⟩ := hStd.1
  have hF := GlobalTheory.T.putInSplitPlaces_datum_product_on_half (I.rec7 l Z) k ι p J hPl _ _ ψ hX.std _ _ (β j) (β (j + 1)) (x j).L (x (j + 1)).L
    (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z j hjm _ hL0) (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z (j + 1) hj _ hL1) hL0 hL1 _ e he ⟨eq, heq⟩ _ (vac j) _ hvac.2.theta hvac.2.lat hO
  have hval := GlobalTheory.T.chartBasePoints_levelDatum_eq_local_prod I hOk hPins l Z u a Ch A hA k ι p β Q _ hStd J hPl j hj α γ
  convert hF using 2 with z
  exact hval z

end GlobalTheory.AdForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedThetaCorrespondence_all_goodPrimes : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, UnrCorr R i t (fun _ => True) := by
  first | exact @GlobalTheory.UnrAll.unrCorr_all | exact GlobalTheory.UnrAll.unrCorr_all | (intros; apply GlobalTheory.UnrAll.unrCorr_all <;> assumption)
end

