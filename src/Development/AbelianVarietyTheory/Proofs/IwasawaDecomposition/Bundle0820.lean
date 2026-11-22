import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0813
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0815
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0741
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0740
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0595
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0814
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0722
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0719
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0763
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasRatioOfHasDRGalois
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0761
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFirstAnalyticDataEnlargedColumnChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 4000000 in

theorem seed_at_enl : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg ?_)
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  rintro K ⟨hK, hO⟩
  refine hO.imp ?_
  rintro B' f' T' hOv hOB w' ⟨pin⟩ B f T w _ _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ hgrp _ core' alg' _ _ hKs _ _ _ _ _

  set Wt' : Set B'.places.Pl := {v | B'.places.resChar v ∈ T'.pl} with hWt
  letI := alg'
  obtain ⟨hHH, -, -, hPos, hStd, hStdX, -, -⟩ := hK (w'.st Z') hOv
  have hok := w'.ok
  have hC := w'.C_eq
  have hrange := w'.xi_range
  have hsel : SelHalf w'.I := by
    intro a b P hP P' hP' hq
    obtain ⟨q, hq, hqP, hqP'⟩ := hq
    obtain ⟨v, -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP
    obtain ⟨v', -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP'
    have hab : ∀ v, (w'.I.sel v).under (𝓞 B'.host.F) = v := fun v => by
      have h := pin.above v
      unfold Formalism.L2.Host.aboveF at h
      rw [Set.Finite.mem_toFinset] at h
      exact h
    have hmem : ∀ v, ((q : 𝓞 B'.host.E) ∈ (w'.I.sel v).asIdeal) → (q : 𝓞 B'.host.F) ∈ v.asIdeal := fun v h => by
      rw [← hab v]
      show (q : 𝓞 B'.host.F) ∈ (w'.I.sel v).asIdeal.comap (algebraMap _ _)
      rw [Ideal.mem_comap, map_natCast]
      exact h
    have := pin.half v v' q hq (hmem v hqP) (hmem v' hqP')
    exact congrArg HeightOneSpectrum.asIdeal this
  have hfin : Wt'.Finite := GlobalTheory.Mem.Top.TwFin.finite_pl B' T'.pl
  have hconj : ∀ v ∈ Wt', B'.places.conj v ∈ Wt' :=
    fun v hv => by simpa only [hWt, Set.mem_setOf_eq, GlobalTheory.Mem.Top.TwFin.resChar_conj] using hv
  have hch : Fld.charField f' ≤ B'.KsC := (GlobalTheory.Mem.Base.KsExact.lower w'.exact).2.2.1
  obtain ⟨hVals, -⟩ := hOB w'.px w'.I hX' hok hC hrange
  have hrange' : Set.range w'.I.xi = T'.set w'.I.C := by rw [hC]; exact hrange
  have hCK : ∀ x ∈ (w'.st Z').B.Ks, ∃ y : core'.Q.c.F, algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y = x := hKs
  have hCE : ∀ x : (w'.st Z').toD7.host.E, ∃ y : core'.Q.c.F, algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y = (w'.st Z').toD7.embE x :=
    fun x => hKs _ (B'.E_le_Ks x)
  have hmu : ∀ (L : Formalism.IndefR.Links.LevCh (w'.st Z').toD7 (TupU w'.I (usedOf w'.I T' Wt'))),
      L.Is (mu0F (X := (w'.st Z').B.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) → L.C = Top.Fr.at (w'.st Z') w'.I.C →
      ∀ (i : Fin (w'.st Z').toD7.R.m) (x : (AE (w'.st Z').toD7)ˣ), infPart (w'.st Z').toD7 (x : AE (w'.st Z').toD7) = 1 →
        ∃ y : core'.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) := by
    intro L hL hLC i x hx
    have hLC' : L.C = Fr.at (w'.st Z') f' := hLC.trans (by rw [hC])
    have hmem : ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ Formalism.L2.Pj.FO (w'.st Z').toD7 := by
      refine GlobalTheory.CoreExact.char_mem_of_values (w'.st Z').toD7 _ _ (hL.mu0 i) (Formalism.L2.Pj.FO (w'.st Z').toD7) ?_ ?_ x hx
      · rw [hLC', ← GlobalTheory.CoreExact.KsC_eq]
        exact (le_iSup (fun j => Fld.valueField (f'.mu0 j) 0) i).trans
          (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hch))))
      · intro k
        obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
        choose z hz using fun g => ((w'.st Z').toD7.hc ((w'.st Z').toD7.eTau.symm g)).e_int i
        have hnz : n = fun g => 2 * -z g := funext fun g => by
          have h1 := hn g
          simp only [Formalism.L2.Host.eExp, hz] at h1
          exact_mod_cast h1
        rw [hnz] at hi
        rw [hi k]
        refine prod_mem fun g _ => ?_
        rw [GlobalTheory.RefCharValues.sign_zpow_even _ ((map_ne_zero _).2 k.ne_zero)]
        exact zpow_mem (div_mem (Formalism.L2.Pj.conj_mem_FO _ _ _) (Formalism.L2.Pj.conj_mem_FO _ ((starRingEnd ℂ).comp _) _)) _
    obtain ⟨x₁, hx₁, hx₁'⟩ := (mem_FO_assembled_iff (w'.st Z') _).1 hmem
    obtain ⟨y, hy⟩ := hCK x₁ hx₁
    exact ⟨y, by rw [hy]; exact hx₁'.symm⟩
  exact GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices (w'.st Z') w'.px w'.I hX' T' Wt' core'.Q.c.F h6 hfin hconj hok hrange' hsel hgrp hVals hHH hStd hStdX hPos hCK hCE hmu

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGridUnitGapFieldContainsValues
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem exists_grid_fieldHas : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  intro cDep
  have h := StepW.and (GlobalTheory.T.nonempty_thetaLiftGridData_unit_gap_all_states cDep) GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates
  refine EvG.imp h (fun K _ _ _ _ hK => ?_)
  obtain ⟨S₁, P₁, A, S₂, a1, a2, hh⟩ := hK
  choose M hMf hM using GlobalTheory.T.exists_numberField_gridCharacters_uniform cDep K.s.b
  choose S hSa hS using fun B₀ => GlobalTheory.T.finiteDimensional_subfield_complex_finitelyGenerated (M B₀) (hMf B₀)
  refine ⟨fun B f F => S₁ B f F ∪ S B, P₁, A, S₂, ?_, a2, ?_⟩
  · intro B f F z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [a1 B f F z hz, hSa B z hz]
  · intro B f T hO hH hP hA hk hF htriv w hw P x
    have hH' : Has₂ B (S₁ B.toPre f B.KsC) (S₂ B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨h1, h3⟩ := hh B f T hO hH' hP hA hk hF htriv w hw
    obtain ⟨G⟩ := h1 P x
    obtain ⟨G', hG'⟩ := hM B.toPre (w.st x.o.Z) rfl (h3 P x) _ x.m.z.R.toRealDat.toLevCh G
    have hle : M B.toPre ≤ B.fixedCoefficientFieldInComplex := hS B.toPre _ (fun z hz => hH.1 z (Finset.mem_union_right _ hz))
    obtain ⟨j, hj⟩ := GlobalTheory.T.exists_ringHom_LL0_of_le_fixedCoefficientField (w.st x.o.Z) (M B.toPre) hle
    refine ⟨G', GlobalTheory.BigTop.Fun.FieldHas.map j ?_⟩
    rw [hj]; exact hG'

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicEigenFrameDirsInExpChart
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.ChartFrames

open GlobalTheory GlobalTheory.LieMet GlobalTheory.Cartier in

theorem exists_frameFam {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (σ : c.F →+* ℂ)
    {n g : ℕ} {e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)} {ex : ExpMaps Z σ g} (hex : IsExpChart e ex)
    (y₀ : CxPts (genStr Z) σ) (hy₀ : y₀ ∈ e.source) :
    ∃ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z))
      (B : Set (Fin n → ℂ)) (a : (Fin n → ℂ) → CxFr Z σ), LogKS.chart V ≫ genStr Z = spMap φ ∧ IsOpen B ∧ e y₀ ∈ B ∧
      B ⊆ e.target ∧ HolFam B a ∧
      ∀ b ∈ B, (a b).1 = e.symm b ∧ ∃ hy : (a b).1 ∈ ptsIn (genStr Z) σ V.1, F.IsMap (evHom hy) (a b).2 := by
  obtain ⟨U, hU, φ, F, hzU, hφ, -⟩ :=
    EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (y₀.1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have hy₀V : y₀ ∈ ptsIn (genStr Z) σ V.1 := CxPts.mem_ptsIn.2 hzU
  have hov : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), σ = (evHom hy).comp φ := fun y hy =>
    EigLoc.spMap_inj (y.2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, spMap_evHom hy]))
  have hx : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      y.1 ≫ genι Z = spMap (evHom hy) ≫ LogKS.chart V ≫ genι Z := fun y hy => by
    rw [← Category.assoc, spMap_evHom hy]
  have hfr : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), EigFrame.IsMap (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (evHom hy) f :=
    fun y hy => EigFrame.exists_isMap F (evHom hy) (hov y hy) (hx y hy)
  choose fr hfr using hfr
  have h0 : e.symm (e y₀) ∈ ptsIn (genStr Z) σ V.1 := by rw [e.left_inv hy₀]; exact hy₀V
  let a : (Fin n → ℂ) → CxFr Z σ := fun b =>
    if h : e.symm b ∈ ptsIn (genStr Z) σ V.1 then ⟨e.symm b, fr _ h⟩ else ⟨e.symm (e y₀), fr _ h0⟩
  have ha : ∀ b (h : e.symm b ∈ ptsIn (genStr Z) σ V.1), a b = ⟨e.symm b, fr _ h⟩ := fun b h => dif_pos h
  let B : Set (Fin n → ℂ) := e.target ∩ e.symm ⁻¹' ptsIn (genStr Z) σ V.1
  have hB : IsOpen B := e.continuousOn_symm.isOpen_inter_preimage e.open_target (isOpen_ptsIn _)
  have hBt : B ⊆ e.target := Set.inter_subset_left
  have hyB : IsHolTo B (fun b => (e.symm b).1) := LocLift.isHolTo_mono hex.2.2.1 hB hBt
  let ev : (Fin n → ℂ) → (Γ(gen Z, V.1) →+* ℂ) := fun b =>
    if h : e.symm b ∈ ptsIn (genStr Z) σ V.1 then evHom h else evHom h0
  have hev : ∀ b (h : e.symm b ∈ ptsIn (genStr Z) σ V.1), ev b = evHom h := fun b h => dif_pos h
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hd : ∀ r : Γ(gen Z, V.1), DifferentiableOn ℂ (fun b => ev b r) B := fun r b hb =>
    (HolLieFrame.differentiableAt_ev hyB (LogKS.chart V) ev
      (fun b' hb' => by rw [hev b' hb'.2]; exact (spMap_evHom hb'.2).symm) hb r).differentiableWithinAt
  refine ⟨V, φ, F, B, a, hφ', hB, ⟨e.map_source hy₀, h0⟩, hBt, ⟨?_, fun ρ i => ?_⟩, fun b hb => ?_⟩
  · exact LocLift.isHolTo_congr hyB fun b hb => by rw [ha b hb.2]
  · exact HolFrames.holTan_dualMap hB (F.v ρ i) (fun b hb => evHom hb.2)
      (fun r => ⟨fun b => ev b r, hd r, fun b hb => (RingHom.congr_fun (hev b hb.2) r).symm⟩)
      (fun b hb => by rw [ha b hb.2]; exact hfr _ hb.2 ρ i)
  · rw [ha b hb.2]
    exact ⟨rfl, hb.2, hfr _ hb.2⟩

open GlobalTheory.Cartier in

theorem exists_open_mem {F : Type} [Field F] (X : Var F) {κ : Type} [Finite κ] {m : κ → ℕ} (S : Fr (ratOf X) m 0)
    {p : X.X} {A : Mat m X.Fn} (hA : A ∈ S.S p) : ∃ G : X.X.Opens, p ∈ G ∧ ∀ p' ∈ G, A ∈ S.S p' := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc p
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt p g → ∃ W : X.X.Opens, p ∈ W ∧ ∀ p' ∈ W, RegAt p' g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    exact ⟨W, hW, fun p' hp' => regAt_fnOf hp' _ a⟩
  choose W hW hW' using fun (τ : κ) (i j : Fin (m τ)) => hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))
  choose W₂ hW₂ hW₂' using fun τ : κ => hreg _ (mem_O_ratOf.1 (hP τ).2.2.1)
  let G : Set X.X := ((show X.X.Opens from U) : Set X.X) ∩ (⋂ τ, ⋂ i, ⋂ j, (W τ i j : Set X.X)) ∩ ⋂ τ, (W₂ τ : Set X.X)
  have hG : IsOpen G := (U.isOpen.inter (isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => (W τ i j).isOpen)).inter (isOpen_iInter_of_finite fun τ => (W₂ τ).isOpen)
  refine ⟨⟨G, hG⟩, ⟨⟨hU, Set.mem_iInter.2 fun τ => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => hW τ i j⟩,
    Set.mem_iInter.2 fun τ => hW₂ τ⟩, fun p' hp' => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp'
  exact (hS _ h1 A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 (hW' τ i j p'
      (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 h2 τ) i) j)), (hP τ).2.1,
    mem_O_ratOf.2 (hW₂' τ p' (Set.mem_iInter.1 h3 τ)), fun i j hi => absurd hi (by simp)⟩

theorem valR_appIso_inv {Y X : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (W : Y.Opens) (g : Γ(Y, W))
    (w : Sp ℂ ⟶ Y) (hw : ⊤ ≤ w ⁻¹ᵁ W) :
    valR (w ≫ j) (j ''ᵁ W) ((j.appIso W).inv.hom g) = valR w W g := by
  have hle : W ≤ j ⁻¹ᵁ j ''ᵁ W := (j.preimage_image_eq W).ge
  rw [← GlobalTheory.Points.valR_appLE w j hle hw, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact GlobalTheory.Points.valR_res w le_rfl hw g

end GlobalTheory.LieBase.ChartFrames

namespace GlobalTheory.LieBase.ChartFrames

open GlobalTheory GlobalTheory.LieMet GlobalTheory.Cartier

theorem cxOf_mem_image {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F]
    (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z} [IsOpenImmersion j]
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (W : X.X.Opens) (z : CxPts X.str (σ.comp e.toRingHom)) :
    cxOf e σ hj z ∈ ptsIn (genStr Z) σ (j ''ᵁ W) ↔ z ∈ ptsIn X.str (σ.comp e.toRingHom) W := by
  rw [CxPts.mem_ptsIn, CxPts.mem_ptsIn]
  show j (z.1 (IsLocalRing.closedPoint ℂ)) ∈ j ''ᵁ W ↔ _
  exact ⟨fun ⟨x, hx, hxe⟩ => (j.isOpenEmbedding.injective hxe) ▸ hx, fun h => ⟨_, h, rfl⟩⟩

end GlobalTheory.LieBase.ChartFrames

open GlobalTheory GlobalTheory.LieMet GlobalTheory.Cartier GlobalTheory.LieBase.ChartFrames in

theorem GlobalTheory.LieBase.exists_chart_dirs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (C : FlagCpt T.Z e) (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ r : ℝ, 0 < r ∧ ∃ W : (Fin n → ℂ) → (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ, (∀ p k, DifferentiableOn ℂ (fun u => W u p k) (Metric.ball 0 r)) ∧ LinearIndependent ℂ (W 0) ∧ ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ch₀.source → ch₀ (cxOf e σ hj z) ∈ Metric.ball 0 r → (∃ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g') ∧ ∀ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g' → Dirs ⟨cxOf e σ hj z, g'⟩ (fun w => (ex (cxOf e σ hj z) w).left) (W (ch₀ (cxOf e σ hj z))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ C X j f f₀ Eb A₀ hj hL y n g ch₀ ex hex hys hy0
  obtain ⟨hoi, -, hT⟩ := hL
  obtain ⟨A, hA⟩ := Eb.nonempty (GlobalTheory.Cartier.under y)
  obtain ⟨V, φ, Φ, B, a, hφ, hB, h0B, hBt, ha, hab⟩ := exists_frameFam T.Z σ hex (cxOf e σ hj y) hys
  rw [hy0] at h0B
  have hsy : ch₀.symm 0 = cxOf e σ hj y := by rw [← hy0]; exact ch₀.left_inv hys
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr T.Z) σ V.1 := by
    obtain ⟨h1, hy, -⟩ := hab 0 h0B
    rwa [h1, hsy] at hy
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ A
  have hMy := hM y hA hyV
  choose Ws hWs s hs using fun τ p q => (hMy.1 τ p q).exists_fnOf
  obtain ⟨G, hG, hGA⟩ := exists_open_mem X Eb hA

  have hoi' : IsOpenImmersion j := hoi
  let sv : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → (Fin n → ℂ) → ℂ := fun τ p q u =>
    valAt' (ch₀.symm u).1 (j ''ᵁ Ws τ p q) ((j.appIso (Ws τ p q)).inv.hom (s τ p q))
  let Ω : Set (Fin n → ℂ) := B ∩ (ch₀.target ∩ ch₀.symm ⁻¹' (ptsIn (genStr T.Z) σ (j ''ᵁ G) ∩
    ⋂ τ, ⋂ p, ⋂ q, ptsIn (genStr T.Z) σ (j ''ᵁ Ws τ p q)))
  have hΩ : IsOpen Ω := hB.inter (ch₀.continuousOn_symm.isOpen_inter_preimage ch₀.open_target
    ((isOpen_ptsIn _).inter (isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun p =>
      isOpen_iInter_of_finite fun q => isOpen_ptsIn _)))
  have h0Ω : (0 : Fin n → ℂ) ∈ Ω := by
    refine ⟨h0B, hBt h0B, ?_⟩
    rw [Set.mem_preimage, hsy]
    exact ⟨(cxOf_mem_image e σ hj G y).2 (CxPts.mem_ptsIn.2 hG), Set.mem_iInter.2 fun τ => Set.mem_iInter.2 fun p =>
      Set.mem_iInter.2 fun q => (cxOf_mem_image e σ hj _ y).2 (CxPts.mem_ptsIn.2 (hWs τ p q))⟩
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ 0 h0Ω
  have src : ∀ b ∈ B, (a b).1 ∈ ch₀.source := fun b hb => by
    rw [(hab b hb).1]; exact ch₀.map_target (hBt hb)
  have h5 := fun b (hb : b ∈ B) => hex.2.2.2.2.2 _ (src b hb)
  choose! Wa hWa using fun b (hb : b ∈ B) (z : Pad.Letter Dw) => ((h5 b hb).2 _ ((a b).2.tan z.1 z.2)).exists
  have hWad : ∀ b ∈ B, ∀ z, DifferentiableAt ℂ (fun b => Wa b z) b := fun b hb z =>
    ExpDirs.differentiableAt_dir hex hB ha.1 src (ha.2 z.1 z.2) (fun b hb => hWa b hb z) hb
  have hsvd : ∀ τ p q, ∀ u ∈ Ω, DifferentiableAt ℂ (sv τ p q) u := fun τ p q u hu => by
    have h := hex.2.2.1 (j ''ᵁ Ws τ p q) ((j.appIso (Ws τ p q)).inv.hom (s τ p q))
    refine h.2.differentiableAt (h.1.mem_nhds ⟨hu.2.1, ?_⟩)
    exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hu.2.2.2 τ) p) q
  let W : (Fin n → ℂ) → (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ := fun u p k =>
    ∑ q, sv p.1 q p.2 u * Wa u ⟨p.1, q⟩ k
  have evEq : ∀ {y₁ y₂ : CxPts (genStr T.Z) σ} (h₁ : y₁ ∈ ptsIn (genStr T.Z) σ V.1)
      (h₂ : y₂ ∈ ptsIn (genStr T.Z) σ V.1), y₁ = y₂ → evHom h₁ = evHom h₂ := by
    rintro _ _ _ _ rfl; rfl
  have key : ∀ z : CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ch₀.source →
      ch₀ (cxOf e σ hj z) ∈ Metric.ball 0 r →
      (∃ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g') ∧
      ∀ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g' →
        Dirs ⟨cxOf e σ hj z, g'⟩ (fun w => (ex (cxOf e σ hj z) w).left) (W (ch₀ (cxOf e σ hj z))) := by
    intro z hzs hzr
    have huΩ := hrΩ hzr
    have hsymm : ch₀.symm (ch₀ (cxOf e σ hj z)) = cxOf e σ hj z := ch₀.left_inv hzs
    obtain ⟨huB, -, hu1, hu2⟩ := huΩ
    rw [hsymm] at hu1 hu2
    have hzG := (cxOf_mem_image e σ hj G z).1 hu1
    have hzW : ∀ τ p q, z ∈ ptsIn X.str (σ.comp e.toRingHom) (Ws τ p q) := fun τ p q =>
      (cxOf_mem_image e σ hj _ z).1 (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hu2 τ) p) q)
    have hAz : A ∈ Eb.S (GlobalTheory.Cartier.under z) := hGA _ (CxPts.mem_ptsIn.1 hzG)
    obtain ⟨ha1, hyV', hmap⟩ := hab _ huB
    have hzV : cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 := by rw [← hsymm, ← ha1]; exact hyV'
    obtain ⟨-, hex', hco⟩ := hM z hAz hzV
    refine ⟨hex', fun g' hg' => ?_⟩
    have hov : σ = (evHom hzV).comp φ := EigLoc.spMap_inj ((cxOf e σ hj z).2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ, ← Category.assoc, spMap_evHom hzV]))
    have hx : (cxOf e σ hj z).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, spMap_evHom hzV]
    obtain ⟨fr, hfr⟩ := Φ.exists_isMap (evHom hzV) hov hx
    have hcoM := hco g' hg' fr hfr
    have hpt : (a (ch₀ (cxOf e σ hj z))).1 = cxOf e σ hj z := ha1.trans hsymm
    have hvq : ∀ τ i, fr.v τ i = (a (ch₀ (cxOf e σ hj z))).2.v τ i := fun τ i => by
      rw [hfr τ i, hmap τ i, evEq hzV hyV' hpt.symm]
    have hD : ∀ q : Pad.Letter Dw, IsDerivAt0 (fun w => (ex (cxOf e σ hj z) w).left)
        (Wa (ch₀ (cxOf e σ hj z)) q) (fr.v q.1 q.2) := fun q => by
      have tr : ∀ (x x' : CxPts (genStr T.Z) σ), x = x' → ∀ w v,
          IsDerivAt0 (fun u => (ex x u).left) w v → IsDerivAt0 (fun u => (ex x' u).left) w v := by
        rintro _ _ rfl _ _ h; exact h
      rw [hvq]
      exact tr _ _ hpt _ _ (hWa _ huB q)
    have e0 : ex (cxOf e σ hj z) 0 = 1 := by simpa using hex.2.2.2.1 _ hzs 0 0
    rintro ⟨τ, i⟩
    have hcomb := ExpDirs.isDerivAt0_of_comb (congrArg (·.left) e0) (fun k => fr.tan τ k) (fun k => hD ⟨τ, k⟩)
      (g'.tan τ i) (fr.co_spec g' τ i)
    convert hcomb using 1
    funext k
    simp only [W, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    rw [hcoM τ, Matrix.map_apply, ← hs τ q i, ratVal_fnOf (hzW τ q i)]
    show valR (ch₀.symm (ch₀ (cxOf e σ hj z))).1 _ _ = _
    rw [hsymm]
    exact valR_appIso_inv j _ _ z.1 (hzW τ q i)
  refine ⟨A, hA, r, hr, W, fun p k u hu => ?_, ?_, key⟩
  · have huΩ := hrΩ hu
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [W]
    refine DifferentiableAt.fun_sum fun q _ => (hsvd _ _ _ u huΩ).mul ?_
    exact differentiableAt_pi.1 (hWad u huΩ.1 ⟨p.1, q⟩) k
  · obtain ⟨⟨g', hg'⟩, hall⟩ := key y hys (by rw [hy0]; exact Metric.mem_ball_self hr)
    have hD := hall g' hg'
    rw [hy0] at hD
    have e0 : ex (cxOf e σ hj y) 0 = 1 := by simpa using hex.2.2.2.1 _ hys 0 0
    have h5y := hex.2.2.2.2.2 _ hys
    obtain ⟨bs, hbs⟩ := ExpDirs.dirs_basis g' (e := fun w => (ex (cxOf e σ hj y) w).left) (congrArg (·.left) e0)
      h5y.1 h5y.2 hD
    rw [← hbs]
    exact bs.linearIndependent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalSymplecticBasisAdaptedCoisotropicStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_symplecticBasis_adapted_coisotropic : ∀ (g r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ), r = 2 * g → Mᵀ = -M → M.det ≠ 0 → LinearIndependent ℚ (fun i j => (c i j : ℚ)) → (∀ v : Fin r → ℝ, (∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (c i j : ℝ)) = 0) → v ∈ Submodule.span ℝ (Set.range fun i j => (c i j : ℝ))) → ∃ (rk : ℕ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ), rk ≤ g ∧ (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 ∧ φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 ∧ φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 ∧ (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) ∧ (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) ∧ (∀ m (j : Fin g), j.val < rk → dl m j = 0) ∧ c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ := by
  first | exact @GlobalTheory.SymplecticNormalForm.exists_adapted_rational_symplectic_basis | exact GlobalTheory.SymplecticNormalForm.exists_adapted_rational_symplectic_basis | (intros; apply GlobalTheory.SymplecticNormalForm.exists_adapted_rational_symplectic_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentRefinesLieFramesGraded
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.BaseRefine

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] C.Y.Fn), Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hjo hj f hπ f₀ Eb A₀ hT hL
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.flagSpaceComponent_baseMap_of_functionFields E H Dw l Xo c O β Z F e C X j hjo hj f hπ hL
  have hgen : genericPt C.Y ≫ f = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X := hφ
  have hx : genericPt C.Y ≫ C.π ≫ genι Z = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (φ : X.Fn →+* C.Y.Fn) inferInstance hst₀ hx hc).1 C.f0
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := fun τ =>
    (Mat.det_map A₀ (φ : X.Fn →+* C.Y.Fn) τ).trans_ne ((map_ne_zero _).2 (hA₀d τ))
  set A₁ : Mat Dw.mult C.Y.Fn := M * A₀.map φ with hA₁
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => by
    rw [hA₁, Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hMu M hM τ).ne_zero (hA₀φ τ)
  have hC : f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) := by
    rw [hA₁, mul_assoc, Mat.mul_inv hA₀φ, mul_one]; exact hM
  obtain ⟨E', hT', hG⟩ := GlobalTheory.T.exists_fullFlagFamily_lieCompatible_graded E H Dw l Xo c O β Z F e C A₁ hA₁d
  have hsub := GlobalTheory.T.fullFlagFrames_flagComponent_pullback_baseFrames E H Dw l Xo c O β Z F e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hC
  exact ⟨E', φ, ⟨fun _ => Nat.zero_le _, hφ, hsub,
    GlobalTheory.T.radical_principal_ideals_stay_radical_flag_component E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ,
    GlobalTheory.T.flagSpace_unique_lift_any_field E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ E' A₁ hT' hC hsub⟩, hG⟩

end GlobalTheory.ShFam.BaseRefine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasRatioOfHasDRGaloisStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRatio_of_hasDR_galois : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → IsGalois ℚ E → ∀ (Z : Mdl Y i₀), HasDR Z → p ∣ Z.i.l.A → ∀ st (x : Letter Dw), letterOf Dw st = some x → HasRatio Z st := by
  first | exact @GlobalTheory.HTLine.Ratio.hasRatio | exact GlobalTheory.HTLine.Ratio.hasRatio | (intros; apply GlobalTheory.HTLine.Ratio.hasRatio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationDotProductStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_intCombination_dotProduct : ∀ (g r r₀ : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ u u' : Fin r₀ → ℤ, (hermForm Hm (∑ i, u i • w i) (∑ j, u' j • w j)).im = (((∑ i, u i • c i) ⬝ᵥ M *ᵥ (∑ i, u' i • c i) : ℤ) : ℝ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb_dotProduct | exact GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb_dotProduct | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb_dotProduct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeGramLocalModelAlgebraicChartHolomorphicStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeGram_localModel_algebraicChart_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ ix : Fin X.dim ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q, ∃ (φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim) (g : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ AnalyticAt ℂ φ (c'.e y) ∧ (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) (c'.e y)) ∧ (∀ τ, IsUnit (g (c'.e y) τ).det) ∧ InDom (coordOf ix (φ (c'.e y))) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∀ τ, lieGram e U hj f₀ A₀ A (c'.e.symm w) τ = (cc τ : ℂ) • (g w τ * modelGram H Dw (coordOf ix (φ w)) τ * (g w τ)ᴴ) := by
  first | exact @GlobalTheory.PointChern.lieGram_local_model | exact GlobalTheory.PointChern.lieGram_local_model | (intros; apply GlobalTheory.PointChern.lieGram_local_model <;> assumption)
end

