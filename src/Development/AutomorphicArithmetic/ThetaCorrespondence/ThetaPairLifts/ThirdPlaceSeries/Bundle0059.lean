import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Bundle0003
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0042
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProduct
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptFBOfNormalFramesStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_scalar_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP), ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.FinPl.AdaptFB (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).ψ ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).J j (σ + 1) h) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).B (j + 1 + 1) σ (idx_step h)) (N₁ (j + 1)) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).x (j + 1)).L (N₁ (j + 1 + 1)) (M₁ (j + 1 + 1) σ (idx_step h)) (PP.under (𝓞 D.host.F)) := by
  first | exact @_root_.GlobalTheory.Fam.adaptFB_of_normalFrames_alt | exact _root_.GlobalTheory.Fam.adaptFB_of_normalFrames_alt | (intros; apply _root_.GlobalTheory.Fam.adaptFB_of_normalFrames_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorPairs
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
namespace GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem anchor_pairs_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → PuNZ D → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → ∀ u, (∀ φ, ∃ C, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ) ∧ (∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ C, ∃ b, _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ ∧ _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0 := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB hPu z hzf hzc v hv u
  obtain ⟨-, hInf, -, hMatch, -, -⟩ := _root_.GlobalTheory.T.bottom_hypothesis_matching_central_alt W hB
  have hEv := GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)
    (z * (show GA D (D.sp.Y 0) from W.Q.tS)) v (by simp) hInf hB.gap hB.idE (hMatch z hzf hzc) hv
  obtain ⟨⟨j, hjbij, hj⟩, -⟩ := hEv
  have hF := hB.fin
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  have hpair : ∀ (Tm : MultT W.Q.Rl.θ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)) (C : Cu W.S.X u W.S.Y.hK),
      _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) C
        ⟪((j Tm : HHX W.S.X) : L2X W.S.X), PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C⟫_ℂ := by
    intro Tm C
    unfold _root_.GlobalTheory.MiTop.IsPairing'
    let g : L2X W.S.X := ((j Tm : HHX W.S.X) : L2X W.S.X)
    have hg : (g : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] fun x => star (evS W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) x) := hj Tm
    refine ⟨star g, ?_, ?_⟩
    · have h1 : ((star g : L2X W.S.X) : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] star (g : W.S.X.B.I.GA → ℂ) := MeasureTheory.Lp.coeFn_star g
      refine h1.trans ((hg.fun_comp star).trans (Filter.EventuallyEq.of_eq ?_))
      funext x
      exact star_star _
    · rw [star_star]
  refine ⟨fun φ => ?_, fun T hT C => ⟨_, hpair ⟨T, hT⟩ C⟩, ?_⟩
  · obtain ⟨C, hC⟩ := (W.S.bij u).2 (D.eMu u φ).1 (hram (D.eMu u φ).2)
    exact ⟨C, hC⟩
  · obtain ⟨φr, hφr⟩ := hPu u
    let x := (D.s_Cu u).symm ⟨φr.1, φr.2.1⟩
    let C : Cu W.S.X u W.S.Y.hK := (W.S.hI hF).eCu u x
    have hpin := W.S.colPin hF u x
    have hC : _root_.GlobalTheory.MiTop.IsColumnForm W u C ((D.eMu u).symm φr) := by
      show Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK C = _
      rw [LinearEquiv.apply_symm_apply, ← Formalism.L2.SG.ColDict.colDict_apply W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)]
      have hpin' : Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u) C = D.s_Cu u x := hpin
      rw [hpin', LinearEquiv.apply_symm_apply]
    let P : HHX W.S.X := (Formalism.L2.SG.PackageTie2.sOf hF).Pu u C
    have hP : P ≠ 0 := by
      have e := (W.S.hI hF).Pu_eq u x
      intro h0
      apply hφr
      have : (W.S.hI hF).eHH (D.s.Pu u x) = 0 := e.trans h0
      exact (LinearIsometryEquiv.map_eq_zero_iff _).1 this
    obtain ⟨Tm, hTm⟩ := hjbij.2 P
    refine ⟨(D.eMu u).symm φr, C, _, Tm.1, Tm.2, hC, hpair Tm C, ?_⟩
    rw [hTm]
    have hPv : ((P : HHX W.S.X) : L2X W.S.X) = PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C := rfl
    rw [hPv]
    refine inner_self_ne_zero.2 ?_
    rw [← hPv]
    exact fun h => hP (Subtype.ext h)
end GlobalTheory.MiTop
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotRelTwo
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting GlobalTheory.Core.Rk
noncomputable section
namespace GlobalTheory.MiTop.BotTwo
variable {D : D7}
end GlobalTheory.MiTop.BotTwo
set_option maxHeartbeats 1000000 in
open GlobalTheory.MiTop.BotTwo in
theorem GlobalTheory.MiTop.botRel_of_pin_of_mem_center : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u), d.Pin z → _root_.GlobalTheory.MiTop.BottomRelation W z d := by
  intro _ hCR D L hT Gi Gl Kc Yd cX ex W hB z hzf hzc u d hP
  obtain ⟨-, hθ, hψ, hMatch, hχ, -⟩ := _root_.GlobalTheory.MiTop.botHyp_match_alt W hB
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.T.exists_isometry_colForm_eq_rTrans_of_pin W hB u d z hP
  obtain ⟨ξ, hξspan, hξ⟩ := GlobalTheory.T.dictionaryColumnScalarForm_eq_traceColumnForm D W.S.X W.Q.instEq u W.Q.Rl.ψ d.B (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) W.S.Y.hK W.Q.Rl.θ d.a₀
    hθ hB.idE hP.adapted hP.h0 (hB.hyp.2.1 u)
  have hRS := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D W.S.X W.Q.instEq W.Q.Rl.θ hθ hB.idE
  obtain ⟨c, hc⟩ := GlobalTheory.T.conjugateRow_pairing_poincareSeries_besselPeriods D W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0) d.B W.S.Y hψ (hB.fin.inHH u)
  have hMt := hMatch z hzf hzc
  have hf1 : (iotaX W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS))).1 = 1 := (hRS.1 _).1 hMt.1
  have hcont : ∀ (C : Cu W.S.X u W.S.Y.hK) ξ', IsContAut (D.sp.X 0) (d.B.colForm C.1 ξ') := fun C =>
    (GlobalTheory.Core.Mi.PhCol.ph_colForm D W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0) d.B W.S.Y.hK C).1
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)
  have hcol : ∀ φ : D.what₂.Mu u, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK
      (e.symm (Submodule.inclusion hram (D.eMu u φ))) = (D.eMu u φ).1 := fun φ =>
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram (D.eMu u φ)))
  have L1 : ∀ (φ : D.what₂.Mu u) (C : Cu W.S.X u W.S.Y.hK), _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ y v,
      d.per φ T y v = _root_.GlobalTheory.MiTop.realCharacter W d.k * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) := by
    intro φ C hC T hT y v
    have hC₀ : _root_.GlobalTheory.MiTop.IsColumnForm W u (e.symm (Submodule.inclusion hram (D.eMu u φ))) φ := hcol φ
    have e1 : (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y =
        fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹) := by
      rw [← hcol φ]
      funext g
      rw [hξ _ y g, hR φ C _ hC hC₀ (ξ y)]
      simp only [rTrans]
      congr 1
      rw [mul_assoc, mul_inv_rev, (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hP.cen) d.a₀⁻¹)]
    have e2 : rTrans (embA d.B.d d.B.o (d.a₀ * d.a)) (rTrans d.b (T v)) =
        _root_.GlobalTheory.MiTop.realCharacter W d.k • rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v) := by
      funext g
      simp only [rTrans, Pi.smul_apply, smul_eq_mul]
      rw [mul_assoc g, hP.eq]
      refine Eq.trans (congrArg (T v) ?_) (lev_multT hT v hP.lev
        (g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) : GA D (D.sp.Y 0)))
      change g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k)) =
        g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) * d.k
      rw [mul_assoc g, mul_assoc ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))]
    have ea : rTrans (d.a₀ * d.a) (fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹)) = d.B.colForm C.1 (ξ y) := by
      funext g; simp only [rTrans, mul_inv_cancel_right]
    have hsh := GlobalTheory.Core.Mi.per_rTrans D W.Q.Rl.ψ D.R.rS d.B.lev (fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹))
      (rTrans d.b (T v)) (d.a₀ * d.a) hψ (contAut_rTrans _ (hcont C (ξ y))) (contAut_rTrans _ (contAut_multT hT v))
    rw [ea] at hsh
    unfold _root_.GlobalTheory.MiTop.BottomData.per
    rw [e1, ← hsh, ← per_smul_f]
    exact congrArg _ e2
  refine ⟨R, ?_⟩
  intro φ φ' T hT T' hT' α α' hrel v C C' b b' hC hC' hb hb'
  have hrelξ : ∀ y v, α * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) +
      α' * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C'.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T' v)) = 0 := by
    intro y v
    have h0 := hrel y v
    rw [L1 φ C hC T hT, L1 φ' C' hC' T' hT'] at h0
    refine (mul_eq_zero.1 ?_).resolve_left (hχ _ hP.lev)
    rw [← h0]; ring
  have hrelAll : ∀ ξ' v, α * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 ξ')
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) +
      α' * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C'.1 ξ')
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T' v)) = 0 := by
    intro ξ' v
    have hmem : ξ' ∈ Submodule.span ℂ (Set.range ξ) := by rw [hξspan]; exact Submodule.mem_top
    obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
    have hlin : ∀ C₁ : Cu W.S.X u W.S.Y.hK, d.B.colForm C₁.1 ξ' = ∑ i ∈ cf.support, cf i • d.B.colForm C₁.1 (ξ i) := by
      intro C₁
      rw [← hcf]
      funext g
      simp only [SBes.colForm, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    rw [hlin C, hlin C',
      GlobalTheory.SeeSaw.perSum_all D W.Q.Rl.ψ hψ D.R.rS d.B.lev _ (contAut_rTrans _ (contAut_multT hT v)) _ cf.support cf
        (fun i => d.B.colForm C.1 (ξ i)) (fun i _ => hcont C (ξ i)),
      GlobalTheory.SeeSaw.perSum_all D W.Q.Rl.ψ hψ D.R.rS d.B.lev _ (contAut_rTrans _ (contAut_multT hT' v)) _ cf.support cf
        (fun i => d.B.colForm C'.1 (ξ i)) (fun i _ => hcont C' (ξ i)),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := hrelξ i v
    linear_combination cf i * this
  have hσ : ∀ y : W.S.X.B.I.Ginf, ∃ σ : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] SmT (W.Q.Rl.MY 0), ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ x,
      T (σ x) = rTrans ((iotaX W.S.X W.Q.instEq).symm (y, 1)) (T x) := by
    intro y
    obtain ⟨σ, hσ⟩ := GlobalTheory.RealTransSm.rTrans_eq_map D W.Q.Rl.θ (D.sp.Y 0) _ (W.Q.Rl.MY 0) hθ
      ((iotaX W.S.X W.Q.instEq).symm (y, 1))
      ((hRS.2.1 _).2 (congrArg Prod.snd ((iotaX W.S.X W.Q.instEq).apply_symm_apply (y, 1))))
    exact ⟨σ, fun T hT x => hσ (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) T hT x⟩
  choose σ hσ using hσ
  have hpt : ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ v (y : W.S.X.B.I.Ginf),
      (fun g => evS W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T v)
        (iotaX W.S.X W.Q.instEq g * (y, W.S.X.xu u))) =
      rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T (σ y v)) := by
    intro T hT v y
    funext g
    rw [hσ y T hT v]
    simp only [evS, rTrans]
    exact congrArg (T v) (shift_swap (iotaX W.S.X W.Q.instEq).toMulEquiv g _ y (W.S.X.xu u) hf1)
  obtain ⟨φL, hφL, rfl⟩ := hb
  obtain ⟨φL', hφL', rfl⟩ := hb'
  rw [hc C _ φL (GlobalTheory.Core.Mi.rowFun_evS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) _ hθ hMt T hT v).1 hφL,
    hc C' _ φL' (GlobalTheory.Core.Mi.rowFun_evS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) _ hθ hMt T' hT' v).1 hφL']
  refine comb_integral _ c α α' _ _ fun y => ?_
  refine Eq.trans ?_ (hrelAll (W.S.X.Wu u y) (σ y v))
  exact congrArg₂ (fun p q => α * p + α' * q) (congrArg (d.B.lev.per W.Q.Rl.ψ _) (hpt T hT v y))
    (congrArg (d.B.lev.per W.Q.Rl.ψ _) (hpt T' hT' v y))
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CFacts
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalC
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory Tr
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem pre_cut_alt {c : CutD D} (hc : c.Good) {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) : _root_.UpperTheory.GalC.GaloisPreconditions (cut D c) (nchCut c x) :=
  have R := _root_.UpperTheory.GalC.Tr.rs_cut_of_good_aux41 hc h.Conclusion1.1 h.what₂
  have A := _root_.UpperTheory.GalC.Tr.admissible_cut (c := c) h.adm
  have lam : GlobalTheory.NRows.LamUsed (cut D c) := h.lam
  { what₂ := R
    adm := A
    Conclusion1 := _root_.UpperTheory.GalS.Parts.main_alt_alt _ A.1 R.a.tieLab R.b.rowSize R.a.hecke lam.loc R.b.thetaOne R.a.g4p
    z := pointsAdmissible_restrictToPoints hc h.z
    rhoBar := rhoBar_cut h.rhoBar
    g3p := _root_.UpperTheory.GalC.Tr.admissible_tame_eigenvalues_of_cut h.g3p
    weight := fun i => h.weight i.1
    block := fun i => h.block i.1
    muUnr := fun i => h.muUnr i.1
    depthG := fun i => h.depthG i.1
    bc := h.bc
    lam := lam
    c2 := jointCondition_restrictToPoints h.c2
    large := large_cut h.large
    nct := nct_cut c h.nct
    trip := fun a => h.trip a.1
    same := fun a => h.same a.1
    good := h.good }
theorem facts_of_galois_preconditions_of_cutRec (hCh : GlobalTheory.TwSys.Cheb) (lf : LocalFiniteness) (ltd : LocalTateDuality) (lec : LocalEulerChar)
    {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) (hC : CutRec D) : _root_.GlobalTheory.NFacts.NormChoiceFacts D x :=
  have ex : GlobalTheory.StringRepresentationDecomposition.RbEx D := GlobalTheory.T.residualRankPartExists_of_jointCondition D h.what₂.c.rho
  have h0 : SumRepresentations.tie0 D := h.adm.1.1.1
  have h1 : SumRepresentations.adm1 D := h.adm.1.1.2.2.1
  have g2 := _root_.UpperTheory.GalS.de_rham_points_weight_jumps_alt D h0 h1 h.what₂.a.a2 h.what₂.a.a5 hC
  { what₂ := h.what₂, adm := h.adm, Conclusion1 := h.Conclusion1
    Conclusion2 := ⟨_root_.UpperTheory.GalS.prvG5_of_admissible_cutRec lf ltd lec D h.adm ex hC, _root_.GlobalTheory.T.prvG6_of_admissible' D h.adm ex, h.z⟩
    rhoBar := h.rhoBar, g3p := h.g3p, weight := h.weight, block := h.block, g2 := g2
    admJ := fun L hL => _root_.UpperTheory.GalS.admJ_of_admPar D L h0 h1 h.what₂.a.a2 h.what₂.a.a5 hC h.weight h.block hL
    muUnr := h.muUnr, depthG := h.depthG, bc := h.bc, lam := h.lam, c2 := h.c2, large := h.large
    duties := _root_.UpperTheory.GalS.duties_of_large_aux41 hCh D h.large h.Conclusion1.1 g2.2 h.rhoBar
    nct := h.nct, trip := h.trip, same := h.same, good := h.good }
theorem exists_good_cut_facts_tie4 (hCh : GlobalTheory.TwSys.Cheb) (lf : LocalFiniteness) (ltd : LocalTateDuality) (lec : LocalEulerChar)
    {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) (hT : Tie4 D) :
    ∃ c : CutD D, c.Good ∧ _root_.GlobalTheory.NFacts.NormChoiceFacts (cut D c) (nchCut c x) ∧ Tie4 (cut D c) := by
  obtain ⟨c, hc⟩ := _root_.UpperTheory.GalC.exists_good_alt (GlobalTheory.T.central_elements_from_idempotent_coeffs GlobalTheory.CentralIdem.centralIdemCoeff) h hT
  exact ⟨c, hc, _root_.UpperTheory.GalC.facts_of_galois_preconditions_of_cutRec hCh lf ltd lec (_root_.UpperTheory.GalC.pre_cut_alt hc h) (cutRec_cut hc), compatibilityTies_eigenRestriction c hT⟩
end UpperTheory.GalC
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CIMulIdx
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.StepConst
variable {D : D7}
theorem cI_mul_idx_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → ∀ j, j < D.R.m → (f.t t).cI j * ∏ i, ((F.Q i).idx (j + 1) : ℂ) = (f.t W.P.A3.A.μ0).cI j := by
  intro D L hT Gi Gl Kc Yd cX ex W u f _ hRow v hv hVT t w F hPins hQL j hj
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := W.Q.charW.base.lev
  have hQ0 := base_empty hL
  obtain ⟨pl, hpl⟩ := hQL.places
  have hq : ∀ i, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, PP'.under (𝓞 D.host.F) = (F.Q i).q.v → PP' = (pl i).1 := fun i PP' h e => by
    have e1 := (hpl (pl.symm ⟨PP', h⟩)).2
    rw [Equiv.apply_symm_apply] at e1
    have e2 : pl.symm ⟨PP', h⟩ = i := hPins.inj (e1.trans e)
    rw [← e2, Equiv.apply_symm_apply]
  have hg : ∀ i, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP'.under (𝓞 D.host.F) ≠ (F.Q i).q.v := fun i PP' h => by
    rw [(hpl i).2]
    exact under_ne hL t (pl i).2 h
  have hgP : ∀ i, (F.Q i).q.v ∉ v.gP := fun i h => by
    obtain ⟨PP, h1, h2⟩ := (hVT.gP _).1 h
    exact hg i PP h1 h2.symm
  have hP : ∀ PP : Pl D.host.E, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 → ¬ PP.under (𝓞 D.host.F) ∈ w.Q := by
    rintro PP (h | h) h'
    · obtain ⟨i, hi⟩ := (hPins.places _).1 h'
      exact hg i PP h hi.symm
    · rw [hQ0] at h
      exact absurd h (Finset.notMem_empty _)
  have key : GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t j * ∏ i, ((F.Q i).idx (j + 1) : ℝ) = GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g W.P.A3.A.μ0 j := by
    unfold GlobalTheory.Fam.volLev
    split_ifs with h1
    · generalize j + 1 = J at h1
      have hb : f.g.b J ∈ GfC (Yc D J) := by rw [← hVT.b J]; exact hv.b J
      have hΛ : ((_root_.GlobalTheory.Fam.pk_z W).ΛY J).FG := (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY J h1)).1.fg
      have hβ : IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).ΛY J) := (hL.βY J h1).choose_spec.1
      obtain ⟨a1, a2, a3, a4, a5⟩ := moved_level (V := Yc D J) (N := v.N J) (P := (· ∈ w.Q)) hβ hΛ ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 J (_root_.GlobalTheory.Fam.pk_z W).triv) hP hb
        (hVT.moves J h1 _ fun p hp => by
          obtain ⟨i, rfl⟩ := (hPins.places _).1 hp
          exact hgP i)
      have loc : ∀ i d hd (g : GA D (Yc D J)), finE (Yc D J) ((f.g.b J)⁻¹ * g * f.g.b J) ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY J) → ∀ x,
          (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY J d hd).β * x.val * ((F.Q i).FY J d hd).γ →
          (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY J) (pl i).1 (finE (Yc D J) ((f.g.b J)⁻¹ * g * f.g.b J)) ∈ blockTri (blk2 D.R.r) ↔
            x ∈ ((F.Q i).T.lev J d hd).J) := fun i d hd g hS x hx => by
        refine red_iff_local (N := v.N J) (F.Q i).q ((F.Q i).FY J d hd) _ hβ hΛ ((_root_.GlobalTheory.Fam.pk_z W).datYt t J (_root_.GlobalTheory.Fam.complexLevelStructure W)) (pl i).2 (hpl i).2
          (hg i) (hq i) hb (hVT.moves J h1 _ fun p hp => hp ▸ hgP i) ((F.Q i).latY J d hd) (fun y hy c hc => ?_) hS hx
        obtain ⟨gl, -, -, hu⟩ := GlobalTheory.LocEmb.exists_gl D _ (F.Q i).q (Yc D J) _ ((F.Q i).FY J d hd)
        have e : c = (F.Q i).gl J d hd y :=
          (hu c y hc.1 hc.2).trans (hu _ y ((F.Q i).gl_loc J d hd y).1 ((F.Q i).gl_loc J d hd y).2).symm
        rw [e]
        exact (hQL.mid i J d hd h1 y hy).1
      have hA := (GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index D f.c v (f.t t) w F hPins).1 J h1 (hv.sd J h1) (f.g.μf J) (hRow.meas.μf J) _
        (moved (f.g.b J) (levG (Yc D J) ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).datYt t J (_root_.GlobalTheory.Fam.pk_z W).triv))) (f.g.b J) hb a1 a2 a3 a4 a5 fun g => by
          refine (mem_moved _ _ g).trans ((mem_levG_iff_base _ _ _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) hQ0 _).trans
            ((and_congr_right fun h0 => ?_).trans (and_congr_left' (mem_moved _ _ g).symm)))
          have hS := parLev_St (lev_le_parLev h0.2)
          refine ⟨fun H i d hd x hx => (loc i d hd g hS x hx).1 (H _ (pl i).2), fun H PP hPP => ?_⟩
          obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
          have hs := (F.Q i).hs
          have hd : J + ((F.Q i).s + 1 - J) = (F.Q i).s + 1 := by omega
          obtain ⟨x, hx⟩ := exists_mat (F.Q i).q ((F.Q i).FY J _ hd) g
          have := (loc i _ hd g hS x hx).2 (H i _ hd x hx)
          rw [hi] at this
          exact this
      have e1 := moved_set (f.g.b J) (levG (Yc D J) ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).datYt t J (_root_.GlobalTheory.Fam.pk_z W).triv))
      have e2 := moved_set (f.g.b J) (levG (Yc D J) ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 J (_root_.GlobalTheory.Fam.pk_z W).triv))
      rw [e1, e2] at hA
      exact hA
    · have hjm : j + 1 = D.R.m := by omega
      rw [hjm]
      have hb : f.g.bT ∈ GfC D.sp.X' := by rw [← hVT.bT.1]; exact hv.bT
      have hΛ : (_root_.GlobalTheory.Fam.pk_z W).ΛX.FG := (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX).1.fg
      have hβ : IsFrame (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.Fam.pk_z W).ΛX := hL.βX.choose_spec.1
      have hm : ∀ P, GlobalTheory.FinPl.Moves D.sp.X' f.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX v.NT P := fun P => by
        rw [hVT.bT.2]
        exact hVT.movesT P
      obtain ⟨a1, a2, a3, a4, a5⟩ := moved_level (V := D.sp.X') (N := v.NT) (P := (· ∈ w.Q)) hβ hΛ ((_root_.GlobalTheory.Fam.pk_z W).datXt W.P.A3.A.μ0) hP hb (hm _)
      have loc : ∀ i (g : GA D D.sp.X'), finE D.sp.X' (f.g.bT⁻¹ * g * f.g.bT) ∈ St (_root_.GlobalTheory.Fam.pk_z W).βX → ∀ x : GL (F.Q i).Z (F.Q i).k,
          (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ →
          (redFn (_root_.GlobalTheory.Fam.pk_z W).βX (pl i).1 (finE D.sp.X' (f.g.bT⁻¹ * g * f.g.bT)) ∈ blockTri (blk2 D.R.r) ↔
            x ∈ (F.Q i).T.levTop.J) := fun i g hS x hx =>
        red_iff_local (N := v.NT) (F.Q i).q (F.Q i).FT _ hβ hΛ (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (pl i).2 (hpl i).2
          (hg i) (hq i) hb (hm _) (F.Q i).latT (hQL.top i) hS hx
      have hA := (GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index D f.c v (f.t t) w F hPins).2 hv.sdT (fun i => (F.Q i).openT) f.g.μT hRow.meas.μT _
        (moved f.g.bT (levG D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t))) f.g.bT hb a1 a2 a3 a4 a5 fun g => by
          refine (mem_moved _ _ g).trans ((mem_levG_iff_base _ _ _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) hQ0 _).trans
            ((and_congr_right fun h0 => ?_).trans (and_congr_left' (mem_moved _ _ g).symm)))
          have hS := parLev_St (lev_le_parLev h0.2)
          refine ⟨fun H i x hx => (loc i g hS x hx).1 (H _ (pl i).2), fun H PP hPP => ?_⟩
          obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
          obtain ⟨x, hx⟩ := exists_mat (F.Q i).q (F.Q i).FT g
          have := (loc i g hS x hx).2 (H i x hx)
          rw [hi] at this
          exact this
      have e1 := moved_set f.g.bT (levG D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t))
      have e2 := moved_set f.g.bT (levG D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt W.P.A3.A.μ0))
      rw [e1, e2] at hA
      exact hA
  show cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g t j * _ = cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g W.P.A3.A.μ0 j
  unfold cIOf
  rw [← key]
  push_cast
  ring
end GlobalTheory.StepConst
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiCompatPkStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_at_level_place_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : Formalism.IndefR.Datum.EAf D →+* k, (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi j PP) μ := by
  first | exact @_root_.GlobalTheory.Fam.chi_compat_pk_alt | exact _root_.GlobalTheory.Fam.chi_compat_pk_alt | (intros; apply _root_.GlobalTheory.Fam.chi_compat_pk_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClosingFamilyX
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory
theorem closingFamilyX_alt_alt : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D) (X : KillingConditions.HubData D), _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.PtCore.PtFam D X.r X.ρ → (∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i) → (∀ i, AbsIrreducibleDistinct D i (X.r i)) ∧ (∀ i, KillingConditions.RangeAD large₂ X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i)) ∧ (∀ i π, EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i))
:= by
  intro hF hK D HW F large₂ X hJ hA hP h41 hO hX hcB
  refine ⟨fun i => UpperTheory.GalS.jc_of_u (hX.good i) hO (_root_.UpperTheory.GalS.g3a_of_restricted_general_alt h41 hA.2.2.1 i _ (hX.good i)), fun i hR π => ?_,
    fun i hl π hπ => ?_, fun i π => GlobalTheory.Pass.ambient_h1f_of_local_finiteness hK D i _ π _ (hX.cont i π)⟩
  · exact GlobalTheory.BlockWindow.jointCond_TB_at_range D HW F large₂ (hJ large₂ hA) hP i _ π _ (fun h => hR.1 (Or.inl h))
      (fun h => hR.2.1 (Or.inl h)) (fun h => hR.2.1 (Or.inr h)) (hX.good i) (hcB i)
  · have hp := _root_.GlobalTheory.T.ptIn_of_ptFam_deRham_away hF D X hX hA.1 i hl π hπ
    intro _ w hw _ C τ a
    have hd : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (X.r i π) (X.ρ i π) (D.nd.chi i) e := by
      obtain ⟨e, he⟩ := hp.dec
      exact ⟨e, fun g u => he g u⟩
    have := D.nd.lPrime i
    have := C.LL.2
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ C.LL _ _ (hp.crys w hw C π)).1
    exact (((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le (X.r i) (X.ρ i) π hd).2 hdr).2.2 τ a).2
end GlobalTheory
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CondUnifStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_conductor_one_exists_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (PP : Pl D.host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → ∀ l : LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∃ ψk : AddChar l.k Circle, (ofSplit l.q).IsChar (_root_.GlobalTheory.Fam.pk_z W).ψ ψk ∧ HasConductor ψk 1) ∧ (∃ ν : Measure l.k, IsUnitVol ν) ∧ (_root_.GlobalTheory.Fam.QAllAlt W PP → ∃ ϖ : l.kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (l.q.pr.comp (incA D)) ϖ) := by
  first | exact @_root_.GlobalTheory.WeilCondUnif.cond_unif_alt | exact _root_.GlobalTheory.WeilCondUnif.cond_unif_alt | (intros; apply _root_.GlobalTheory.WeilCondUnif.cond_unif_alt <;> assumption)
end
end

