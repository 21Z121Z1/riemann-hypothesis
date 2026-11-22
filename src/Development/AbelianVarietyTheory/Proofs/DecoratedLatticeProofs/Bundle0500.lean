import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0491
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0173
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0495
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlaceStabilizerPartialProductsFiniteSet
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseTermNormCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

set_option maxHeartbeats 1000000 in

theorem base_term_norm_coords : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∀ g : GA D V, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ = ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ G Φ hG hΦ 𝓐 𝓑 hlay g
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  have hTL := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS
  have hsplit : ∀ (n : GA D V) (h : GA D W), om (n * g, h) Φ = om (n, 1) (om (g, h) Φ) := by
    intro n h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hψn : ∀ x, ‖ψ x‖ₑ = 1 := fun x => by
    rw [← ofReal_norm_eq_enorm, hω.std.1.2.1 x, ENNReal.ofReal_one]
  have hFm : Measurable (fun p : flagN d × GA D W =>
      ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ) := by
    refine Continuous.measurable ?_
    refine ((hG.2.1.comp continuous_snd).mul ?_).enorm
    exact ((hTL Φ hΦ).2.2.2.1 x₀).comp
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hfib : ∀ h : GA D W, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
      ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν =
      ∫⁻ n in 𝓐, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) x₀‖ₑ ∂vN.ν := by
    intro h
    have hΨ : IsThetaFunO ψ V W (om (g, h) Φ) := hω.om_pres (g, h) Φ hΦ
    have hfm : Measurable (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) :=
      (((hTL _ hΨ).2.2.2.1 x₀).comp (continuous_id.prodMk continuous_const)).enorm.measurable
    have hinv : ∀ c, ∀ n ∈ flagN d,
        (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) (d.nC c * n) =
        (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) n := by
      intro c n hn
      have hΨ' := hω.om_pres (n, 1) _ hΨ
      have t1 := (hTL _ hΨ').1 x₀ 0 1 c
      rw [d.nB_zero, OneMemClass.coe_one, map_one, mul_one, mul_one, ← Module.End.mul_apply, ← map_mul,
        Prod.mk_mul_mk, one_mul] at t1
      show ‖term ψ d W vS (om (d.nC c * n, 1) (om (g, h) Φ)) x₀‖ₑ =
        ‖term ψ d W vS (om (n, 1) (om (g, h) Φ)) x₀‖ₑ
      rw [t1, enorm_mul, hψn, one_mul]
      simp [term]
    have hval : ∀ (u : UX D ρ) (b : Mx D ρ V₀.rank),
        ‖term ψ d W vS (om (d.nB b * d.levi u.1, 1) (om (g, h) Φ)) x₀‖ₑ =
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ := by
      intro u b
      have t1 := (hTL _ hΨ).1 x₀ b u 0
      rw [d.nC_zero, one_mul] at t1
      rw [t1, enorm_mul, hψn, one_mul]
    have hl := hlay _ hfm hinv
    calc ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
          ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν
        = ‖G h‖ₑ * ∫⁻ n in 𝓐, ‖term ψ d W vS (om (n.1, 1) (om (g, h) Φ)) x₀‖ₑ ∂vN.ν := by
          rw [hl]
          simp only [hval]
      _ = ∫⁻ n in 𝓐, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) x₀‖ₑ ∂vN.ν := by
          rw [← lintegral_const_mul' _ _ enorm_ne_top]
          refine lintegral_congr fun n => ?_
          rw [enorm_mul, hsplit]
  rw [← Measure.prod_restrict, lintegral_prod_symm _ hFm.aemeasurable]
  refine lintegral_congr fun h => ?_
  exact hfib h

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiMapCarriesNormalFrameLinesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobiMap_carries_normalFrameLines : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.ColsAt ((y.bes j ρ h).lev (a.x j).vol).d (xZero ((y.jac j ρ h).lev (a.x (j + 1)).vol).d) (N j) (N (j + 1)) (PP.under (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.ColsXZeroNormal.colsAt_xZero_of_normalFr | exact GlobalTheory.ColsXZeroNormal.colsAt_xZero_of_normalFr | (intros; apply GlobalTheory.ColsXZeroNormal.colsAt_xZero_of_normalFr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepKernelPreservesLevelRamifiedFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainStepKernel_preserves_levelRamifiedForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ φ : ColT I l u a i, RamT i φ → RamT (i + 1) ((I.chain l u a).K i φ) := by
  first | exact @GlobalTheory.KRamT.kernel_keeps_ramT | exact GlobalTheory.KRamT.kernel_keeps_ramT | (intros; apply GlobalTheory.KRamT.kernel_keeps_ramT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesSplitUnramifiedQuotientsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainTwistPlaces_split_unramifiedQuotients : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → (∀ v, v ∈ c.S ↔ v ∈ w.S₀ ∨ ∃ PP ∈ w.Q, PP.under (𝓞 D.host.F) = v) ∧ (∀ PP ∈ w.Q, PP.under (𝓞 D.host.F) ∉ w.S₀) ∧ Set.InjOn (fun PP : Pl D.host.E => PP.under (𝓞 D.host.F)) w.Q ∧ (∀ PP ∈ w.Q, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (PP.under (𝓞 D.host.F)) ∧ Ideal.absNorm (PP.under (𝓞 D.host.F)).asIdeal = Ideal.absNorm PP.asIdeal ∧ ∃ PP' : Pl D.host.E, PP' ≠ PP ∧ (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) ↔ P = PP ∨ P = PP') ∧ Ideal.absNorm PP'.asIdeal = Ideal.absNorm PP.asIdeal ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP' = (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP)⁻¹) ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.UnrOff (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w.S₀ := by
  first | exact @GlobalTheory.ChainTw.twist_places | exact GlobalTheory.ChainTw.twist_places | (intros; apply GlobalTheory.ChainTw.twist_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePairDatumRationalApproxEqTwistedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBasePair_datum_rational_approx_eq_twisted : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) g g', g ∈ GfC _ → g' ∈ GfC _ → finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g = ((A.K i (Nat.le_of_succ_le hi) (A.chOf i c)).y ⟨c, rfl⟩).1.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) g' = ((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1.1 → ∃ M : ℕ, 0 < M ∧ ∀ (γ γ₀ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → γ₀.map (fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ g⁻¹ g'⁻¹ (γ.map fun r => A.e * incA (I.rec7 l Z) r) + M • v → A.xi i hi (A.chOf i c) (A.chOf (i + 1) c') γ₀ = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ)) := by
  first | exact @GlobalTheory.AdForm.TwResid.tw_resid_datum | exact GlobalTheory.AdForm.TwResid.tw_resid_datum | (intros; apply GlobalTheory.AdForm.TwResid.tw_resid_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePointsLevelDatumEqLocalProdStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBasePoints_levelDatum_eq_local_prod : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) (α : Ch j) (γ : Ch (j + 1))
      (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E),
      B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z)) =
        (J.map fun i => phiOne (Q j i) (Q (j + 1) i) (rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z))))).prod := by
  first | exact @GlobalTheory.PhiOneVal.phiT_base_eq_prod | exact GlobalTheory.PhiOneVal.phiT_base_eq_prod | (intros; apply GlobalTheory.PhiOneVal.phiT_base_eq_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.ChartReps

section Gen
variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (y : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  (U : Subgroup (GA D V)) (hU : ∀ g, g ∈ U ↔ g ∈ GfC V ∧ ∃ κ : S.U, κ.1.1 = finM V hn g)
  (h : cl → GA D V) (hh : ∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (y c).1.1)

def finHomN : GA D V →* GL (Fin n) (EF D) where
  toFun g := GlobalTheory.AdForm.Model.finGL V hn g
  map_one' := Units.ext (GlobalTheory.AdForm.Model.finM_one V hn)
  map_mul' g g' := Units.ext (GlobalTheory.AdForm.Model.finM_mul V hn g g')

theorem finHomN_val (g : GA D V) : (finHomN V hn g).1 = finM V hn g := rfl

theorem finHomN_eq_one (g : GA D V) : finHomN V hn g = 1 ↔ g ∈ GinfC V := by
  rw [Units.ext_iff, finHomN_val, Units.val_one, GlobalTheory.AdForm.finM_eq_one_iff_mem_GinfC D V n hn g]

include hU in

theorem lift_mem (e : ↥(GfC V) ≃* ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (he : ∀ g, (e g).1.1 = finM V hn g.1) (κ : S.U) :
    (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 ∈ U ∧ finM V hn (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 = κ.1.1 := by
  have h1 : finM V hn (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 = κ.1.1 := by rw [← he, e.apply_symm_apply]
  exact ⟨(hU _).2 ⟨(e.symm _).2, κ, h1.symm⟩, h1⟩

include hU hh in
set_option maxHeartbeats 1000000 in

theorem reps_of_chart (hy : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S))) : IsReps V U h := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V n hn
  obtain ⟨r, hr⟩ := GlobalTheory.RatPtsEquiv.rat_equiv D V n hn
  have hmemU : ∀ (g : GfC V), g.1 ∈ U ↔ (e g).1 ∈ S.U := by
    intro g
    rw [hU]
    constructor
    · rintro ⟨_, κ, hκ⟩
      have : (e g).1 = κ.1 := Units.ext ((he g).trans hκ.symm)
      rw [this]; exact κ.2
    · intro hx; exact ⟨g.2, ⟨(e g).1, hx⟩, he g⟩
  have hΦe : ∀ g : GfC V, finHomN V hn g.1 = (e g).1 := fun g => Units.ext (he g).symm
  refine ⟨fun g hg => ((hU g).1 hg).1, ?_, ?_, fun c => (hh c).1, ?_, ?_⟩
  · have hset : (U : Set (GA D V)) = (fun x => (e.symm x).1) '' {x | x.1 ∈ S.U} := by
      ext g
      constructor
      · intro hg
        have hgf := ((hU g).1 hg).1
        exact ⟨e ⟨g, hgf⟩, (hmemU ⟨g, hgf⟩).1 hg, by simp only [e.symm_apply_apply]⟩
      · rintro ⟨x, hx, rfl⟩
        exact (hmemU _).2 (by rw [e.apply_symm_apply]; exact hx)
    have hc : IsCompact {x : ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) | x.1 ∈ S.U} := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert S.U_compact using 1
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hz; exact ⟨⟨z, ((S.U_eq z).1 hz).1⟩, hz, rfl⟩
    rw [hset]
    exact hc.image (continuous_subtype_val.comp e.symm.continuous)
  · have : ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) = e ⁻¹' {x | x.1 ∈ S.U} := by
      ext g
      exact (Subgroup.mem_subgroupOf).trans (hmemU g)
    rw [this]
    exact S.U_open.preimage e.continuous
  · intro g
    obtain ⟨p, hpq⟩ : ∃ p : GinfC V × GfC V, g = p.1.1 * p.2.1 :=
      ⟨(GlobalTheory.AdelicSplit.splitEquiv V).symm g, ((GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g).symm⟩
    obtain ⟨⟨c, δ, κ0⟩, hδ, hdec⟩ := GlobalTheory.AdForm.Model.exists_dec V hn S y hy.2 p.2.1
    obtain ⟨κ, hκU, hκf⟩ : ∃ κ ∈ U, finM V hn κ = κ0.1.1 :=
      ⟨_, (lift_mem V hn S U hU e.toMulEquiv he κ0).1, (lift_mem V hn S U hU e.toMulEquiv he κ0).2⟩
    obtain ⟨γ, hγ, hΦγ⟩ : ∃ γ ∈ GQ V, finHomN V hn γ = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ := by
      refine ⟨(r.symm ⟨δ, hδ⟩).1, (r.symm ⟨δ, hδ⟩).2, ?_⟩
      apply Units.ext
      have h1 := hr (r.symm ⟨δ, hδ⟩)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
    refine ⟨γ, hγ, c, (h c)⁻¹ * γ⁻¹ * g * κ⁻¹, ?_, κ, hκU, by group⟩
    rw [← finHomN_eq_one V hn]
    have e1 : finHomN V hn g = finHomN V hn p.2.1 := by
      rw [hpq, map_mul, (finHomN_eq_one V hn _).2 p.1.2, one_mul]
    have e2 : finHomN V hn p.2.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * (y c).1 * κ0.1 :=
      Units.ext (by rw [finHomN_val, hdec])
    have e3 : finHomN V hn (h c) = (y c).1 := Units.ext (by rw [finHomN_val, (hh c).2])
    have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, hκf])
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, e1, e2, e3, e4, hΦγ]
    group
  · intro c c' γ hγ k hk κ hκ heq
    obtain ⟨_, κ0, hκ0⟩ := (hU κ).1 hκ
    have hΦγ : finHomN V hn γ = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 :=
      Units.ext (by rw [finHomN_val, hr ⟨γ, hγ⟩])
    have e3 : ∀ c, finHomN V hn (h c) = (y c).1 := fun c => Units.ext (by rw [finHomN_val, (hh c).2])
    have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, ← hκ0])
    have key : (y c').1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 * (y c).1 * κ0.1 := by
      rw [← e3, ← e3, heq, ← e4, ← hΦγ]
      simp only [map_mul, (finHomN_eq_one V hn k).2 hk, mul_one]
    have hmemγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 ∈
        UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      rw [← hΦγ]; exact GlobalTheory.AdForm.Model.finGL_mem V hn γ
    apply hy.1
    show (Quotient.mk'' (y c) : Cls S) = Quotient.mk'' (y c')
    refine (DoubleCoset.eq _ _ _ _).2 ⟨⟨_, hmemγ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ (r ⟨γ, hγ⟩).2),
      ⟨κ0.1, ((S.U_eq κ0.1).1 κ0.2).1⟩, Subgroup.mem_subgroupOf.2 κ0.2, Subtype.ext key⟩

end Gen

section Gen2
variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (y : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  (U : Subgroup (GA D V)) (hU : ∀ g, g ∈ U ↔ g ∈ GfC V ∧ ∃ κ : S.U, κ.1.1 = finM V hn g)
  (h : cl → GA D V) (hh : ∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (y c).1.1)

include hU hh in
set_option maxHeartbeats 1000000 in

theorem stabOrd_of_chart {stab : cl → Type} [∀ c, Group (stab c)]
    (stabI : ∀ c, stab c →* UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)))
    (hinj : ∀ c, Function.Injective (stabI c))
    (hran : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))),
      γ ∈ (stabI c).range ↔ bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        S.U.map (MulAut.conj (y c).1).toMonoidHom)
    (c : cl) : stabOrd U (h c) = Nat.card (stab c) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V n hn
  obtain ⟨r, hr⟩ := GlobalTheory.RatPtsEquiv.rat_equiv D V n hn
  have hΦγ : ∀ γ : GQ V, finHomN V hn γ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r γ).1 :=
    fun γ => Units.ext (hr γ)
  have e3 : finHomN V hn (h c) = (y c).1 := Units.ext (by rw [finHomN_val, (hh c).2])
  have hcond : ∀ γ : GQ V, (∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h c = h c * k * κ) ↔ r γ ∈ (stabI c).range := by
    intro γ
    rw [hran]
    constructor
    · rintro ⟨k, hk, κ, hκ, heq⟩
      obtain ⟨_, κ0, hκ0⟩ := (hU κ).1 hκ
      have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, ← hκ0])
      have key := congrArg (finHomN V hn) heq
      rw [map_mul, map_mul, map_mul, hΦγ, e3, e4, (finHomN_eq_one V hn k).2 hk, mul_one] at key
      refine Subgroup.mem_map.2 ⟨κ0.1, κ0.2, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← key]
      group
    · intro hmem
      obtain ⟨κ1, hκ1, hconj⟩ := Subgroup.mem_map.1 hmem
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hconj
      obtain ⟨κ, hκU, hκf⟩ : ∃ κ ∈ U, finM V hn κ = κ1.1 :=
        ⟨_, (lift_mem V hn S U hU e.toMulEquiv he ⟨κ1, hκ1⟩).1, (lift_mem V hn S U hU e.toMulEquiv he ⟨κ1, hκ1⟩).2⟩
      have e4 : finHomN V hn κ = κ1 := Units.ext (by rw [finHomN_val, hκf])
      refine ⟨(h c)⁻¹ * γ.1 * h c * κ⁻¹, ?_, κ, hκU, by group⟩
      rw [← finHomN_eq_one V hn, map_mul, map_mul, map_mul, map_inv, map_inv, hΦγ, e3, e4, ← hconj]
      group
  unfold stabOrd
  rw [Nat.card_congr (r.toEquiv.subtypeEquiv hcond)]
  exact (Nat.card_congr (MonoidHom.ofInjective (hinj c)).toEquiv).symm

end Gen2

set_option maxHeartbeats 1000000 in

theorem twDat_reps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, IsReps ((I.rec7 l Z).sp.X i) (A.U i β) (A.h i β) ∧ (Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ)) ∧ ∀ c, stabOrd (A.U i β) (A.h i β c) = Nat.card ((I.chain l u a).stab i c.1) := by
  intro B X I hOk hP l Z u a Ch A hA i hi β
  exact ⟨reps_of_chart _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (A.U i β) (hA.U i hi β) (A.h i β)
      (hA.h i hi β) (A.K i hi β).y_bij,
    GlobalTheory.T.continuous_chartLevelCharacters_adelic_tuple I hOk hP l Z u a Ch A hA i hi β,
    fun c => stabOrd_of_chart _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (A.U i β) (hA.U i hi β) (A.h i β)
      (hA.h i hi β) (A.K i hi β).stabI (A.K i hi β).stabI_inj (A.K i hi β).stabI_range c⟩

end GlobalTheory.ChartReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartScalarFormAdelicPointEqClassTransportStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartScalarForm_adelicPoint_eq_classTransport : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b (c : (I.chain l u a).cls j) (d : (I.stp u a j).D c.1)
    (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (z : TC.GA B (B.R.N j)), x ∈ GfC _ →
    z.1 = finM _ (rankN (I.rec7 l Z) j hj) x → TC.PtOf (z * A.kb j b) (extTo I.SQ d.1.1) →
    A.chOf j ((I.stp u a j).cl c.1 d) = b →
    cosetIn d = cosetIn ((I.stp u a j).rep ((I.stp u a j).cl c.1 d)) → ∀ y,
      A.rd θ j hj b φ y x = (I.stp u a j).trTo B.fields.emb B.embLL c.1 d (φ ((I.stp u a j).cl c.1 d)) y := by
  first | exact @GlobalTheory.AdForm.rd_trTo | exact GlobalTheory.AdForm.rd_trTo | (intros; apply GlobalTheory.AdForm.rd_trTo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DisjointReferenceTwistPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Core.Rk
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.RowRead

theorem map_mem_span_range {K L M N J : Type*} [Semiring K] [Semiring L] [AddCommMonoid M] [AddCommMonoid N] [Module K M]
    [Module L N] {σ : K →+* L} (f : M →ₛₗ[σ] N) {φ : J → M} (h : Submodule.span K (Set.range φ) = ⊤) (z : M) :
    f z ∈ Submodule.span L (Set.range fun a => f (φ a)) := by
  have hz : z ∈ Submodule.span K (Set.range φ) := h ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact Submodule.subset_span ⟨a, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

section G
open GlobalTheory.PeriodOnStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

def valMt (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) :
    (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun F p := F.1 () p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def valMtP : MtP W Ch sel mu P σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun G p := G.1 (toRow sel mu p.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem valMtP_injective : Function.Injective (valMtP W Ch sel mu P σ) := by
  intro G G' h
  refine Subtype.ext (funext fun d => ?_)
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  exact congrFun h (trivPt X _ _ _ _ p)

theorem rowEmb_linearIndependent (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) {J : Type} {φ : J → MtildeV W Ch sel mu P}
    (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun a => rowEmb W Ch sel mu P b0 til ext tz H hd σ (φ a) :=
  LinearIndependent.of_comp (valMt W Ch sel mu P b0 til ext tz σ H)
    ((toMtilde_linearIndependent W Ch sel mu P σ h).map' (valMtP W Ch sel mu P σ)
      (LinearMap.ker_eq_bot.2 (valMtP_injective W Ch sel mu P σ)))

theorem rowEmb_span (hX : X.Ok) {J : Type} {φ : J → MtildeV W Ch sel mu P} (h : Submodule.span X.K (Set.range φ) = ⊤) :
    Submodule.span ℂ (Set.range fun a => rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ (φ a)) = ⊤ :=
  GlobalTheory.PerQ.RowIntModel.eq_top_of_rowEmb_mem W Ch sel mu P b0 til ext tz hd σ hX _ fun z _ =>
    map_mem_span_range (rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ) h z

end G

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem disjoint_reference_twist_primes (h : I.Ok) :
    Disjoint (B.primes X).vGs (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) :=
  Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I I.mu0) (GlobalTheory.Mem.LevTwist.levOk_twists B X I h).2.1

def rowRead (h : I.Ok) (l : I.Laws) (u : B.Word) : (MtTrue I).V →ₛₗ[B.embLL] (I.per l u I.mu0).Mt :=
  GlobalTheory.PeriodOnStep.rowEmb (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps (I := I.chIn u I.mu0) (I.perIn u I.mu0).b0
    (I.perIn u I.mu0).til (I.perIn u I.mu0).ext (I.perIn u I.mu0).tz (I.perIn u I.mu0).H (disjoint_reference_twist_primes I h) B.embLL

end GlobalTheory.Core.Rk.RowRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMethodOfEisensteinFacts
section
namespace GlobalTheory

theorem doublingMethod_of_three : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.SiegelEisensteinContinuation →
    GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.DoublingMethod :=
  fun hC hE hP => GlobalTheory.T.siegel_eisenstein_continuation_and_poles hC (fun D V h0 a ha hI μ b hμ hb s₁ φ hφ =>
    ⟨hE D V h0 a ha hI μ b hμ hb s₁ φ hφ, fun hab => hP D V h0 a ha hI μ b hμ hb s₁ φ hφ hab⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConstMovedVacuumAllTuplesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_movedVacuum_all_tuples : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → VacT I l Z θ i hi c₀ μ om vac := by
  first | exact @GlobalTheory.AdForm.VacAll.vacT_all | exact GlobalTheory.AdForm.VacAll.vacT_all | (intros; apply GlobalTheory.AdForm.VacAll.vacT_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlaceStabilizerPartialProductsFiniteSetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_placeStabilizer_partialProducts_finiteSet : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (κ : GA D S), IsSelfDualC S L → InK S L P κ → ∀ Fs : Finset (Pl D), ∃ l : List (GA D S), (∀ y ∈ l, ∃ v, P v ∧ InK S L (· = v) y) ∧ (∀ i j, infPart D (Formalism.L2.Theta.mt S l.prod i j) = infPart D (Formalism.L2.Theta.mt S κ i j)) ∧ (∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S l.prod i j) = GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j)) ∧ ∀ w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S l.prod i j) = GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
  first | exact @GlobalTheory.PlaceProducts.finite_place_products | exact GlobalTheory.PlaceProducts.finite_place_products | (intros; apply GlobalTheory.PlaceProducts.finite_place_products <;> assumption)
end

