import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0301
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0329
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0328
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0288
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0284
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0139
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0300
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0302
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0291
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.PureDegreeZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0310
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0307
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0222
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseFrameBadPrimeEqCompanionLattice
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameLat

theorem locP_map_equiv' {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (e : W ≃ₗ[R] W') (q : Ideal R) [q.IsPrime] (Λ : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ q (Λ.map (e : W →ₗ[R] W')) = (Formalism.HermitianLatticesTheory.localization₂ q Λ).map (e : W →ₗ[R] W') := by
  ext x
  constructor
  · rintro ⟨s, hs, z, hz, hzx⟩
    refine ⟨e.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have : s • e.symm x = z := by
      apply e.injective
      rw [map_smul, e.apply_symm_apply]
      exact hzx.symm
    rw [this]
    exact hz
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, by simp⟩

theorem locP_mvL_comm {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ : Submodule (𝓞 E) (Fin N → E)) : Formalism.HermitianLatticesTheory.localization₂ q (mvL c Λ) = mvL c (Formalism.HermitianLatticesTheory.localization₂ q Λ) :=
  locP_map_equiv' ((toLE c).restrictScalars (𝓞 E)) q Λ

theorem mvL_one' {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) : mvL 1 Λ = Λ := by
  unfold mvL
  convert Submodule.map_id _
  refine LinearMap.ext fun z => ?_
  show toLE 1 z = z
  rw [toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem span_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (h : Submodule.span E (Λ : Set (Fin N → E)) = ⊤) : Submodule.span E ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = ⊤ := by
  have e : ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = (toLE c : (Fin N → E) →ₗ[E] (Fin N → E)) '' (Λ : Set (Fin N → E)) := by
    unfold mvL
    rw [Submodule.map_coe]
    rfl
  rw [e, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  exact (toLE c).surjective

end GlobalTheory.BaseFrameLat

open GlobalTheory.BaseFrameLat in

theorem GlobalTheory.TwV.baseFrame_std_eq_compan : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p, IsPtAd A a i hi β x p → ∀ P : SB t μ, mvL (A.fb i hi β P) (stdAt D.host.E (D.R.N i) (seamP t.seam P.1)) = Formalism.HermitianLatticesTheory.localization₂ (seamP t.seam P.1).asIdeal (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpins htie i hi β x p hp P
  have hd : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  have hR := GlobalTheory.T.transportedFrame_standardLocal_eq_localization t.seam P.1 (frsF t.sel (t.tup μ) p P) p.deco.1.N (GlobalTheory.TopStep.frsF_mem p P)
  rw [hp.lat] at hR
  have hJ : IsUnit (gramN D i hi).det := by
    rw [← hpins.crd_orth i hi, Matrix.det_mul]
    have hc : IsUnit ((A.crd i hi).1).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.crd i hi).isUnit
    refine IsUnit.mul ?_ hc
    show IsUnit ((((A.crd i hi).1).map (sigD D : D.host.E →+* D.host.E))ᵀ).det
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hc.map _
  have hfg : (((St i hi).K β).lev.Lb).FG := Module.Finite.iff_fg.mp ((St i hi).K β).lev.Lb_fin
  have hsp := ((St i hi).K β).lev.Lb_span
  have h4 := GlobalTheory.T.companionLattice_adelicLattice_localization_eq D.sp (sigD D) rfl (gramN D i hi) hJ a x.1 x.2 _ hfg hsp (seamP t.seam P.1)
  have hCfg := GlobalTheory.T.companionHermitianLattice_fg D.sp (gramN D i hi) hJ a _ hfg hsp
  set C := compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb with hC
  have hCs : Submodule.span D.host.E (C : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
    refine eq_top_iff.2 (hsp ▸ Submodule.span_mono ?_)
    intro z hz
    exact (le_sup_left : ((St i hi).K β).lev.Lb ≤ C) hz
  unfold latCo at hR
  rw [locP_mvL_comm, h4, ← locP_mvL_comm] at hR
  have e1 : mvL (A.crd i hi) (latAd x.1 C) = latAd (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (mvL (A.fb i hi β P)⁻¹ C) := by
    rw [GlobalTheory.T.adelicPointLattice_mul_rationalGL, ← mvL_mul, mul_inv_cancel, mvL_one']
    exact (latAd_rat _ _ _).symm
  rw [e1] at hR
  have h3 := GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime (seamP t.seam P.1) _ hd _ _ (mvL (A.fb i hi β P)⁻¹ C) (hCfg.map _) (span_mvL _ _ hCs) (hp.frame P) hR.symm
  rw [← h3, ← locP_mvL_comm, ← mvL_mul, mul_inv_cancel, mvL_one']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartDatumLevelPrimeInvariantMulLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.PhiTLev

set_option maxHeartbeats 2000000 in

theorem deco_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj) (κ : ((St j hj).K β).lev.U) p p₁,
      x₁.1 = x.1 * κ.1 → IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
      p₁.deco.1.N = p.deco.1.N ∧ ∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ κ p p₁ hx hp hp₁
  have hL : latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb =
      latCo D.sp (gramN D j hj) (A.crd j hj) a x.1 ((St j hj).K β).lev.Lb := by
    unfold latCo
    rw [hx, Formalism.MainNotions.G.KAat.latAd_stab _ _ _ (hatStab_of_lev _ κ)]
  have hN : p₁.deco.1.N = p.deco.1.N := by
    have h := congrArg (latBack t.seam) ((hp₁.lat.trans hL).trans hp.lat.symm)
    rwa [latBack_seam_lat, latBack_seam_lat] at h
  refine ⟨hN, fun P => ?_⟩
  obtain ⟨v, hov, hTv, -⟩ := FnlAwayCpl.exists_place hTie P
  have hat : p₁.deco.1.at P.1 = p.deco.1.at P.1 := by
    show Formalism.HermitianLatticesTheory.localization₂ _ p₁.deco.1.N = Formalism.HermitianLatticesTheory.localization₂ _ p.deco.1.N
    rw [hN]
  refine FnlAwayCpl.f_eq_on_at p.deco.2 p₁.deco.2 P hat fun w hw hw₁ => ?_
  have H := GlobalTheory.CplPt.funMoved_mul_lev t.seam _ P v (hTv j hj) _ _ _ κ (hp.fnl P v (hTv j hj) hov)
  have e : ratA D.host.F (A.crd j hj) * x₁.1 = ratA D.host.F (A.crd j hj) * x.1 * κ.1 := by
    rw [hx, mul_assoc]
  rw [← e] at H
  have hu₁ : (fun l => t.seam.iE (w l)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb := by
    rw [← hp₁.lat]
    exact Submodule.subset_span ⟨w, hw₁, rfl⟩
  obtain ⟨z, hz⟩ := FnlAwayCpl.exists_latS_pullV D.sp (gramN D j hj) (A.crd j hj) a x₁.1 x₁.2
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) ((St j hj).K β).lev.Lb ((St j hj).K β).lev.Lb_fin
    ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hu₁
  rw [hp₁.fnl P v (hTv j hj) hov w hw₁ z hz, H w hw z hz]

set_option maxHeartbeats 2000000 in

theorem phiT_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi)
    (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
      ∀ z, phiT t.X.K p₁.deco.1 p₁'.deco.1 z = phiT t.X.K p.deco.1 p'.deco.1 z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' z
  obtain ⟨hN, hf⟩ := deco_mul_lev A dtU a hPins hTie i (Nat.le_of_succ_le hi) β x x₁ κ p p₁ hx hp hp₁
  obtain ⟨hN', hf'⟩ := deco_mul_lev A dtU a hPins hTie (i + 1) hi β' x' x₁' κ' p' p₁' hx' hp' hp₁'
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
  refine forall_congr' fun P => ?_
  simp only [Deco.at, hN, hN']
  refine forall₂_congr fun y hy => and_congr_right fun hzy => ?_
  rw [hf P y hy, hf' P (z y) hzy]

end GlobalTheory.TwV.PhiTLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeAtBadPlacesStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N j)), w ∈ p.deco.1.at P.1 → w ∈ p₁.deco.1.at P.1 → p₁.deco.1.f P w = p.deco.1.f P w) := by
  first | exact @GlobalTheory.TwV.FnlAway.fnl_away | exact GlobalTheory.TwV.FnlAway.fnl_away | (intros; apply GlobalTheory.TwV.FnlAway.fnl_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllStepsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_badPlaces_allSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  first | exact @GlobalTheory.TwV.fnl_eq_of_away_cpl | exact GlobalTheory.TwV.fnl_eq_of_away_cpl | (intros; apply GlobalTheory.TwV.fnl_eq_of_away_cpl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeUnderLevelPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_under_levelPrime : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := by
  first | exact @GlobalTheory.FnlAway.fnl_eq | exact GlobalTheory.FnlAway.fnl_eq | (intros; apply GlobalTheory.FnlAway.fnl_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointMulLevelSameDecorationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoint_mul_level_same_decoration : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj) (κ : ((St j hj).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
      p₁.deco.1.N = p.deco.1.N ∧ ∀ P w, p₁.deco.1.f P w = p.deco.1.f P w) := by
  first | exact @GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco | exact GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco | (intros; apply GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnLastStepLocalFactorTwistPrimeLaw
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwTopQ

theorem topF_eq {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (i : ℕ) (P : rowSG Pr sel mu) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
  topF Ch sel mu cst i P p Y p' x = topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

theorem locq_twist : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP g z g' z' hcpl hfr htop hfr' Z
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hD := hok.depthQ P hP
  have hM := hc.M_pos
  have hX : t.X.Ok := hPin.fields.ok
  have hU := qUnif_of t.sel (t.tup μ) hX t.pr_ok hPin.sel
  have hgI : g ∈ GLint t.X.E _ P.1 :=
    hok.int (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β) P ((exists_midLev_iff _ _ _ _ _ _ _ _).1 ⟨z, hcpl.1⟩)
  have hg'I : g' ∈ GLint t.X.E _ P.1 := GlobalTheory.T.topRankLevel_mem_integralGL_at_twist_prime _ _ _ _ _ P hP g' z' htop
  have hdep : topDep t.sel (t.tup μ) (t.cst μ) P = 2 * (t.cst μ).M := if_neg hP
  obtain ⟨hk, hkc⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ κ.1 p p₁ hx hp hp₁ P (t.cst μ).D g
    (hc.D_pos P) le_rfl hgI hfr
  obtain ⟨hk', hkc'⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1 + 1) hi β' x' x₁' κ'.1 p' p₁' hx' hp' hp₁' P
    (topDep t.sel (t.tup μ) (t.cst μ)) g' (by rw [hdep]; omega) (by rw [hdep]; exact hD) hg'I hfr'
  rw [hdep] at hkc'
  have hy0 : y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P = A.y0 β P := by
    unfold y0At
    rw [dif_pos rfl]
  obtain ⟨hW0, hV1, hW⟩ := GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime A dtU a hPin hTie (Nat.le_of_succ_le hi) β P hP p p₁ g
    ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)) hgI (by rw [hy0]; exact hcpl.2) hk hkc
    (fun w => by simp)
  rw [topF_eq, topF_eq]
  have e1 : inFr (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p₁' P) Z =
      ((frsF t.sel (t.tup μ) p₁' P).trans ((frsF t.sel (t.tup μ) p' P).symm.trans g'.symm)).symm.toLinearMap ∘ₗ
        (g'.symm.toLinearMap ∘ₗ inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) Z ∘ₗ g.toLinearMap) ∘ₗ
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).toLinearMap := by
    refine LinearMap.ext fun w => ?_
    simp [inFr, LinearEquiv.trans_symm]
  have e2 : (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)) =
      ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).symm
        (g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)))) := by
    simp [LinearEquiv.trans_symm]
  have hy'' : ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).M) *
      g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) l) := by
    have h1 := (hk _).2 hV1
    rw [map_smul] at h1
    have e3 : ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm))
        ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) =
        g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) := by
      simp
    rw [e3] at h1
    intro l
    simpa using (ciMem_stdAt _ _).1 h1 l
  rw [e1, e2, GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime t.Ch t.sel (t.tup μ) (t.cst μ) (m_eq t μ) hc P hP hD _ _ hk hkc hk' hkc' _ _ hy'']
  exact GlobalTheory.T.topLevelDatum_transform_at_twist_prime_under_levels t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) hok hU (A.ib (t.m2 + 1) (cpl_lt t μ) β) P hP g z hcpl.1 g' z' htop _ _ _ hW hW0

end GlobalTheory.TwTopQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConcreteChainAgreesAtTupleOfNormalisedRows
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Svd.tiesAt_of_rowPin : ∀ (K : Ctx) (β : BPt K), β.Is (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) → ∀ μ, GlobalTheory.AtG.TiesAt β.D β.O.ex.errX β.O.X μ := by
  intro K β hβ μ
  have key := positionOf_ind (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ∀ N h μ,
      GlobalTheory.AtG.TiesAt (setDiv X.toD7 N h) (O.tr N h).ex.errX (O.tr N h).X μ) ?_ hβ
  · exact key (β.Y.obj β.p) ((show ofObj (β.Y.obj β.p) = layObj β.Y from rfl).trans β.hY) (nPrime β.p.L) β.p.ht μ
  · intro K B f T w Z c hc O hO N h μ
    obtain ⟨⟨P⟩, hrow⟩ := hc
    have hpart : Part w Z (ofObj O) := hO ▸ P
    obtain ⟨_, hpiG, hpiT, hqp, _⟩ := Part.kerTie B f T w Z O hpart
    exact GlobalTheory.T.periodRelations_trueColumns_at_tuple w.I w.ok w.l (GlobalTheory.Mem.Db.setDivZ Z N h) w.l0 P.pin.jets _ _ μ hpiG hpiT hqp
      (GlobalTheory.AtG.rowPin_setDivZ w.I w.ok w.l Z N h μ (hrow μ))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChain
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.RatPt

theorem isPtAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs ×
          GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp
  exact ⟨GlobalTheory.T.pointLattice_moved_rational_isometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp, GlobalTheory.T.chartPointFrames_move_rationalIsometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp,
    GlobalTheory.T.levelPrimeFunctionals_move_rationalIsometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp⟩

theorem xiPt_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG t.X.E (D.R.N (i + 1)) t.Pr.vGs × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi
  rcases lt_trichotomy i t.m2 with h | h | h
  · exact GlobalTheory.T.matrixStepDatum_equivariant_rational_unitary A dtU a hP hTie i hi h
  · exact GlobalTheory.T.firstCoupledStepDatum_rationalUnitary_equivariant A dtU a hP hTie i hi h
  · exact GlobalTheory.T.lastStepDatum_equivariant_rationalUnitary A dtU a hP hTie i hi h

theorem ratLaw_of_tie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    PtEx A a → (∀ i hi, PtAway A a i hi) → RatLaw A a) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hAw
  intro i hi β β' x x' x₁ x₁' γ hγ γ' hγ' h₁ h₁' z
  obtain ⟨g, hg⟩ := GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry A dtU a hP hTie i (Nat.le_of_succ_le hi) γ hγ
  obtain ⟨g', hg'⟩ := GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry A dtU a hP hTie (i + 1) hi γ' hγ'
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  have hq := isPtAd_rat A dtU a hP hTie i (Nat.le_of_succ_le hi) β x x₁ γ hγ h₁ g hg p hp
  have hq' := isPtAd_rat A dtU a hP hTie (i + 1) hi β' x' x₁' γ' hγ' h₁' g' hg' p' hp'
  have hE1 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x₁' p' := ⟨⟨_, hq⟩, ⟨_, hq'⟩⟩
  have hE0 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨_, hp⟩, ⟨_, hp'⟩⟩
  have a1 := hAw i hi β β' x₁ x₁' x₁ x₁' _ _ _ _ hq hq' hE1.1.choose_spec hE1.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  have a0 := hAw i hi β β' x x' x x' _ _ _ _ hp hp' hE0.1.choose_spec hE0.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  unfold xiAd
  rw [dif_pos hE1, dif_pos hE0, a1, a0, GlobalTheory.T.orthonormalChange_intertwines_rationalIsometries A dtU a hP hTie i hi γ γ' g g' hg hg' z]
  rw [xiPt_smul A dtU a hP hTie i hi β β' x x' p p' hp hp' g g']

end GlobalTheory.RatPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormAtEachLocationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_at_each_location : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ i, MtForm D P.M i := by
  first | exact @GlobalTheory.FormAllLevels.main | exact GlobalTheory.FormAllLevels.main | (intros; apply GlobalTheory.FormAllLevels.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceHeckeEigenMatchStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_hecke_eigen_match : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  first | exact @GlobalTheory.SummandEig.main | exact GlobalTheory.SummandEig.main | (intros; apply GlobalTheory.SummandEig.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.Holds7SizeAway
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory.GalCut7

noncomputable section

namespace GlobalTheory.GalCut7.SizeAway

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

open GlobalTheory.ResW in

theorem isUnitarisable (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (ha : 1 ≤ a)
    (π : CuspSub E a) (wt : ℤ) (hw : IsWeight π wt) (w : HeightOneSpectrum (𝓞 E)) (σ) (hσ : π.IsLocComp w σ) :
    GlobalTheory.SmGL.IsUnitarisable ((algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ)).rep := by
  set t : ℝ := ((a : ℝ) - 1 - wt) / 2 with ht
  have hr := GlobalTheory.UnitLocWeight.rexp_eq ha hw
  have hu : (π.twist (nu E (-t))).IsUnitary := by
    have e := (letter_centralExponent E ⟨a, π⟩).2.2.1 ha (-t)
    refine ((rexp_eq_zero_iff_isUnitary E (tw ⟨a, π⟩ (-t)) ha).1.1 ?_)
    rw [e, hr]; ring
  have hU := isUnitarisable_of_isLocComp_cusp E a _ ha hu w _ (hσ.twist (nu E (-t)))
  have hloc : (nu E (-t)).loc w = GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ) :=
    GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (-t)) w
  set σ' := σ.twist (CuspSub.locDet a (nu E (-t)) w) (CuspSub.isOpen_ker_locDet (nu E (-t)) w) with hσ'
  have key : (algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ) = IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
    have e1 : (((1 - (a : ℝ)) / 2 : ℝ) : ℂ) + (((wt : ℝ) / 2 : ℝ) : ℂ) = ((-t : ℝ) : ℂ) := by
      rw [ht]; push_cast; ring
    unfold algNorm
    rw [IrrGL.nu_nu, e1]
    unfold IrrGL.nu
    rw [IrrGL.tw_of]
    refine IrrGL.of_eq_of.2 ⟨?_⟩
    have e2 : GlobalTheory.SmGL.twist σ.ρ (GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ))) =
        σ'.ρ := by
      ext g v
      change ((GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ)) g : ℂˣ) : ℂ) • σ.ρ g v =
        ((CuspSub.locDet a (nu E (-t)) w g : ℂˣ) : ℂ) • σ.ρ g v
      congr 2
      simp [CuspSub.locDet, hloc, GlobalTheory.SmGL.detChar]
    rw [e2]
    exact .refl _
  rw [key]
  exact GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred) hU

end GlobalTheory.GalCut7.SizeAway

end
end

