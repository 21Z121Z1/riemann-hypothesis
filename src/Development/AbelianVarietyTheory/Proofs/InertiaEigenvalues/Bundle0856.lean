import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0680
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0841
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0854
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0853
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0805
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0506
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries MvPolynomial Matrix
open Formalism.IndefR.Links
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Scale

variable {D : D7} {n : ℕ}

theorem coefFn_translate (lam : D.what₂.Tau → DomWeight n) (u : GLR D n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n) (x : GLR D n) :
    coefFn (RingHom.id ℂ) lam (actP lam (invTrK u) F) x = coefFn (RingHom.id ℂ) lam F (u⁻¹ * x) := by
  have e1 : actP lam (invTrK u) F = detTwK lam (invTrK u) • trAct (invTrK u) F := rfl
  have e2 : (eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (x v.1).val v.2.1 v.2.2)).comp
        (trAct (invTrK u) : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n →+* Formalism.L2.DIV.Pol ℂ D.what₂.Tau n) =
      eval₂Hom (RingHom.id ℂ) (fun v => ((u⁻¹ * x) v.1).val v.2.1 v.2.2) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp [trAct, Formalism.GradedWeylDivisibility.blockAct]) fun v => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, eval₂Hom_C,
      eval₂Hom_X', Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => rfl
  have e3 : (RingHom.id ℂ) (detTwK lam (invTrK u)) =
      ((detFam (fun τ => (lam τ).detShift) u⁻¹ : ℂˣ) : ℂ) := by
    simp only [detTwK, detPow, detFam, map_prod, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      map_zpow₀, GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    change (((u τ)⁻¹).valᵀ).det = _
    rw [det_transpose]
    rfl
  rw [coefFn, coefFn, e1, smul_eq_C_mul, map_mul, eval₂Hom_C, e3, ← e2, map_mul, Units.val_mul]
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  ring

theorem coefFn_map {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) :
    coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  rw [coefFn, coefFn, eval₂Hom_map_hom, RingHom.id_comp]

def coefLin (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n)
  map_add' F F' := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add, Pi.add_apply, mul_add]
  map_smul' a F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, smul_eq_C_mul, map_mul, eval₂Hom_C, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem coefLin_injective (lam : D.what₂.Tau → DomWeight n) : Function.Injective (coefLin lam) :=
  (injective_iff_map_eq_zero _).2 fun F hF => Subtype.ext (GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily D n lam F (congrFun hF))

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {j : Fin D.R.m}
  {B : Base (Vc D j) (Wc D j)}

theorem io_act (hlev : R.toLevCh.Is A.μ0) (hth : R.IsThP) (hB : B.Good) (hψ : B.F.ψ = R.ψ) (hθ : B.F.θ = R.θ)
    (hsT : B.F.sT = cart (R.MW j (sg0 D A))) (hBS : ∀ τ, (B.F.BS τ).val = R.BV j τ) (hBT : B.F.BT = onb (R.MW j (sg0 D A)))
    (hmu : B.mu0 = R.mu0 ((j : ℕ) + 1)) (heta : B.eta = R.eta) (x : LowT (R.MW j (sg0 D A))) :
    ∀ u ∈ GinfC (Vc D j), ∀ w, R.ioP j x ((R.cV j).ρ u w) = B.act u (R.ioP j x w) := by
  have hinf : IsInfFam R.θ := hθ ▸ hB.frame.vac.2.inf
  have hf : IsThetaFunO R.ψ (Vc D j) (Wc D j) (R.vP j A.μ0) := by
    have := hth.pt_theta j A.μ0 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D j) τ) 1 (R.BV j τ) (Vc D j).rank := fun τ => hBS τ ▸ hB.frame.onbS τ
  have hinj : Function.Injective (R.ptP j A.μ0) :=
    GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW j (sg0 D A)) (R.BV j) (R.vP j A.μ0) (hth.ωP j A.μ0).std hinf
      (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hon τ)) hon hf
      (GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βV j))
        (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βW j)) hB.frame.rank_le (hth.vP j A.μ0))
      (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hth.vP j A.μ0) hf)
  have hexp : ∀ τ, HasInfExp D (R.toLevCh.mu A.μ0 ((j : ℕ) + 1)) τ
      ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) := fun τ => by
    obtain ⟨k, hk, ho⟩ := hlev.xi_fin A.μ0
    have h1 := hB.inf τ
    rw [hmu] at h1
    have h2 := GlobalTheory.Chain.StepVac.hasInfExp_mul h1 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hinf (hlev.xi A.μ0) hk ho τ)
    rwa [add_zero] at h2
  intro u hu w
  exact hinj (((hth.ioP j A.μ0).1 u hu x w).symm.trans
    (GlobalTheory.T.realisation_definite_realPoint_fockVector_action D G Pl0 T0 A Ks R j A.μ0 B hth hB hψ hθ hsT hBS hBT heta hexp u hu _))

theorem exists_scale (hlev : R.toLevCh.Is A.μ0) (hth : R.IsThP) (hc : (R.cV j).Is) (hB : B.Good) (hψ : B.F.ψ = R.ψ)
    (hθ : B.F.θ = R.θ) (hsT : B.F.sT = cart (R.MW j (sg0 D A))) (hBS : ∀ τ, (B.F.BS τ).val = R.BV j τ)
    (hBT : B.F.BT = onb (R.MW j (sg0 D A))) (hmu : B.mu0 = R.mu0 ((j : ℕ) + 1)) (heta : B.eta = R.eta)
    (hap : ∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ)
    (ham : ∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ)
    (c0 : VV D.what₂.LL (FWT.lamV D j) →ₛₗ[D.what₂.embLL] (R.cV j).W)
    (ht : Bridge.CoefMapTie (Vc D j) (R.cV j).coef c0 (rhoVr (labLL D) (FWT.lamV D j)))
    (x : LowT (R.MW j (sg0 D A))) (w₀ : (R.cV j).W) (hw : R.ioP j x w₀ = RealDat.Delta j) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ F : VV D.what₂.LL (FWT.lamV D j), harmFn (Wc D j).rank B.w B.F.BS (R.ioP j x (c0 F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
  have hinf : IsInfFam R.θ := hθ ▸ hB.frame.vac.2.inf
  have hT := io_act hlev hth hB hψ hθ hsT hBS hBT hmu heta x
  have hlam : B.w.lam = FWT.lamV D j := GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight D T0 R.toLevCh A.μ0 j B hlev hB hmu hap ham
  have hpq : ∀ τ, B.w.p τ + B.w.q τ ≤ (Wc D j).rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hΔ : B.w.delta (Wc D j).rank = RealDat.Delta j := by
    unfold Weight.delta RealDat.Delta
    rw [show B.w.p = _ from funext fun τ => congrArg Prod.fst (hB.sig τ),
      show B.w.q = _ from funext fun τ => congrArg Prod.snd (hB.sig τ), show B.w.ap = _ from funext hap,
      show B.w.am = _ from funext ham]
  have hirr : ∀ U : Submodule ℂ (R.cV j).W, (∀ h : GinfC (Vc D j), U.map ((R.cV j).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hc.2.2.2.2 U fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hc.1 k hk, mul_one]
      exact hU ⟨a, ha⟩
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
  have hharm : ∀ w, R.ioP j x w ∈ harm (Wc D j).rank B.w B.F.BS := by
    rcases hirr ((harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x)) (fun h => by
      rintro _ ⟨w, hw', rfl⟩
      rw [Submodule.mem_comap, hT h h.2]
      exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x) := by
        rw [Submodule.mem_comap, hw, ← hΔ]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x))
  obtain ⟨e, he0, he⟩ := GlobalTheory.CoefReal.exists_real_model (Vc D j) R.θ (R.cV j) (FWT.lamV D j) c0 hinf hc ht
  haveI := hc.2.2.2.1
  obtain ⟨c, hcc⟩ := GlobalTheory.T.schur_equivariant_maps_proportional (GinfC (Vc D j)) (R.cV j).W (GLR D (Vc D j).rank → ℂ) (fun h => (R.cV j).ρ h)
    (fun h => LinearMap.funLeft ℂ ℂ fun y => (realGL R.θ (Vc D j) h)⁻¹ * y)
    (harmFn (Wc D j).rank B.w B.F.BS ∘ₗ R.ioP j x) (coefLin (FWT.lamV D j) ∘ₗ e.symm.toLinearMap) hirr
    ((coefLin_injective _).comp e.symm.injective)
    (by
      rintro _ ⟨w, rfl⟩
      have h1 : harmFn (Wc D j).rank B.w B.F.BS (R.ioP j x w) ∈
          (harm (Wc D j).rank B.w B.F.BS).map (harmFn (Wc D j).rank B.w B.F.BS) := Submodule.mem_map_of_mem (hharm w)
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt hpq, hlam] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨F, rfl⟩
      exact ⟨e F, congrArg (coefLin _) (e.symm_apply_apply F)⟩)
    (fun h w => funext fun y => by
      change harmFn _ B.w B.F.BS (R.ioP j x ((R.cV j).ρ h w)) y = harmFn _ B.w B.F.BS (R.ioP j x w) _
      rw [hT h h.2, ← hθ]
      exact harmFn_fockGL _ _ _ _ _)
    (fun h w => funext fun y => by
      obtain ⟨v, rfl⟩ := e.surjective w
      change coefLin _ (e.symm ((R.cV j).ρ h (e v))) y = coefLin _ (e.symm (e v)) _
      rw [he h h.2, e.symm_apply_apply, e.symm_apply_apply]
      exact coefFn_translate _ _ _ _)
  refine ⟨c, fun h0 => hΔ0 ?_, fun F => ?_⟩
  · have h1 := LinearMap.congr_fun hcc w₀
    rw [h0, zero_smul, LinearMap.comp_apply, hw] at h1
    exact GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt hpq _ (hw ▸ hharm w₀) h1
  · refine (LinearMap.congr_fun hcc (c0 F)).trans ?_
    change c • coefLin _ (e.symm (c0 F)) = _
    rw [show e.symm (c0 F) = _ from e.symm_apply_eq.2 (he0 F).symm, ← coefFn_map]
    rfl

end Scale

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_isScale (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ)
    (hlev : Rl.toLevCh.Is A3.A.μ0) (hfam : Rl.toRealDat.fam_tie) (hcV : Rl.toRealDat.models_cV) (hth : Rl.toRealDat.IsThP)
    (hio : FWT.IoExt Rl.toRealDat) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) : ∃ c : ℂ, c ≠ 0 ∧ IsScale Rl v₀ (ρ.B i j b) c := by
  obtain ⟨gramR, c0R, c0L, hft⟩ := hfam
  obtain ⟨u, w₀, hu, -, hw⟩ := FWT.IsChosenExtremalVector.io _ hv hio
  obtain ⟨c, hc0, hc⟩ := Scale.exists_scale hlev hth (hcV j) (hρ.base i j b) (hpin.psi i j b) (hpin.inf i j b)
    (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b) (hpin.ap i j b) (hpin.am i j b)
    (c0L j) (hft.mapL j) _ w₀ hw
  exact ⟨c, hc0, gramR, c0R, c0L, hft, u, hu, hc⟩

theorem exists_isScale_of_char (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ)
    {F : Face3 D A3} (hC : Rl.Char3 F) (hio : FWT.IoExt Rl.toRealDat) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) : ∃ c : ℂ, c ≠ 0 ∧ IsScale Rl v₀ (ρ.B i j b) c :=
  exists_isScale Rl cG v₀ hρ hpin hC.lev hC.fam.tie hC.models.cV hC.thP hio i j b hv

end GlobalTheory.SeriesTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralQuotientComparisonFundamentalDomains
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellCompare

theorem isFundamentalDomain_of_map {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G)
    (H : Subgroup G) (Γ : Subgroup H) (𝓕 : Set G)
    (h : IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ) : IsFundamentalDomain Γ 𝓕 μ := by
  let E := Subgroup.equivMapOfInjective Γ H.subtype H.subtype_injective
  refine h.preimage_of_equiv (f := id) (e := E.symm) (Measure.QuasiMeasurePreserving.id μ)
    E.symm.bijective (fun g x => ?_)
  show (((E.symm g : Γ) : H) : G) * x = (g : G) * x
  congr 1
  have h1 : ((E (E.symm g) : Γ.map H.subtype) : G) = (g : G) := by rw [E.apply_symm_apply]
  rw [← h1, Subgroup.coe_equivMapOfInjective_apply]
  rfl

end GlobalTheory.CellCompare

theorem GlobalTheory.CellCompare.lintegral_comparison : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    (Γ Γ' : Subgroup H) [Countable Γ] [Countable Γ'] (D D' : Set H), IsFundamentalDomain Γ D ν →
    IsFundamentalDomain Γ' D' ν → ∀ (𝓕 𝓕' : Set G), IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ →
    IsFundamentalDomain (Γ'.map H.subtype) 𝓕' μ → ∀ f : G → ℝ≥0∞, Measurable f → (∀ h : H, ∀ g, f (h * g) = f g) →
    ν D' * ∫⁻ g in 𝓕, f g ∂μ = ν D * ∫⁻ g in 𝓕', f g ∂μ := by
  intro G _ _ _ _ μ _ _ H ν _ _ _ Γ Γ' _ _ D D' hD hD' 𝓕 𝓕' h𝓕 h𝓕' f hf hinv
  haveI : MeasurableSMul₂ H G := ⟨(measurable_subtype_coe.comp measurable_fst).mul measurable_snd⟩
  haveI : SMulInvariantMeasure H G μ := inferInstance
  haveI : MeasurableInv H := ⟨by
    have : Measurable fun x : H => (((x : G)⁻¹ : G)) := measurable_subtype_coe.inv
    exact Measurable.subtype_mk (f := fun x : H => ((x : G))⁻¹) (h := fun x => H.inv_mem x.2) this⟩
  haveI : MeasurableMul₂ H := ⟨by
    have : Measurable fun p : H × H => ((p.1 : G) * (p.2 : G)) :=
      (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
    exact Measurable.subtype_mk (f := fun p : H × H => ((p.1 : G) * (p.2 : G)))
      (h := fun p => H.mul_mem p.1.2 p.2.2) this⟩
  exact GlobalTheory.CovolIndep.lintegral_mul_eq ν μ Γ Γ' 𝓕 𝓕' D D'
    (GlobalTheory.CellCompare.isFundamentalDomain_of_map μ H Γ 𝓕 h𝓕)
    (GlobalTheory.CellCompare.isFundamentalDomain_of_map μ H Γ' 𝓕' h𝓕') hD hD' f hf (fun s x => hinv s x)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmitted
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremBAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  intro hBK hTD hEC D HW F Cm
  have hN1 := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨hP1, -, -, -, -, hP6, -, hP8, hP9, -⟩ := hN1
  have h54 := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨-, ⟨hWX, -⟩, hW1, -, -, hH, -, -⟩ := h54
  have hB := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  obtain ⟨hSat, -, hSatP, hPi0, hKL, hKill, -, hF1, -⟩ := hB
  obtain ⟨hRelay, hArcAdm⟩ := GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses hBK hTD hEC D HW F Cm
  have hA11 := GlobalTheory.T.ramifiedCoefficientChains_adm11 D
  have hArc := GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 D HW F Cm hArcAdm hP1 hA11
  have hJ := (GlobalTheory.jumps_exact_adm D HW F).2
  have hExt := GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F
  have hAdm9 := GlobalTheory.T.dcris_exact_strict_elementwise_crystalline D
  have hSplit := GlobalTheory.T.classSplitting_along_arcs_of_admissible D HW F Cm ⟨hP8, hP9, hW1, hJ, hExt, hF1, hRelay, hArc⟩ hArcAdm hP1 hP6 hWX
    (GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F) hJ hAdm9 hA11
  have hUniv := GlobalTheory.T.crystallineUniversalPart_caseA D HW F Cm ⟨hSat, hKL, hPi0, hArc⟩ hP9 hH (GlobalTheory.T.dDeRham_eq_dCris_of_unramified D)
  exact ⟨(GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1, GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm, hSat, hSatP, hKill,
    ArcLiftingSetup.content_divisibility_clause D, GlobalTheory.T.h1fGeneratorBoundAll_loc D, hRelay, hArc, hSplit, hUniv, hAdm9, GlobalTheory.T.blochKato_crystalline_extension_criterion D⟩

end GlobalTheory.TheoremBAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamifiedCoefficientChainsPrvTwentyFive
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem ramifiedCoefficientChains_prv_twenty_five :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
        RamifiedCoefficientChains.aux₃ D HW F 25 := by
  intro hBK hTD hEC D HW F Cm
  have hadm := GlobalTheory.T.localLifting_theoremC_hypotheses_admitted hBK hTD hEC D HW F Cm
  have h23 : LiftingTheory.adm23 D HW F := (GlobalTheory.jumps_exact_adm D HW F).2
  have hC4 : LetterConditionGlobal D HW F := GlobalTheory.T.letterConditionGlobal_of_N1used D HW F Cm (GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm)
  have hH : ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F := GlobalTheory.AdmHerrLocal.main D HW F
  have h22 : CrystallineLiftingBounds.adm22 D HW F := GlobalTheory.FontaineIneq.one_place_admissible_of_gap_constant_le D HW F
  have hL : InvariantsGenerators.LitFont D HW F := GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F
  exact GlobalTheory.T.ramified_coefficient_chains_of_hypotheses D HW F Cm 10 23 32 32 h23 hC4 hH h22 hL hadm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenThetaMatchStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_theta_match : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → BuiltEx A M C tp.tup → EvO A M C tp.tup (fun D' => (SumRepresentations.hypO D' → SumRepresentations.Conclusion41 D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D') → EvO A M C tp.tup (fun D' => Large D' ∧ Duties D') ∧ ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ Built A M C tp.tup big L ∧ Large (withLoc L) ∧ Duties (withLoc L) := by
  first | exact @GlobalTheory.CoefDuty.large_and_duties_of_large_rings | exact GlobalTheory.CoefDuty.large_and_duties_of_large_rings | (intros; apply GlobalTheory.CoefDuty.large_and_duties_of_large_rings <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtPowOdd
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ClassScalarIn

theorem unimod_hLat {D : D7} (V : HSp D) (hg : V.gram = 1) (g : Bridge.Gf V) :
    (⟨Bridge.hLat V g⟩ : GenLat D.host.E V.rank).Unimod := by
  intro v
  have h := (GlobalTheory.MovedLat.isSelfDualC_hLat V g).2 v
  rw [h]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  simp only [hg, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e : ∑ j, (IsCMField.complexConj D.host.E) (v j) * w j =
      IsCMField.complexConj D.host.E (∑ x, star (w x) * v x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, show star (w x) = IsCMField.complexConj D.host.E (w x) from rfl,
      IsCMField.complexConj_apply_apply, mul_comm]
  rw [e]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(Formalism.L2.Pj.hostOfRecord D).bar b, by rw [← hb]; exact (Formalism.L2.Pj.hostOfRecord D).bar_eq b⟩
  · rintro ⟨b, hb⟩
    refine ⟨(Formalism.L2.Pj.hostOfRecord D).bar b, ?_⟩
    rw [(Formalism.L2.Pj.hostOfRecord D).bar_eq]
    have hb' : ((b : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (∑ x, star (w x) * v x) := hb
    rw [hb', IsCMField.complexConj_apply_apply]

theorem sqrt_pow_odd (N k s : ℕ) : Real.sqrt (((N * k ^ 2 : ℕ) : ℝ) ^ (2 * s + 1)) =
    ((N ^ s * k ^ (2 * s + 1) : ℕ) : ℝ) * Real.sqrt N := by
  rw [show (((N * k ^ 2 : ℕ) : ℝ)) ^ (2 * s + 1) = (((N ^ s * k ^ (2 * s + 1) : ℕ) : ℝ)) ^ 2 * N by push_cast; ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

end GlobalTheory.ClassScalarIn

theorem _root_.GlobalTheory.SingleDatum.clsScal_mem : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → StdBase B → ∀ χ : Formalism.L2.Host.HChar D.host.E, ChrEq (B.mu * B.eta⁻¹) χ → ∀ (p bad : ℕ) (O : Subring ℂ), p.Prime → p ∣ bad → (∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q → (bad : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ k : ℕ, Nat.Coprime k p → (k : ℂ)⁻¹ ∈ O) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), (bad : 𝓞 D.host.E) ∉ P.asIdeal → GlobalTheory.IdemSupport.cP P ≠ P → ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ O ∧ (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) → ∀ (h : GA D V) (Λ : GenLat D.host.E V.rank) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) → clsScal (B.mu * 1 * B.eta⁻¹) y Λ W.rank ∈ O := by
  intro D V W B hB hstd χ hχ p bad O hp hpb hPl hO hval h Λ e' Ps y he hPs hsupp hy hΛ
  have hg : V.gram = 1 := hstd.1
  have hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := SetLike.coe_injective
    ((GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice V).trans (hstd.2.2.1.symm.trans hstd.2.2.2.2))
  obtain ⟨hu, hr⟩ := GlobalTheory.T.character_unramified_off_bad D V W B hB χ hχ bad hPl
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e' Ps y he hsupp hy bad hPs
    (B.mu * 1 * B.eta⁻¹) χ (by rwa [mul_one]) hu hr
  set L := Bridge.hLat V (finPt V h) with hLdef
  let H := Formalism.L2.Pj.hostOfRecord D
  have hbar : (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (H.bar_eq a)
  obtain ⟨m, m0, m1, m2, m3⟩ := GlobalTheory.T.exists_elem_stdLattice_sandwich_splitSupport D V hg hL h e' Ps bad he hPs hsupp
  have hS : GenLat.SplitSupp H (⟨L⟩ : GenLat D.host.E V.rank) :=
    ⟨m, m0, m1, m2, fun P hP hm => by rw [hbar]; exact (m3 P hP hm).1⟩
  have hU := GlobalTheory.ClassScalarIn.unimod_hLat V hg (finPt V h)
  obtain ⟨k, k0, hk⟩ := GlobalTheory.LawOfSquares.index_eq H L cc hU hS
    (by show cc ⊔ cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤; rw [hbar]; exact c1)
    (by show Submodule.span _ (detSet L) * idlE (cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) = idlE cc
        rw [hbar]; exact c3)
  have hΛL : Λ = GlobalTheory.ClassScalarCompare.conjLat L := by
    cases Λ with
    | mk La =>
      congr 1
      ext v
      exact (hΛ v).trans GlobalTheory.ClassScalarCompare.mem_conjLat.symm
  have hidx : ((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      Ideal.absNorm cc * k ^ 2 := by
    have := GlobalTheory.ClassScalarCompare.stdIndex_conjLat L
    rw [← hΛL] at this
    exact this.trans hk
  have hmp : ∃ a b : 𝓞 D.host.E, a * m + b * (p : 𝓞 D.host.E) = 1 := by
    have htop : Ideal.span {m, (p : 𝓞 D.host.E)} = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
      have hm : m ∈ P := hle (Ideal.subset_span (Set.mem_insert _ _))
      have hpP : (p : 𝓞 D.host.E) ∈ P := hle (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      refine (m3 P hP.isPrime hm).2 ?_
      obtain ⟨t, ht⟩ := hpb
      rw [ht, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hpP
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (htop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ Ideal.span {m, (p : 𝓞 D.host.E)})
    exact ⟨a, b, hab⟩
  have hcop : Nat.Coprime (Ideal.absNorm cc * k ^ 2) p := by
    obtain ⟨a, b, hab⟩ := hmp
    have h0 : Ideal.absNorm cc * k ^ 2 ≠ 0 :=
      mul_ne_zero (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0)) (pow_ne_zero _ k0)
    rw [← hk] at h0 ⊢
    haveI := Fact.mk hp
    haveI : Finite (L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) :=
      Nat.finite_of_card_ne_zero h0
    refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_).symm
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hd
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hpy : p • (QuotientAddGroup.mk y : L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0 := by
      rw [← hx]; exact addOrderOf_nsmul_eq_zero _
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hpy
    have h1 : ((p • y : L.toAddSubgroup) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := (AddSubgroup.mem_addSubgroupOf.1 hpy).2
    have h2 : (m • (y : Fin V.rank → D.host.E)) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank :=
      m1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self m) y.2)
    have h3 : (y : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
      have e : (y : Fin V.rank → D.host.E) = a • (m • (y : Fin V.rank → D.host.E)) + b • ((p • y : L.toAddSubgroup) : Fin V.rank → D.host.E) := by
        rw [AddSubgroupClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul, smul_smul, ← add_smul,
          hab, one_smul]
      rw [e]
      exact add_mem (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h1)
    have h4 : (QuotientAddGroup.mk y : L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_addSubgroupOf.2 ⟨y.2, h3⟩)
    rw [h4, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hNcop : Nat.Coprime (Ideal.absNorm cc) p := Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) hcop
  have hkcop : Nat.Coprime k p :=
    (Nat.coprime_pow_left_iff two_pos _ _).1 (Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hcop)
  have hv := GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring D.host.E χ O cc c0 fun P hP => by
    have hb : ((bad : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun hb =>
      P.isPrime.ne_top (eq_top_iff.2 (c2 ▸ sup_le hP ((Ideal.span_singleton_le_iff_mem _).2 hb)))
    have hc : GlobalTheory.IdemSupport.cP P ≠ P := fun hc => by
      refine P.isPrime.ne_top (eq_top_iff.2 (c1 ▸ sup_le hP ?_))
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : x ∈ P.asIdeal := hP hx
      rw [← hc] at h1
      exact Ideal.mem_comap.2 ((GlobalTheory.IdemSupport.mem_cP P x).1 h1)
    exact (hval P hb hc).2
  obtain ⟨s, hs⟩ := hB.odd
  have hq : ((((Ideal.absNorm cc) ^ s * k ^ (2 * s + 1) : ℕ) : ℂ))⁻¹ ∈ O :=
    hO _ (Nat.Coprime.mul (hNcop.pow_left _) (hkcop.pow_left _))
  unfold clsScal
  rw [hidx, hs, GlobalTheory.ClassScalarIn.sqrt_pow_odd, c4]
  convert O.mul_mem hv hq using 1
  push_cast
  rw [mul_inv, mul_inv]
  ring
end

