import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0521
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0516
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferred
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem PiLocalization₂.val_autCusp {D : D7} (c : Com D) (s : PiLocalization₂ D) (u : s.CC c) (x : SmT s.M) :
    IsAutFunSm c.θ s.V (PiLocalization₂.val u x) ∧ IsCuspFun s.V (PiLocalization₂.val u x) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D c.θ s.V _ s.M _ _ _).1 ((mem_multT _ _ _ _ _).1 u.2)
  have key : ∀ y : SmT s.M, PiLocalization₂.val u y =
      (PiTensorProduct.lift (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) y := by
    intro y; rw [LinearEquiv.apply_symm_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [key, map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    have e : PiLocalization₂.val u (x + y) = PiLocalization₂.val u x + PiLocalization₂.val u y := map_add _ _ _
    rw [e]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem rankY_succ {D : D7} (k : ℕ) : D.R.rankY (k + 1) = D.R.rankY k + D.R.t := by
  show D.R.r + (k + 1) * D.R.t = D.R.r + k * D.R.t + D.R.t
  ring

theorem upPar_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, LevFacts D → UpPar D := by
  intro hRD hHowe D _ hND c hc k hk s s' hs hs' p hp u B φ hu v _ hne
  have hlat' := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc (k + 1) hk s' hs').2
  have hlat := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc k hk.le s hs).2
  set y := PiLocalization₂.val u v with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hne; funext x; simp [Step.up, h]
  have hyB : IsParamFunV s.V c.S (fun g => conj (y g)) B := (hlat _ B).1 (hu.2 v hy0)
  have hconj : (fun x => conj (p.up φ y x)) =
      fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν := by
    funext x; simp only [Step.up]; rw [← integral_conj]; congr 1; funext g; simp [map_mul]
  have hne' : (fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν) ≠ 0 := by
    rw [← hconj]; intro h; apply hne; funext x; simpa using congrFun h x
  have hrank : s'.V.rank = s.V.rank + D.R.t := by rw [hs'.rank, hs.rank, rankY_succ]
  have hYA := PiLocalization₂.val_autCusp c s u v
  unfold ParFun
  rw [hlat', hconj]
  intro w0 hw0 w h
  have hw0' : w0 ∉ c.S := by simpa using hw0
  exact GlobalTheory.T.thetaIntegral_conjCuspForm_parameterTransfer hRD D (GlobalTheory.T.sphericalParameterTransfer_all_finitePlaces hHowe D) c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.weil D.R.t hrank s.ν s.fd
    hs.haar hs.fund w0 (fun w' hw' => GlobalTheory.T.thetaChain_step_chars_unramified_off_S D c hc k hk w0 hw0' w' hw') w h (p.pt φ)
    (GlobalTheory.T.fock_vectors_lattice_vacua_off_finite_set D hND c hc k hk s s' hs hs' p hp φ w0 hw0') y (B w) hYA.1 hYA.2 (hyB w0 hw0 w h) hne'

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductFormulaDefiniteOfRallisConverge
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IPFConv

theorem integrableOn_of_quot {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsMulLeftInvariant]
    {𝓕 : Set (GA D V)} (hFD : IsFundamentalDomain (GQ V) 𝓕 μ) {φ : GA D V → ℂ}
    (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ)
    (h : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ)) : IntegrableOn φ 𝓕 μ := by
  have h1 := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hFD).1 (memLp_one_iff_integrable.2 h)
  rw [hφ.lift_descend] at h1
  exact memLp_one_iff_integrable.1 h1

theorem thetaKO_left_snd {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χV χW ω)
    {φ : WO V W → ℂ} (hf : IsThetaFunO ψ V W φ) (h : GA D V) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ W) (fun g => thetaKO ω h g φ) := fun γ hγ g => by
  have e : ((h, γ * g) : GA D V × GA D W) = (1, γ) * (h, g) := by simp
  show thetaKO ω h (γ * g) φ = thetaKO ω h g φ
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ φ hf)

theorem innerProductFormulaC_of_convergent : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hConv hpar
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  intro ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v₁ v₂ Q₁ Q₂
  intro φ₁ φ₂ F₁ F₂ Z pt
  have hCore : GlobalTheory.Hk3.Core R F := hL.1
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω := hL.2.2.2.2.2.1
  obtain ⟨hwitt, hrank, cA, hSet, hA0⟩ := GlobalTheory.T.liftPair_positiveDefinite_wittIndexZero_cartan R F hCore hpar i σ
  have hFo₁ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁
  have hFo₂ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₂
  have hW := hCore.models.νW i
  haveI : (R.νW i).IsHaarMeasure := hW.1.1
  have hFDW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := hW.2
  haveI : ν.IsHaarMeasure := hν.1.1
  have hFDV : IsFundamentalDomain (GQ (Vc D i)) 𝓕 ν := hν.2
  have hF₁ : F₁ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₁ hU₁ v₁
  have hF₂ : F₂ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₂ hU₂ v₂
  have hL₁ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₁ := (Submodule.mem_inf.1 hF₁).2.2.1
  have hL₂ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₂ := (Submodule.mem_inf.1 hF₂).2.2.1
  have hKP : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1)
      true (fun _ => True) (fun _ => True) (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂)
      (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂) :=
    ⟨ω, φ₁, φ₂, hω, hFo₁, hFo₂, trivial, trivial, fun _ _ => rfl, fun _ _ => rfl, μ, 𝓧, hμ, fun _ => rfl⟩
  obtain ⟨hC₁, hC₂, hInt, hEq⟩ := hConv R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1) D.R.t
    cA true (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂) (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂)
    (R.νW i) ν F₁ F₂ hSet (Or.inl hwitt) hrank hKP inferInstance inferInstance hF₁ hF₂
  have hpetW : ∀ u₁ u₂ : GA D (Wc D i) → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₁ →
      GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₂ → GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) u₁ u₂ = petW R i u₁ u₂ :=
    fun u₁ u₂ h₁ h₂ => GlobalTheory.AutomorphicL2Unitary.pet_eq hFDW h₁ h₂
  have hlift₁ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₁) F₁ = upLift R i ω φ₁ F₁ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₁.1 h) hL₁
  have hlift₂ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₂) F₂ = upLift R i ω φ₂ F₂ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₂.1 h) hL₂
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv at hC₁ hC₂
  rw [hlift₁] at hC₁ hEq
  rw [hlift₂] at hC₂ hEq
  have hZeq : ∀ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
      conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) = Z g := fun g => by
    rw [hpetW (rTr (Wc D i) g F₁) F₂ (hL₁.mul_right g) hL₂]
  have hpc := GlobalTheory.T.petersson_principal_level_continuous_right_invariant hP R F hCore i σ
  have hZc : Continuous Z :=
    (GlobalTheory.T.continuous_weilCoefficient_fockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hμ Q₁ Q₂).mul
      (Complex.continuous_conj.comp (hpc.2 U₁ hU₁ U₂ hU₂ _ _).1)
  have hZi : Integrable Z (R.νW i) := hInt.congr (ae_of_all _ hZeq)
  have hZr : ∀ g, ∀ k ∈ levW R i, Z (g * k) = Z g := fun g k hk => by
    have hk1 := GlobalTheory.T.principalLevel_fixes_fockVectors_finiteDatum R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁ k hk
    have e : (((1 : GA D (Vc D i)), g * k) : GA D (Vc D i) × GA D (Wc D i)) = (1, g) * (1, k) := by simp
    show l2 μ 𝓧 (ω (1, g * k) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) (g * k) F₁) F₂) =
      l2 μ 𝓧 (ω (1, g) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) g F₁) F₂)
    rw [e, map_mul, Module.End.mul_apply, hk1, (hpc.2 U₁ hU₁ U₂ hU₂ _ _).2 g k hk]
  obtain ⟨hfin, hdis⟩ := GlobalTheory.T.integral_unitaryAdelic_eq_sum_finiteCosets_realIntegrals D R.θ hSet.2.2.2.1 (Wc D i) hSet.2.2.2.2.1 _ (R.νW i) hW.1 hpc.1 Fr hFr mR
    hmR Z hZc hZi hZr
  refine ⟨fun h => ?_, ?_, hfin, ?_⟩
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) (fun g => thetaKO ω h g φ₁ * starRingEnd ℂ (F₁ g)) :=
      fun γ hγ g => by
        have e1 : thetaKO ω h (γ * g) φ₁ = thetaKO ω h g φ₁ := thetaKO_left_snd hω hFo₁.1 h γ hγ g
        have e2 : F₁ (γ * g) = F₁ g := hL₁ γ hγ g
        show thetaKO ω h (γ * g) φ₁ * starRingEnd ℂ (F₁ (γ * g)) = _
        rw [e1, e2]
    exact integrableOn_of_quot hFDW hLp (hC₁.1 h)
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Vc D i))
        (fun h => upLift R i ω φ₁ F₁ h * starRingEnd ℂ (upLift R i ω φ₂ F₂ h)) := fun γ hγ g => by
      have e1 : upLift R i ω φ₁ F₁ (γ * g) = upLift R i ω φ₁ F₁ g := hC₁.2.1 γ hγ g
      have e2 : upLift R i ω φ₂ F₂ (γ * g) = upLift R i ω φ₂ F₂ g := hC₂.2.1 γ hγ g
      show upLift R i ω φ₁ F₁ (γ * g) * starRingEnd ℂ (upLift R i ω φ₂ F₂ (γ * g)) = _
      rw [e1, e2]
    exact integrableOn_of_quot hFDV hLp (hC₁.2.integrable_mul_conj hC₂.2)
  · have hvol : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Vc D i) ν = (ν 𝓕).toReal := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hFDV]
    have hpV : GlobalTheory.Cusp.petersson (Vc D i) ν (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) =
        l2 ν 𝓕 (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) := GlobalTheory.AutomorphicL2Unitary.pet_eq hFDV hC₁.2.1 hC₂.2.1
    have hI : ∫ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
        conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) ∂(R.νW i) = ∫ g, Z g ∂(R.νW i) :=
      integral_congr_ae (ae_of_all _ hZeq)
    rw [hpV, hvol, hI, hdis] at hEq
    exact hEq

end GlobalTheory.IPFConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RatioStep

variable {D : D7}

theorem mul_mem_intAE' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem mul_mem_intAt {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact mul_mem_intAE' ha.2 hb.2⟩

theorem diag_inv {ρ : ℕ} (t : GL (Fin ρ) (AE D)) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    t.1 = diagonal (fun k => t.1 k k) ∧ (t⁻¹).1 = diagonal (fun k => (t⁻¹).1 k k) ∧
      ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := by
  have h1 : t.1 = diagonal (fun k => t.1 k k) := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · rw [diagonal_apply_ne _ h, ht a b h]
  have hm : t.1 * (t⁻¹).1 = 1 := t.mul_inv
  have h3 : ∀ a b, t.1 a a * (t⁻¹).1 a b = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) a b := by
    intro a b
    have := congrFun (congrFun hm a) b
    rw [h1, diagonal_mul] at this
    exact this
  have h4 : ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := fun k => by
    have := h3 k k; rwa [one_apply_eq] at this
  refine ⟨h1, ?_, h4⟩
  ext a b
  by_cases h : a = b
  · subst h; simp
  · rw [diagonal_apply_ne _ h]
    have e := h3 a b
    rw [one_apply_ne h] at e
    calc (t⁻¹).1 a b = (t⁻¹).1 a a * (t.1 a a * (t⁻¹).1 a b) := by
          rw [← mul_assoc, mul_comm ((t⁻¹).1 a a), h4, one_mul]
      _ = 0 := by rw [e, mul_zero]

theorem conj_transv {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (t : GL (Fin ρ) (AE D))
    (ht : ∀ i j, i ≠ j → t.1 i j = 0) {i j : Fin ρ} (hij : i ≠ j) (c : AE D) :
    (d.levi t)⁻¹ * d.levi (GlobalTheory.GLGen.transvGL hij c) * d.levi t =
      d.levi (GlobalTheory.GLGen.transvGL hij ((t⁻¹).1 i i * c * t.1 j j)) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  obtain ⟨h1, h2, h3⟩ := diag_inv t ht
  ext : 1
  rw [Units.val_mul, Units.val_mul]
  show (t⁻¹).1 * Matrix.transvection i j c * t.1 = Matrix.transvection i j ((t⁻¹).1 i i * c * t.1 j j)
  conv_lhs => rw [h2, h1]
  exact GlobalTheory.GLGen.diag_transv_diag _ _ (fun k => by rw [mul_comm]; exact h3 k) hij c

theorem transv_mem_UX {ρ : ℕ} {i j : Fin ρ} (hij : i ≠ j) (hlt : i < j) (c : AE D) :
    GlobalTheory.GLGen.transvGL hij c ∈ UX D ρ := by
  rw [mem_UX]
  intro a b
  show (b < a → (Matrix.transvection i j c) a b = 0) ∧ (Matrix.transvection i j c) a a = 1
  refine ⟨fun hba => ?_, ?_⟩
  · simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    rw [one_apply_ne (ne_of_gt hba), zero_add, if_neg]
    rintro ⟨rfl, rfl⟩
    exact absurd (hba.trans hlt) (lt_irrefl _)
  · simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, one_apply_eq]
    rw [if_neg, add_zero]
    rintro ⟨rfl, e⟩
    exact hij e.symm

theorem upSum_transv {ρ : ℕ} {i j : Fin ρ} (hij : i ≠ j) (hj : j.1 = i.1 + 1) (c : AE D) :
    upSum (GlobalTheory.GLGen.transvGL hij c : GL (Fin ρ) (AE D)).1 = c := by
  have e : (GlobalTheory.GLGen.transvGL hij c : GL (Fin ρ) (AE D)).1 = Matrix.transvection i j c := rfl
  rw [e]
  unfold upSum
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [if_pos hj]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, one_apply_ne hij, and_self, if_true, zero_add]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h
    · have hbk : b ≠ k := fun e => by rw [e] at h; omega
      simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, one_apply_ne hbk, zero_add]
      rw [if_neg]
      rintro ⟨rfl, -⟩
      exact hb rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mat_mem_idAt {P : Pl D → Prop} {m n k l : ℕ} (A : Mx D m n) (M : Mx D n k) (B : Mx D k l)
    (hM : ∀ a b, M a b ∈ idAt D P) (i : Fin m) (j : Fin l) : (A ⬝ M ⬝ B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun b _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hM a b)

theorem levi_sub_one_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {t : GL (Fin ρ) (AE D)}
    (ht : d.levi t ∈ grpAt S P) (i j : Fin ρ) : t.1 i j - (1 : Mx D ρ ρ) i j ∈ idAt D P := by
  have hm : ∀ a b, (mt S (d.levi t) - 1) a b ∈ idAt D P := by
    intro a b
    have h := (MonoidHom.mem_ker).1 ht
    have h2 := congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idAt D P) => u.1 a b) h
    simp only [Units.val_one] at h2
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have e1 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idAt D P))).comp (matHom S) (d.levi t)).1 =
      (mt S (d.levi t)).map (Ideal.Quotient.mk (idAt D P)) := rfl
    rw [e1, Matrix.map_apply] at h2
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e : t.1 - 1 = d.pX ⬝ (mt S (d.levi t) - 1) ⬝ d.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, d.pX_jX, Matrix.mul_assoc, ← blockX, blockX_levi]
  rw [← Matrix.sub_apply, e]
  exact mat_mem_idAt _ _ _ hm i j

theorem opA_levi_one (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (om : Om V₀ W₀) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ)
    (Ξ : WO V₀ W₀ → ℂ) : opA ψ dW o ζ om (dW.levi u) 1 Ξ = Ξ := by
  unfold opA
  rw [show dW.levi u = dW.levi u * 1 from (mul_one _).symm, jacT_levi_mul ψ dW V₀ _ (yZero_mul V₀ _ hu),
    jacT_one]
  show (om (1, 1)) Ξ = Ξ
  rw [show ((1 : GA D V₀), (1 : GA D W₀)) = 1 from rfl, map_one]
  rfl

theorem psiFlag_transv (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {i j : Fin ρ}
    (hij : i ≠ j) (hj : j.1 = i.1 + 1) (c : AE D) :
    psiFlag ψ d (d.levi (GlobalTheory.GLGen.transvGL hij c)) = psiE ψ c := by
  rw [psiFlag, blockX_levi, upSum_transv hij hj c]

set_option maxHeartbeats 1000000 in

theorem psi_root {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {v : Pl D}
    (hG : GoodBF ψ B J LV LV₀ LW LW₀ v) (hU : UnrAt s v) {𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)}
    (hF : IsFlatBF s (· = v) 𝔉) {f : WO B.V J.W → ℂ} (hf : Vac ψ B.V J.W LV LW (· = v) f)
    (t : GL (Fin ρ) (AE D)) (ht : J.d.levi t ∈ grpAt J.W (· = v)) (hne : 𝔉 (s.om (1, J.d.levi t) f) ≠ 0)
    {i j : Fin ρ} (hij : i ≠ j) (hlt : i < j) (hj : j.1 = i.1 + 1) (c : AE D)
    (hK : InK J.W LW (· = v) ((J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t)) :
    psiE ψ c = 1 := by
  have hu : GlobalTheory.GLGen.transvGL hij c ∈ UX D ρ := transv_mem_UX hij hlt c
  have hnF : J.d.levi (GlobalTheory.GLGen.transvGL hij c) ∈ flagN J.d := J.d.levi_mem_NFlag hu
  have hnG : J.d.levi (GlobalTheory.GLGen.transvGL hij c) ∈ grpAt J.W (· = v) := by
    have e : J.d.levi (GlobalTheory.GLGen.transvGL hij c) = J.d.levi t *
        ((J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t) * (J.d.levi t)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem ht hK.1) (inv_mem ht)
  have hθ : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hf.1
  have h1K : InK B.V LV (· = v) 1 := ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩
  have hfix : s.om (1, (J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t) f = f :=
    GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hG.sdV hG.sdW (· = v)
      (by rintro w rfl; exact ⟨hG.tame, hU.1, hU.2⟩) f hf 1 _ h1K hK
  have hom : s.om (1, J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.emb0 1) (s.om (1, J.d.levi t) f) =
      s.om (1, J.d.levi t) f := by
    rw [map_one, mul_one]
    have e : (1, J.d.levi (GlobalTheory.GLGen.transvGL hij c)) * ((1 : GA D B.V), J.d.levi t) =
        ((1 : GA D B.V), J.d.levi t) *
          (1, (J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t) := by
      simp only [Prod.mk_mul_mk, one_mul]
      congr 1
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hfix]
  have heq := hF.equiv _ hθ _ hnF hnG 1 (one_mem _)
  have hψ := psiFlag_transv ψ J.d hij hj c
  rw [hom] at heq
  have hA : opA ψ J.d B.o B.ζ s.om₀ (J.d.levi (GlobalTheory.GLGen.transvGL hij c)) 1 (𝔉 (s.om (1, J.d.levi t) f)) =
      𝔉 (s.om (1, J.d.levi t) f) := opA_levi_one ψ J.d B.o B.ζ s.om₀ hu _
  rw [hA, hψ] at heq
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
  have h1 := congrFun heq w
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hw
  have h2 : star (psiE ψ c) = 1 := mul_right_cancel₀ hw (h1.symm.trans (one_mul _).symm)
  rw [← star_star (psiE ψ c), h2, star_one]

set_option maxHeartbeats 1000000 in

theorem ratio_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 hF f hf t htd ht hne i j hj
  have hij : i ≠ j := fun e => by rw [e] at hj; omega
  have hlt : i < j := by rw [Fin.lt_def]; omega
  obtain ⟨-, -, h3⟩ := diag_inv t htd
  have hti : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d ht i i
    rwa [one_apply_eq] at this
  have htj : (t⁻¹).1 j j - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d (P := (· = v)) (t := t⁻¹) (by rw [map_inv]; exact inv_mem ht) j j
    rwa [one_apply_eq] at this
  have hx1 : t.1 i i * (t⁻¹).1 j j - 1 ∈ idAt D (· = v) := by
    have e : t.1 i i * (t⁻¹).1 j j - 1 = (t.1 i i - 1) * (t⁻¹).1 j j + ((t⁻¹).1 j j - 1) := by ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hti) htj
  refine GlobalTheory.T.integral_of_keeps_selfDualLatticeLineColon D B.V B.V₀ ρ B.d LV LV₀ v hG.tame hG.sdV hG.monoV i j _ hx1 ?_
  intro r hr hR
  have hP := hG.prim i j hj
  refine (hP (r * (t.1 i i * (t⁻¹).1 j j)) (Ideal.mul_mem_right _ _ hr)).2 ?_
  intro o ho
  have hψr := (hP r hr).1 hR
  have hro : r * o ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hr
  have hRo : ∀ a : AE D, colMul B.d.jX j a ∈ latV B.V LV (· = v) → colMul B.d.jX i (r * o * a) ∈ latV B.V LV (· = v) :=
    (hP (r * o) hro).2 fun o' ho' => by rw [mul_assoc]; exact hψr _ (mul_mem_intAt ho ho')
  have hWV := GlobalTheory.T.latticeLineRatio_transport_of_columnsCarryLines D B.V B.V₀ J.W J.W₀ ρ B.d J.d LV LV₀ LW LW₀ v hG.tame hG.sdV hG.sdW hG.monoV hG.monoW hG.cols
    i j (r * o) hro hRo
  have hK := GlobalTheory.T.wittLeviTransvection_mem_compactAtPlace D J.W J.W₀ ρ J.d LW LW₀ v hG.sdW hG.monoW i j hij (r * o) hro hWV
  have hc : (t⁻¹).1 i i * (r * o * (t.1 i i * (t⁻¹).1 j j)) * t.1 j j = r * o := by
    linear_combination (r * o * (t.1 j j * (t⁻¹).1 j j)) * h3 i + (r * o) * h3 j
  have hK' : InK J.W LW (· = v) ((J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij (r * o * (t.1 i i * (t⁻¹).1 j j))) *
      J.d.levi t) := by
    rw [conj_transv J.d t htd hij, hc]
    exact hK
  have := psi_root s hG hU hF hf t ht hne hij hlt hj _ hK'
  rwa [mul_right_comm r o] at this

end GlobalTheory.FinPl.RatioStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCompactLevelProperty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FinPl.AwayLevel.single_natCast_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (T : ℕ) (j b : Fin n) [Decidable (b = j)] :
    (Pi.single j (T : K) : Fin n → K) b = ((if b = j then (T : 𝓞 K) else 0 : 𝓞 K) : K) := by
  by_cases hb : b = j
  · subst hb
    simp
  · simp [hb]

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.FinPl.AwayLevel.mem_levelVL_base : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => True) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v (F0 W u).cls0.lev.Lb := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a hat κ hκ y hy hmv v hv
  have hL := (hat.pinX.xs 0 (Nat.zero_le _)).2.2
  have hint := (GlobalTheory.SeeSaw.LevMem.moves_iff hL _ hy).1 hmv
  obtain ⟨k, hR⟩ := (hA.tr.std.some u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb : ∀ x, x ∈ (F0 W u).cls0.lev.Lb ↔ x ∈ TC.baseL B (B.R.N 0) (X.piT u) := hR.lb ()
  have hv' : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal := hv
  have h1 : ∀ x ∈ (F0 W u).cls0.lev.Lb, ∀ j, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = r := fun x hx j => by
    obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
    exact ⟨r, hr⟩
  have h2 : ∀ j, (Pi.single j ((B.T u : ℕ) : (I.rec7 l Z).host.E) : Fin ((I.rec7 l Z).R.N 0) → (I.rec7 l Z).host.E) ∈ (F0 W u).cls0.lev.Lb := fun j =>
    (hLb _).2 fun b => by
      have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
      refine ⟨if b = j then (B.T u : 𝓞 B.host.E) else 0, ?_, fun _ => ?_⟩
      · exact GlobalTheory.FinPl.AwayLevel.single_natCast_eq (K := B.host.E) (B.T u) j b
      · split_ifs
        · refine ⟨B.fields.conjO ((B.primes X).piT u), ?_⟩
          rw [hPr.piT_norm u]
        · exact dvd_zero _
  have hS := fun x => GlobalTheory.Mem.Col2.LevRead.mem_latS_iff hv' h1 h2 x
  have hmul : ∀ (N : GL (Fin ((I.rec7 l Z).R.N 0)) (Formalism.L2.DIV.AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), (∀ i j, N.1 i j ∈ Formalism.L2.DIV.RInt (I.rec7 l Z).host.F (I.rec7 l Z).host.E) →
      ∀ x : Fin ((I.rec7 l Z).R.N 0) → (I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F, (∀ b, x b ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v) →
        ∀ b, ((Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) N).1 *ᵥ x) b ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v := fun N hN x hx b => by
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (Formalism.UG.P.afsplit_prV_int v _ (hN b j)) (hx j)
  refine Subgroup.mem_inf.2 ⟨GlobalTheory.MemDual.bc_prV_mem_UPts _ _ v y.2, fun x => ?_⟩
  rw [hS, hS]
  refine ⟨hmul _ hint.1 x, fun h b => ?_⟩
  have := hmul _ hint.2 _ h b
  rwa [map_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
end

