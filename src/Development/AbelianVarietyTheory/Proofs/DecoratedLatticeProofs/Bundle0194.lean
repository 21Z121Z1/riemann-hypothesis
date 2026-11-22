import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0179
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfGluingFacts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0324
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_iterated_integrals_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ (ν : Measure (GA D S)) (X : Set (GA D S)) (ν' : Measure (GA D T)) (X' : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) X ν → ν'.IsHaarMeasure → IsFundamentalDomain (GQ T) X' ν' → ∀ (G : GA D S → ℂ) (F : GA D T → ℂ), GlobalTheory.Grow.RapidDec S G → GlobalTheory.Grow.RapidDec T F → ∫ h in X', ∫ g in X, thetaKO om g h f * F h * conj (G g) ∂ν ∂ν' = ∫ g in X, ∫ h in X', thetaKO om g h f * F h * conj (G g) ∂ν' ∂ν := by
  first | exact @GlobalTheory.ChainOnto.ThetaSwap.integral_swap | exact GlobalTheory.ChainOnto.ThetaSwap.integral_swap | (intros; apply GlobalTheory.ChainOnto.ThetaSwap.integral_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
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

namespace GlobalTheory.ChainOnto.ThetaFirstVar

open GlobalTheory.Size

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

theorem thetaKO_left_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    ∀ γ ∈ GQ V, ∀ g, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g => by
  have e : ((γ * g, h) : GA D V × GA D W) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

theorem thetaKO_continuous_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    Continuous fun g => thetaKO ω g h f :=
  (hω.om_cont f hf 0).comp (Continuous.prodMk_left h)

theorem thetaKO_modGrowth_fst (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    (h : GA D W) : GlobalTheory.Grow.ModGrowth V fun g => thetaKO ω g h f := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * GlobalTheory.Grow.height W h ^ A, A, fun g => ?_⟩
  rw [mul_assoc _ (GlobalTheory.Grow.height W h ^ A), ← mul_pow, mul_comm (GlobalTheory.Grow.height W h)]
  exact (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h

theorem thetaKO_mul_conj_integrableOn : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (u : WO S T → ℂ) (y : GA D S → ℂ), IsThetaFunO ψ S T u → IsAutFunSm θ S y → IsCuspFun S y → ∀ (a : GA D S) (x : GA D T), IntegrableOn (fun g => thetaKO om g x u * conj (y (g * a))) 𝓕 ν := by
  intro hP D ψ S T χS χT om hω θ hθ ν 𝓕 hν h𝓕 u y hu hy hc a x
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have hR : GlobalTheory.Grow.RapidDec S fun g => conj (y (g * a)) :=
    ((GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hy hc).mul_right a).conj
  exact hR.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth_fst hθ hω hu x) (thetaKO_left_fst hω hu x)
    (thetaKO_continuous_fst hω hu x).measurable.aestronglyMeasurable

end GlobalTheory.ChainOnto.ThetaFirstVar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumNonsplitPlaceVacuumAtPrime
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
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
namespace GlobalTheory.VacInertAt

variable {D : D7}

theorem half_eq_two_smul {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) (S T : HSp D) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) fun _ => True)
    (hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u) :
    ∃ u' ∈ latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
      (fun x => x = v), u = 2 • u' := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have h2F : (2 : D.host.F) ≠ 0 := two_ne_zero
  set γ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F := α * algebraMap D.host.F _ ((2 : D.host.F)⁻¹) with hγdef
  have hγ : γ ∈ intAf D.host.F := fun w => by
    rw [hγdef, map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      rw [h1, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀]
      have : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1 := by
        rw [← map_ofNat (algebraMap (𝓞 D.host.F) D.host.F) 2, HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
      rw [this, inv_one]
    · rw [h0 w hw, zero_mul]; exact zero_mem _
  have hγv : ∀ w, ¬ w = v → evalV D.host.F w γ = 0 := fun w hw => by
    rw [hγdef, map_mul, h0 w hw, zero_mul]
  have hαγ : α = γ + γ := by
    rw [← two_mul, hγdef, mul_comm α, ← mul_assoc, ← map_ofNat (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) 2,
      ← map_mul, mul_inv_cancel₀ h2F, map_one, one_mul]
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 γ) with ha₀
  let φ : WO S T →+ WO S T := DistribMulAction.toAddMonoidHom (WO S T) a₀
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      (latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
        (fun x => x = v)).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨γ * β, GlobalTheory.VacLat.intAf_mul hγ hβ,
      fun w hw => by rw [map_mul, hγv w hw, zero_mul], a, ha, s, by rw [← hermitianSpaceBaseLattice_eq_frameLattice]; exact hs, t,
      by rw [← hermitianSpaceBaseLattice_eq_frameLattice]; exact ht, ?_⟩
    ext i j
    simp only [φ, DistribMulAction.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.VacLat.pairA_mul]
  refine ⟨a₀ • u, key hu, ?_⟩
  have he : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = a₀ + a₀ := by
    rw [ha₀, ← map_add, hαγ]
    congr 1
    exact Prod.ext (add_zero 0).symm rfl
  ext i j
  rw [two_nsmul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← add_mul, ← he]
  exact (hh i j).symm

theorem isVacAt_of_vacFin : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w = w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ),
    VacFin ψ S T v f → IsVacAt ψ S T w f := by
  intro D v w hv hw ψ S T f hf
  obtain ⟨ε, hε, -, hc, hpi⟩ := GlobalTheory.VacFixInert.inert_data hw
  have h2 := GlobalTheory.VacFixInert.two_not_mem hc
  rw [hv] at hε h2
  refine ⟨hf.1, fun e f' he u hu hhalf => ?_⟩
  have hee := (hpi e f' he).1
  have hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
    rcases hhalf with h | h
    · rw [hee] at h; exact h
    · rw [hee, GlobalTheory.IdemSupport.cA_algebraMap] at h; exact h
  obtain ⟨u', hu', rfl⟩ := half_eq_two_smul hε h2 S T u hu hh
  exact hf.2.1 u' hu'

end GlobalTheory.VacInertAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumSplitPlaceVacuumAtPrime
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
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.VacSplit

theorem isVacAt_of_vacFin : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w ≠ w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f := by
  intro D v w hvw hw ψ S T f hf
  refine ⟨hf.1, fun e f' he u hu hhalf => ?_⟩
  have he' := he
  obtain ⟨hid, rfl⟩ := GlobalTheory.CentralShift.split_of_primeIdem hw he
  obtain ⟨v', ε, hε, hf', hv'⟩ := GlobalTheory.VacLat.place_of_primeIdem he'
  rw [hvw] at hv'
  subst hv'
  have hfu : ∀ i j, (e + Formalism.L2.Theta.cA D e) * u i j = u i j := by
    have h1 := hid.1.1
    have h2 := hid.1.2.1
    have h3 : Formalism.L2.Theta.cA D e * Formalism.L2.Theta.cA D e = Formalism.L2.Theta.cA D e := by rw [← map_mul, h1]
    have h4 : Formalism.L2.Theta.cA D e * e = 0 := by rw [mul_comm]; exact h2
    rcases hhalf with h | h <;> intro i j
    · have h' : e * u i j = u i j := h i j
      rw [← h', ← mul_assoc, add_mul, h1, h4, add_zero]
    · have h' : Formalism.L2.Theta.cA D e * u i j = u i j := h i j
      rw [← h', ← mul_assoc, add_mul, h2, h3, zero_add]
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hα : α ∈ intAf D.host.F := fun w' => by
    by_cases hw' : w' = v
    · subst hw'; rw [h1]; exact one_mem _
    · rw [h0 w' hw']; exact zero_mem _
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) with ha₀
  let φ : WO S T →+ WO S T := DistribMulAction.toAddMonoidHom (WO S T) a₀
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      (latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
        fun u => u = v).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α * β, GlobalTheory.VacLat.intAf_mul hα hβ,
      fun v'' hv'' => by rw [map_mul, h0 v'' hv'', zero_mul], a, ha, s, ?_, t, ?_, ?_⟩
    · show S.frame.equivFun.symm s ∈ S.L0
      rw [Module.Basis.equivFun_symm_apply]; exact hs
    · show T.frame.equivFun.symm t ∈ T.L0
      rw [Module.Basis.equivFun_symm_apply]; exact ht
    · ext i j
      simp only [φ, DistribMulAction.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.VacLat.pairA_mul]
  have hum : u ∈ latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
      fun u => u = v := by
    have hk := key hu
    have hφ : φ u = u := by
      ext i j
      have hx := hfu i j
      rw [hf'] at hx
      exact hx
    rwa [AddSubgroup.mem_comap, hφ] at hk
  rcases hhalf with h | h
  · exact hf.2.2 e hid.1 u hum h
  · refine hf.2.2 (Formalism.L2.Theta.cA D e) ⟨by rw [← map_mul, hid.1.1], ?_, ?_⟩ u hum h
    · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm]; exact hid.1.2.1
    · obtain ⟨w', η, hη, hwη⟩ := hid.1.2.2
      exact ⟨w', η, hη, by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]; exact hwη⟩

end GlobalTheory.VacSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChain_adjoint_nonvanishing_step : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  first | exact @GlobalTheory.ChainOnto.stepUp | exact GlobalTheory.ChainOnto.stepUp | (intros; apply GlobalTheory.ChainOnto.stepUp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterInjectivePlacewiseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChainHeckeParameter_injective_placewise : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  first | exact @GlobalTheory.ChainOnto.chainPar_inj | exact GlobalTheory.ChainOnto.chainPar_inj | (intros; apply GlobalTheory.ChainOnto.chainPar_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.ParClosed

variable {D : D7}

theorem chS_succ (c : Com D) (k : ℕ) : c.chS (k + 1) = c.μ (k + 1) * c.eps (k + 1) := by
  unfold Com.chS Com.eps Lift.chrStep
  split_ifs <;> simp

theorem chT_succ (c : Com D) (k : ℕ) : c.chT (k + 1) = c.μ (k + 1) * c.eps k := by
  unfold Com.chT Com.eps Lift.chrStep
  rcases Nat.even_or_odd k with hk | hk
  · have h1 : Odd (k + 1) := hk.add_one
    have h2 : ¬ Odd k := Nat.not_odd_iff_even.2 hk
    simp [h1, h2]
  · have h1 : ¬ Odd (k + 1) := Nat.not_odd_iff_even.2 hk.add_one
    simp [h1, hk]

theorem eps_succ (c : Com D) (k : ℕ) :
    c.chS (k + 1) * (c.chT (k + 1))⁻¹ * c.eps k = c.eps (k + 1) := by
  rw [chS_succ, chT_succ]
  exact by
    have h : ∀ a b e : (AE D)ˣ →* Circle, a * b * (a * e)⁻¹ * e = b := fun a b e => by
      rw [_root_.mul_inv_rev, mul_comm e⁻¹ a⁻¹, mul_comm a b]
      simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one]
    exact h _ _ _

abbrev vf (χ : (AE D)ˣ →* Circle) : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := GlobalTheory.LFun.val (F := D.host.F) χ

theorem vf_mul (χ ψ : (AE D)ˣ →* Circle) : vf (χ * ψ) = vf χ * vf ψ := by
  funext w; simp [vf]

theorem twist_sum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → GlobalTheory.LFun.Fam K)
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : GlobalTheory.LFun.twist (∑ i ∈ s, f i) z = ∑ i ∈ s, GlobalTheory.LFun.twist (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => funext w; simp [GlobalTheory.LFun.twist]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LFun.twist_add, ih]

theorem stepPar_eq (χS χT : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) :
    stepPar χS χT t B = GlobalTheory.LFun.twist B (vf (χS * χT⁻¹)) + GlobalTheory.LFun.segFam (vf χS) t := by
  funext w; simp [stepPar, GlobalTheory.LFun.twist, GlobalTheory.LFun.segFam, vf]

theorem chainPar_closed (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B k = GlobalTheory.LFun.twist (B + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i)) D.R.t) (vf (c.eps k)) := by
  induction k with
  | zero =>
    have h1 : vf (1 : (AE D)ˣ →* Circle) = 1 := funext fun w => GlobalTheory.LFun.val_one (F := D.host.F) w
    simp [chainPar, Com.eps, h1]
  | succ k ih =>
    rw [chainPar_succ, ih, stepPar_eq, GlobalTheory.LFun.twist_twist, ← vf_mul, eps_succ, Finset.sum_Icc_succ_top (by omega),
      ← add_assoc, GlobalTheory.LFun.twist_add (B + _), GlobalTheory.LFun.twist_segFam, ← vf_mul, chS_succ, mul_comm (c.eps (k + 1))]

theorem twist_vf (μ e : (AE D)ˣ →* Circle) : (vf (μ * e))⁻¹ * vf e = (vf μ)⁻¹ := by
  funext w; simp [vf, mul_comm]

theorem vf_quot (μ ν : (AE D)ˣ →* Circle) : (vf ν)⁻¹ * vf μ = vf (μ * ν⁻¹) := by
  funext w; simp [vf, mul_comm]

end GlobalTheory.ChainOnto.ParClosed

open GlobalTheory.ChainOnto.ParClosed in

theorem GlobalTheory.ChainOnto.chainPar_twist_chT : ∀ (D : D7) (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ),
    GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ =
      GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ +
        ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t := by
  intro D c B k
  change GlobalTheory.LFun.twist (chainPar c B k) (vf (c.chT (k + 1)))⁻¹ =
    GlobalTheory.LFun.twist B (vf (c.μ (k + 1)))⁻¹ + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t
  rw [chainPar_closed, GlobalTheory.LFun.twist_twist, chT_succ, twist_vf, GlobalTheory.LFun.twist_add, twist_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.LFun.twist_segFam, vf_quot]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), IsInfFam θ → Matches X h J χ t → ∀ T ∈ MultT θ M J χ, ∀ x : SmT M, RowFun X (evS X h t (T x)) ∧ MemLp (evS X h t (T x)) 2 (muX X) := by
  first | exact @GlobalTheory.Core.Mi.rowFun_evS | exact GlobalTheory.Core.Mi.rowFun_evS | (intros; apply GlobalTheory.Core.Mi.rowFun_evS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedFrameGramOrth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem transported_frame_gram_orth : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (i j : Fin (D.sp.X 0).rank) (a : Fin D.R.rS), (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) = (D.sp.X 0).gram i j ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.eX a) = 0 ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.fY a) = 0 ∧ (VS D).hT (X.zu u) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) = 0 := by
  intro D X u F₀ tr i j a
  have key : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) (tr.wt.symm y) = (VS D).hT x y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have key2 : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) y = (VS D).hT x (tr.wt y) := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have key3 : ∀ (x y : (VS D).V), (VS D).hT x (tr.wt.symm y) = (VS D).hT (tr.wt x) y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key, Fin.cast_cast, Fin.cast_eq_self]
    exact D.sp.iXY_isom 0 hm _ _
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_e]
    exact (D.sp.hyp_orthX a _).1
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_f]
    exact (D.sp.hyp_orthX a _).2
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key3, tr.weight_z]
    exact Formalism.MainNotions.BridgeLemma₂.z_orth_embedding D u _

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlace
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
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.UnrPlDict

open GlobalTheory.IdemSupport

variable {D : D7}

theorem exists_glue_kill {χ : (AE D)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 D.host.E)} (hu : UnrAt χ w)
    {e : AE D} (hd : GlobalTheory.IdemSupport.IsDelta (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) w e)
    (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D) (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) :
    ∃ y : (AE D)ˣ, (y : AE D) = e * (x : AE D) + (1 - e) ∧ χ y = 1 := by
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hm : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (x : AE D) w *
      GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((x⁻¹ : (AE D)ˣ) : AE D) w = 1 := by
    rw [← ev_mul, Units.mul_inv, map_one]
    try rfl
  let u : (w.adicCompletion D.host.E)ˣ :=
    ⟨_, _, hm, by rw [mul_comm]; exact hm⟩
  have hU : Formalism.L2.Host.IsUnitAt w u := by
    rw [GlobalTheory.LFun.EulerTie.isUnitAt_iff]
    exact ⟨(hΦ.int _).1 h1 w, (hΦ.int _).1 h2 w⟩
  refine ⟨GlobalTheory.LFun.locIdele D.host.F w u, (GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd rfl).symm, ?_⟩
  have := congrArg (fun z : ℂˣ => (z : ℂ)) (hu u hU)
  exact Circle.ext this

theorem unrPl_of_unrAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w.under (𝓞 D.host.F) = v → ∀ χ : (AE D)ˣ →* Circle,
    (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ := by
  intro D v w hw χ hχ e f hp x hx h1 h2
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hd := (of_isPrimeIdem hΦ hp).1
  rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · have hd' := delta_conj hΦ hd
    obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    obtain ⟨z, hz, hz1⟩ := exists_glue_kill (hχ (cP w) ((under_cP w).trans hw)) hd' x h1 h2
    have ho : e * cA D e = 0 := hi.1.2.1
    have e1 : x = y * z := Units.ext (by
      rw [Units.val_mul, hy, hz]
      linear_combination (-1 : AE D) * hx - ((x : AE D) - 1) ^ 2 * ho)
    rw [e1, map_mul, hy1, hz1, one_mul]
  · obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    have e1 : x = y := Units.ext (by rw [hy]; linear_combination (-1 : AE D) * hx)
    rw [e1, hy1]

end GlobalTheory.UnrPlDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilConjugationAdjointRuleStandardCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilConjugationAdjointRule_standard_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.ConjAdjoint ψ S T := by
  first | exact @GlobalTheory.WeilConjAdjoint.conjAdjoint_holds | exact GlobalTheory.WeilConjAdjoint.conjAdjoint_holds | (intros; apply GlobalTheory.WeilConjAdjoint.conjAdjoint_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelationsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ (g : GA D S) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), ∑ i, a i • heisO ψ S T (y i) F = F → ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F = 0 → ∫ w in X, om (g, 1) F w * conj (F w) ∂m = 0 := by
  first | exact @GlobalTheory.ChainOnto.coef_zero_of_heis_relations | exact GlobalTheory.ChainOnto.coef_zero_of_heis_relations | (intros; apply GlobalTheory.ChainOnto.coef_zero_of_heis_relations <;> assumption)
end

