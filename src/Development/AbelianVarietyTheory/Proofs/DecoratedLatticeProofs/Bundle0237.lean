import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryLocalPointLatticeGraphNormIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPolynomialMulGaussianOfAnnihilated

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLifts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem comb_sum_mul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) {n : ℕ} (a : Fin n → ℂ)
    (F : Fin n → WO S T → ℂ) :
    comb ψ S T c (fun w => ∑ i, a i * F i w) = fun w => ∑ i, a i * comb ψ S T c (F i) w := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => by ring

theorem comb_pureTensorO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS sT BS BT) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (c : WO S T →₀ ℂ)
    (hc : IsFinComb c) (P : PolF D T.rank S.rank) :
    comb ψ S T c (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T c f) P := by
  let e := c.support.equivFin
  have key := (GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D ψ θ S T hψ hθ sS sT BS BT f hf c.support.card (fun i => c (e.symm i).1)
    (fun i => (e.symm i).1) (fun i => hc _ (e.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ c.support, c u • g u = ∑ i, c (e.symm i).1 • g (e.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort c.support]
    exact (Equiv.sum_comp e.symm (fun u : c.support => c u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem integrableOn_kernel {S T : HSp D} (hS : CoCpt S) (v : Vol S) {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hw : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {φ : GA D S → ℂ} (hφ : IsContAut S φ) (h : GA D T) :
    IntegrableOn (fun g => om (g, h) f 0 * φ g) v.𝓕 v.μ := by
  have hc : Continuous fun g : GA D S => om (g, h) f 0 :=
    (hw.om_cont f hf 0).comp (by fun_prop : Continuous fun g : GA D S => (g, h))
  refine (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS v Unit (fun g _ => om (g, h) f 0 * φ g) ((hc.mul hφ.2).comp continuous_fst) ?_).1 ()
  intro γ hγ g _
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply, hw.om_aut γ hγ 1 (one_mem _) _ (hw.om_pres _ _ hf), hφ.1 γ hγ g]

theorem biLift_biComb_fockSum : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank) (C : WO A S → WO S A' → ℂ), (∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  intro D _ _ hL ψ θ hθ A S A' x y z hx hy hz k k' hk hk' n P P' C hC φ hφ
  obtain ⟨χA, χS, hwA⟩ := hk.weil
  obtain ⟨χS', χA', hwB⟩ := hk'.weil
  have hX : ∀ i, IsThetaFunO ψ A S (k.pt ψ θ x y (P i)) := fun i => (hL ψ θ hθ A S x y hx hy k hk (P i)).1
  have hY : ∀ i, IsThetaFunO ψ S A' (k'.pt ψ θ y z (P' i)) := fun i => (hL ψ θ hθ S A' y z hy hz k' hk' (P' i)).1
  have hLc : ∀ i, IsContAut S (k.lift ψ θ x y (P i) φ) := fun i => (hL ψ θ hθ A S x y hx hy k hk (P i)).2.1 φ hφ
  have hcX : ∀ i, comb ψ A S k.c (pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i)) = k.pt ψ θ x y (P i) := fun i =>
    comb_pureTensorO ψ θ A S hwA.std hθ _ _ _ _ k.vac hk.vac.2.theta k.c hk.fin (P i)
  have hcY : ∀ i, comb ψ S A' k'.c (pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i)) = k'.pt ψ θ y z (P' i) :=
    fun i => comb_pureTensorO ψ θ S A' hwB.std hθ _ _ _ _ k'.vac hk'.vac.2.theta k'.c hk'.fin (P' i)
  have hbi : biComb ψ A S A' k.c k'.c C = fun u v => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v := by
    funext u v
    simp only [biComb]
    have e1 : (fun u' => comb ψ S A' k'.c (C u') v) = fun u' => ∑ i,
        comb ψ S A' k'.c (pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i)) v *
          pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u' := by
      funext u'
      have : C u' = fun v => ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u' *
          pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := funext (hC u')
      rw [this, comb_sum_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e1, comb_sum_mul]
    simp only [hcX, hcY]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hint : ∀ h₀ h₁ h₂, k'.om (h₁, h₂) (fun v => k.om (h₀, h₁)
      (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) 0) 0 =
      ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
    intro h₀ h₁ h₂
    have e1 : ∀ v, (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) =
        ∑ i, k'.pt ψ θ y z (P' i) v • k.pt ψ θ x y (P i) := by
      intro v; funext u; simp [Finset.sum_apply, mul_comm]
    have e2 : (fun v => k.om (h₀, h₁) (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) 0) =
        ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 • k'.pt ψ θ y z (P' i) := by
      funext v; rw [e1 v, map_sum]; simp [Finset.sum_apply, mul_comm]
    rw [e2, map_sum]; simp [Finset.sum_apply]
  funext h₂
  have hin : ∀ h₁, ∫ h₀ in x.vol.𝓕, φ h₀ * ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 *
      k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 ∂x.vol.μ =
      ∑ i, k.lift ψ θ x y (P i) φ h₁ * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
    intro h₁
    have e : (fun h₀ => φ h₀ * ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 *
        k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0) = fun h₀ => ∑ i,
          k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 * φ h₀ * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
      funext h₀; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const]
      rfl
    · intro i _
      exact (integrableOn_kernel hx.cpt x.vol hwA (hX i) hφ h₁).mul_const _
  simp only [biLift, hbi, hint, hin, Finset.sum_apply]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [KerDat.lift, liftT_apply]
    congr 1
    funext h₁
    exact mul_comm _ _
  · intro i _
    have := (integrableOn_kernel hy.cpt y.vol hwB (hY i) (hLc i) h₂)
    exact Integrable.congr this (Filter.Eventually.of_forall fun h₁ => mul_comm _ _)

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSectionStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFlatSection_eq_translate_standardSection : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A) (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f → ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f) → s0 B A.rank = sZero A B ∧ (∀ (z : ℂ) (g : GA D (dblSp A)), flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z g = npow (absA D (aP A p)) (sZero A B - z) * sect omS (hgtStd A a κ p) Φ z (κ (g * p))) ∧ ∀ g : GA D (dblSp A), (omS (κ (g * p)) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f) := by
  first | exact @GlobalTheory.StdUnn.flat_swSec_eq_sect | exact GlobalTheory.StdUnn.flat_swSec_eq_sect | (intros; apply GlobalTheory.StdUnn.flat_swSec_eq_sect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaEqSumSchrodingerFunctionPeriodisatioStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledTheta_eq_sum_schrodingerFunction_periodisation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x : Mx D B.rank A.rank, (Summable fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => ‖sch ψ A B ν 𝓨 f (x + rat ξ)‖) ∧ HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ)) (f ((dblDec A).extX B x)) := by
  first | exact @GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch | exact GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch | (intros; apply GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingClassOffOpenOrbitFixedByUnipotentRadicalStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingClass_offOpenOrbit_fixedByUnipotentRadical : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ¬ (∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V) → ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C ∧ (∀ n ∈ NI V C, ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1) ∧ ∀ δ ∈ GQ V, γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  first | exact @GlobalTheory.Core.Rk.Dich.offOpen | exact GlobalTheory.Core.Rk.Dich.offOpen | (intros; apply GlobalTheory.Core.Rk.Dich.offOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRight
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.EulerProd

open Filter Topology

theorem limit_eq_prod_mul {ι : Type} (S : Finset ι) (f : ι → ℂ) (I : Finset ι → ℂ) {P J : ℂ}
    (hP : HasProd (fun v : {v : ι // v ∉ (S : Set ι)} => f v.1) P) (hJ : Tendsto I atTop (𝓝 J))
    (h : ∀ T U : Finset ι, Disjoint S T → (∀ u, u ∈ U ↔ u ∈ S ∨ u ∈ T) → I U = (∏ v ∈ T, f v) * I S) :
    J = P * I S := by
  classical
  let e : {v : ι // v ∉ (S : Set ι)} ↪ ι := Function.Embedding.subtype _
  have ht : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => S ∪ T.map e) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop (b.subtype fun v => v ∉ (S : Set ι))).mono fun T hT u hu => ?_
    by_cases hS : u ∈ S
    · exact Finset.mem_union_left _ hS
    · exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨u, hS⟩, hT (Finset.mem_subtype.2 hu), rfl⟩)
  have h1 := hJ.comp ht
  have h2 : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => (∏ v ∈ T, f v.1) * I S) atTop (𝓝 (P * I S)) :=
    Tendsto.mul_const _ hP
  refine tendsto_nhds_unique h1 (h2.congr fun T => ?_)
  rw [Function.comp_apply, h (T.map e) _ ?_ fun u => Finset.mem_union, Finset.prod_map]
  · rfl
  · refine Finset.disjoint_left.2 fun u hu hu' => ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hu'
    exact w.2 hu

theorem bounded_of_isParamFun (hP : GlobalTheory.Published.CuspRapidDecay) {D : D7} (hB : ParamBoundOn D (fun _ => True))
    {θ : InfFam D} {A : HSp D} {cA : CptF A} {L : Lat A} (hθ : IsInfFam θ) (hL : IsSelfDualC A L)
    (m : Measure (GA D A)) (hm : m.IsHaarMeasure) {Sf : Finset (FinPl D)} {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA)
    {par : GlobalTheory.LFun.Fam D.host.E} (hpar : GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u par) :
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (Sf : Set (FinPl D))) par A.rank ((A.rank : ℝ) / 2) := by
  intro w hw
  have hv : w.under (𝓞 D.host.F) ∉ Sf := hw
  have h0 : u ≠ 0 := (hpar _ hw w rfl).ne_zero
  have hs : SphFun A L Sf u := fun v hv k hk g => by
    obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v := by
      have := v.isMaximal
      obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
        (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
          (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
      refine ⟨⟨Q, hQ.isPrime, fun hb => v.ne_bot ?_⟩, HeightOneSpectrum.ext e⟩
      rw [← e, hb, Ideal.comap_bot_of_injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (FaithfulSMul.algebraMap_injective _ _)]
    exact (congrFun ((hpar v hv w' hw').mem_fixed ⟨k, hk⟩) g).trans (by simp)
  have hc := GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified hP D θ A cA L hθ m hm Sf u hu u hu par hpar hs _ hv 1 (map_one _)
  have h1 : MemL2Quotient (GQ A) m u := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu).1
  have hpos := petersson_self_pos h1 (mem_cuspForms.1 hu).1.1.toIsAutFun.cont h0
  have hne : rcoef m u u (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) ≠ 0 := by
    have e : rTr A (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) u = u := funext fun g => by
      simp only [rTr, map_one, mul_one]
    rw [rcoef, e]
    intro h
    rw [h] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨h2, h3⟩ := hB A L hL _ trivial par _ hc hne w rfl
  exact ⟨h2.le, h3⟩

theorem eulerRight : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) →
    ParamBoundOn D (fun _ => True) → EulerRight D := by
  intro hP D hS hZ hB ψ θ A B χA χB sA sB t cA a om ν 𝓕 hp LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph
    s hs hint
  have ha : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
  have hb := bounded_of_isParamFun hP hB hp.setting.2.2.2.1 hU.sdA m hm hu₁ hpar
  have hL := GlobalTheory.T.hasProd_partialLFunctionTwistedByChar_local_factors D Sf par χB _ _ hb (s + 1 / 2) (by
    have : (s + 1 / 2 : ℂ).re = s.re + 1 / 2 := by simp
    rw [this]; linarith)
  obtain ⟨hd0, hdv, hd⟩ := (GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank).2 s (by linarith)
  refine limit_eq_prod_mul Sf
    (fun v => GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s)
    (fun S => ∫ g in openOff A LA S, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) ?_
    (GlobalTheory.T.tendsto_setIntegral_unramifiedOutsideOpenSubset D A LA hU.sdA m _ hint) fun T U hT hTU =>
      GlobalTheory.T.setIntegral_unramified_places_union_eq_local_factors hP D hS hZ ψ θ A B χA χB sA sB t cA a om ν 𝓕 hp LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par
        hpar hsph s (by linarith) hint Sf T le_rfl hT U hTU
  exact (Tendsto.div hL hd hd0).congr fun T => (Finset.prod_div_distrib _ _).symm

end GlobalTheory.Core.Rk.EulerProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightSplitPlaceChartBiInvariantTorusVal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped NNReal
namespace GlobalTheory.ChartHgt

open GlobalTheory.Doubling in

theorem hgtV_mul_stab (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    {k k' : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v} (hk : k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v)
    (hk' : k' ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) (g : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v (k * g * k') = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v g := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hI := GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom (GlobalTheory.AdelicU.isCMExt_host D) (gram_hdbl V) (isHermND_gram V)
    (isHermND_gram (dblSp V)) τ Λ (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV
  congr 1
  have e1 : ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (k * g * k', 1) =
      (ioDiag (R := Fv D.host.F v) (gram_hdbl V) k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig (dblSp V).gram v) *
        ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (g, 1) * ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (k', k⁻¹) := by
    rw [coe_ioDiag, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp [mul_assoc]
  rw [e1]
  refine (HasIwasawa.hgtH_right (continuous_absEv v) (isCompact_KFin v) hI _
    ((ioH_mem_KFin (gram_hdbl V)).2 ⟨hk', inv_mem hk⟩)).trans ?_
  refine (HasIwasawa.hgtH_left (continuous_absEv v) (isCompact_KFin v) hI _ _).trans ?_
  rw [aH_ioDiag, abs_detH (absEv_conjUnit _ v) (isHermND_gram V).2, one_mul]

open ValuativeRel in

theorem nnnorm_unif (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : (Fv F v)ˣ)
    (h : letI := GlobalTheory.LocalData.complRel v; valuation (Fv F v) (ϖ : Fv F v) = uniformizer (Fv F v)) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    ‖(ϖ : Fv F v)‖₊ = ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℕ) : ℝ≥0)⁻¹ := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  rw [GlobalTheory.LFun.SatBoundGL.resCard_completion]
  apply GlobalTheory.norm_uniformiser_eq_inv_absNorm
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have h1 : Valued.v (ϖ : Fv F v) < 1 := by
    rw [← he.lt_one_iff_lt_one, h]; exact uniformizer_lt_one
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have h2 : Valued.v p ≤ Valued.v (ϖ : Fv F v) := by
    rw [← he.le_iff_le, h, le_uniformizer_iff, he.lt_one_iff_lt_one, hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have h0 : Valued.v (ϖ : Fv F v) ≠ 0 := (map_ne_zero _).2 ϖ.ne_zero
  rw [hp, ← WithZero.exp_log h0, WithZero.exp_le_exp] at h2
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold Formalism.UG.IsUnifV
  rw [← WithZero.exp_log h0]
  have : WithZero.log (Valued.v (ϖ : Fv F v)) = -1 := by omega
  rw [this]; rfl

theorem hgtFin_ioH_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (hQ : Q = GlobalTheory.Doubling.dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (g : GlobalTheory.AdelicU.GLoc σ J v) :
    GlobalTheory.Doubling.hgtFin σ Q L v (GlobalTheory.Doubling.ioH (Fv F v) σ hQ (g, 1)) =
      GlobalTheory.Doubling.hgtFin σ (GlobalTheory.Doubling.dblGram finSumFinEquiv J) L v (GlobalTheory.Doubling.ioH (Fv F v) σ rfl (g, 1)) := by
  subst hQ; rfl

theorem min_zpow_inv (q : ℝ≥0) (hq : 1 ≤ q) (m : ℤ) : min ((q⁻¹) ^ m) (((q⁻¹) ^ m)⁻¹) = q ^ (-|m|) := by
  rw [_root_.inv_zpow', ← _root_.zpow_neg, neg_neg]
  rcases le_total 0 m with hm | hm
  · rw [abs_of_nonneg hm, min_eq_left (zpow_le_zpow_right₀ hq (by omega))]
  · rw [abs_of_nonpos hm, neg_neg, min_eq_right (zpow_le_zpow_right₀ hq (by omega))]

theorem prod_zpow_eq {ι : Type} (s : Finset ι) (q : ℝ≥0) (hq : q ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem bridge : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v)
    (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ →
    Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v,
    (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) →
    ∃ (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (β : GL (Fin s.V.rank) (Fv D.host.F v))
      (ε : Fin D.R.r ⊕ Blocks k D.R.t ≃ Fin s.V.rank), GlobalTheory.AdelicU.IsSplitBasis τ s.Λ β ∧
      ∀ y, (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e y)).1.submatrix ε ε = y.1 := by
  intro D s k v φ ι _ hfr ⟨ε, _, hε⟩ e he
  refine ⟨_, _, ε, GlobalTheory.ChartStab.isSplitBasis_frCo hfr φ, fun y => ?_⟩
  have h2 := (hε y).2
  rw [he y, GlobalTheory.ChartStab.grpCo_emb] at h2
  exact h2

theorem isHgt_chart : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y) := by
  intro D s k v φ ι hΛ hβ hι e he x ϖ hϖ
  obtain ⟨τ, β, ε, hB, hy⟩ := bridge D s k v φ ι hΛ hβ hι e he
  have hΨ : ∀ y, (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e y)).1 =
      y.1.submatrix ε.symm ε.symm := fun y => by
    rw [← hy y, Matrix.submatrix_submatrix]; simp
  have hmul : ∀ a b, e (a * b) = e a * e b := fun a b =>
    (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β).injective
      (Units.ext (by rw [map_mul, Units.val_mul, hΨ, hΨ, hΨ, Units.val_mul, Matrix.submatrix_mul_equiv]))
  have hK := GlobalTheory.ChartStab.chart_stab D s k v φ ι hΛ hβ hι e he
  refine ⟨fun κ hκ g => ⟨?_, ?_⟩, fun e' => ?_⟩
  · have := hgtV_mul_stab D s.V s.Λ hΛ v τ ((hK κ).2 hκ) (one_mem _) (e g)
    rwa [mul_one, ← hmul] at this
  · have := hgtV_mul_stab D s.V s.Λ hΛ v τ (one_mem _) ((hK κ).2 hκ) (e g)
    rwa [one_mul, ← hmul] at this
  · haveI := hΛ.1
    have hsd := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v
    obtain ⟨-, hval, -⟩ := (GlobalTheory.GraphNorm.graphNormFinite D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D)
      s.V.rank s.V.gram (GlobalTheory.Doubling.isHermND_gram s.V) s.Λ v hsd).1 τ β hB
      (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e'))
    have hd : GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.IsElemDiv (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D)
        (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')))
        (fun i => ϖ ^ e' (ε.symm i)) := by
      refine ⟨1, one_mem _, 1, one_mem _, ?_⟩
      rw [hΨ, GlobalTheory.GLDoubling.val_torusElt, Matrix.submatrix_diagonal_equiv]
      simp
    have h1 := hval _ hd
    obtain ⟨-, -, -, -, hv⟩ := hϖ
    have hn := nnnorm_unif _ v ϖ hv
    have hq : 1 ≤ ((GlobalTheory.SplitWeil.resCard (Fv D.host.F v) : ℕ) : ℝ≥0) := by
      rw [GlobalTheory.LFun.SatBoundGL.resCard_completion]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (fun h0 => v.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0))
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')) =
        (GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.graphHgt D.sp.cm.sig s.V.gram s.Λ v (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')) : ℝ) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.graphHgt
      exact congrArg _ (hgtFin_ioH_eq _ _ _ _ _ _ _)
    refine e2.trans ?_
    rw [h1]
    simp only [Units.val_zpow_eq_zpow_val, nnnorm_zpow, hn]
    simp only [min_zpow_inv _ hq]
    rw [prod_zpow_eq _ _ (zero_lt_one.trans_le hq).ne', NNReal.coe_zpow, NNReal.coe_natCast, Finset.sum_neg_distrib]
    congr 2
    exact Equiv.sum_comp ε.symm (fun a => |e' a|)

end GlobalTheory.ChartHgt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem delta_isKFinVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → IsKFinVec omh (Khat A a) (delta A B Φ₁ Φ₂) := by
  intro D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ₁ Φ₂ h₁ h₂
  obtain ⟨-, -, -, hθ, -, -, hcA, hcB, -⟩ := hP.setting
  have hc := GlobalTheory.T.doubled_cartanInvolution_commute_maximalCompact D θ A sA a hθ hcA hP.maj_eq
  have hb := GlobalTheory.T.doublingSeesawTensorMap_polynomial_fock_vector D ψ θ A B sA sB hP.weil.std hθ Φ₁ Φ₂ h₁ h₂
  exact GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp A) B 1 χB omh _ sB homh hθ hc.1 hcB (Khat A a) (isCompact_Khat A a) hc.2 _ hb

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_leftInvariant_rep_conjugateTensor : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) := by
  first | exact @GlobalTheory.ConjRowRep.exists_contRep | exact GlobalTheory.ConjRowRep.exists_contRep | (intros; apply GlobalTheory.ConjRowRep.exists_contRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleTraceZeroNormAdjustRealComponentsStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idele_traceZero_norm_adjust_realComponents : ∀ (D : D7) (μ : D.host.E), IsSkew μ → ∀ u₀ : (AE D)ˣ, ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ (∀ v, compFin D.host.F D.host.E v u = compFin D.host.F D.host.E v u₀) ∧ ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4 := by
  first | exact @GlobalTheory.StdUnn.exists_scal_real | exact GlobalTheory.StdUnn.exists_scal_real | (intros; apply GlobalTheory.StdUnn.exists_scal_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPolynomialMulGaussianOfAnnihilatedStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_mul_gaussian_of_annihilated : ∀ (D : D7) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ (N : ℕ) (f : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ), ContDiff ℝ ∞ f → (∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annC V l s q.1 q.2 g) f = 0) → ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ z, f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  first | exact @GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC | exact GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC | (intros; apply GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC <;> assumption)
end

