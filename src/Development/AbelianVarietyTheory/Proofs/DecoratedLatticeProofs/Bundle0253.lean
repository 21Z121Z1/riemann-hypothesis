import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Core.Mi.SepPer

variable {D : D7}

def contLeft (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | Continuous F ∧ ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨hF.add hG, fun γ hγ g => by simp [hF' γ hγ g, hG' γ hγ g]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c F ⟨hF, hF'⟩
    exact ⟨continuous_const.mul hF, fun γ hγ g => by simp [hF' γ hγ g]⟩

theorem rTrans_mem {V : HSp D} (t : GA D V) {F : GA D V → ℂ} (hF : F ∈ contLeft V) : rTrans t F ∈ contLeft V :=
  ⟨hF.1.comp (continuous_id.mul continuous_const), fun γ hγ g => by
    simp only [rTrans, mul_assoc]; exact hF.2 γ hγ (g * t)⟩

theorem norm_psiBes {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (n : GA D S) : ‖psiBes ψ d θ z n‖ = 1 := by
  exact hψ.1.2.1 _

theorem per_add_bound {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) (Ω : Set (GA D B.V)) (hΩc : IsCompact Ω)
    (hΩ : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) :
    ∃ C : ℝ, (∀ f g, f ∈ contLeft B.V → g ∈ contLeft B.V → B.per ψ φ (f + g) = B.per ψ φ f + B.per ψ φ g) ∧
      ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) → ‖B.per ψ φ f‖ ≤ C * K := by
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut B.cpt hφ
  have hμ : B.vA.μ B.vA.𝓕 < ⊤ := GlobalTheory.Unf.vol_fund_lt_top B.cpt B.vA
  have hν1 : B.vN.ν B.vN.𝓝 = 1 := B.vN.unit.2.2
  have hν : B.vN.ν B.vN.𝓝 < ⊤ := by rw [hν1]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  have hψc : Continuous ψ := hψ.1.1
  have hemb := GlobalTheory.Unf.BesSemi.continuous_embA B.d B.o
  have hpsi := GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψc 1 (vecB B.o B.ζ)

  have hsup : ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) →
      ∀ (h : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h)‖ ≤ K := by
    intro f hf K hK h n
    have hs : n.1 * embA B.d B.o h ∈ besGrp B.d B.o :=
      mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)
    obtain ⟨γ, hγ, hγs⟩ := hΩ _ hs
    rw [← hf.2 γ (Subgroup.mem_inf.1 hγ).1]
    exact hK _ hγs
  have hbd : ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) →
      ∀ h n, ‖GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n‖ ≤ Cφ * K := by
    intro f hf K hK h n
    simp only [GlobalTheory.MixPer.besFun, norm_mul, norm_star, norm_psiBes hψ, mul_one]
    exact mul_le_mul (hCφ h) (hsup f hf K hK h n) (norm_nonneg _) ((norm_nonneg _).trans (hCφ h))
  have hcont : ∀ f, f ∈ contLeft B.V → ∀ h, Continuous (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) := by
    intro f hf h
    change Continuous fun n : flagN B.d => φ h * f (n.1 * embA B.d B.o h) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)
    exact (continuous_const.mul (hf.1.comp (continuous_subtype_val.mul continuous_const))).mul
      (continuous_star.comp (hpsi.comp continuous_subtype_val))
  have hcontH : ∀ f, f ∈ contLeft B.V → ∀ n : flagN B.d,
      Continuous fun h => GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n := by
    intro f hf n
    simp only [GlobalTheory.MixPer.besFun]
    exact (hφ.2.mul (hf.1.comp (continuous_const.mul hemb))).mul continuous_const
  have hK : ∀ f, f ∈ contLeft B.V → ∃ K : ℝ, ∀ x ∈ Ω, ‖f x‖ ≤ K := by
    intro f hf
    obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hf.1.continuousOn
    exact ⟨K, hK⟩
  have hin : ∀ f, f ∈ contLeft B.V → ∀ h,
      IntegrableOn (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν := by
    intro f hf h
    obtain ⟨K, hK⟩ := hK f hf
    exact Measure.integrableOn_of_bounded hν.ne (hcont f hf h).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n => hbd f hf K hK h n)
  have houtC : ∀ f, f ∈ contLeft B.V →
      Continuous fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
    intro f hf
    obtain ⟨K, hK⟩ := hK f hf
    haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA B.A
    exact continuous_of_dominated (bound := fun _ => Cφ * K)
      (fun h => (hcont f hf h).aestronglyMeasurable)
      (fun h => Filter.Eventually.of_forall fun n => hbd f hf K hK h n) (integrable_const _)
      (Filter.Eventually.of_forall fun n => hcontH f hf n)
  have hout : ∀ f, f ∈ contLeft B.V →
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
    intro f hf
    obtain ⟨K, hK⟩ := hK f hf
    refine Measure.integrableOn_of_bounded (M := Cφ * K * B.vN.ν.real B.vN.𝓝) hμ.ne (houtC f hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun h => ?_)
    exact norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd f hf K hK h n
  refine ⟨Cφ * B.vA.μ.real B.vA.𝓕, fun f g hf hg => ?_, fun f hf K hK' => ?_⟩
  · have e : ∀ h n, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ (f + g) h n =
        GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n + GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ g h n := by
      intro h n; simp only [GlobalTheory.MixPer.besFun, Pi.add_apply]; ring
    simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
    simp_rw [e]
    rw [← integral_add (hout f hf) (hout g hg)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_add (hin f hf h) (hin g hg h))
  · have hνr : B.vN.ν.real B.vN.𝓝 = 1 := by simp [Measure.real, hν1]
    have h1 : ∀ h ∈ B.vA.𝓕, ‖∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν‖ ≤ Cφ * K := by
      intro h _
      have := norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd f hf K hK' h n
      rwa [hνr, mul_one] at this
    have h2 := norm_setIntegral_le_of_norm_le_const hμ h1
    simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
    calc _ ≤ Cφ * K * B.vA.μ.real B.vA.𝓕 := h2
      _ = _ := by ring

end GlobalTheory.Core.Mi.SepPer

namespace GlobalTheory.Core.Mi.SepPer

variable {D : D7}

theorem mult_mem_contLeft (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (u : M.Vec) : T u ∈ contLeft V := by
  let Q : Submodule ℂ (MMap M) :=
    { carrier := {T | ∀ u, T u ∈ contLeft V}
      add_mem' := fun ha hb u => by simpa using (contLeft V).add_mem (ha u) (hb u)
      zero_mem' := fun u => by simpa using (contLeft V).zero_mem
      smul_mem' := fun c T hT u => by simpa using (contLeft V).smul_mem c (hT u) }
  have : Mult θ M J χ ≤ Q := Submodule.span_le.2 fun T hT u => ⟨(hT.aut u).cont, (hT.aut u).left⟩
  exact this hT u

theorem mult_bound (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (Ω : Set (GA D V)) (hΩ : IsCompact Ω)
    (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g ∈ Ω, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact GlobalTheory.T.cuspFormMap_values_compact_sobolev_bound D θ V S M J χ hθ T hT Ω hΩ τ v
  | zero => exact ⟨[], 0, by simp, fun w g _ => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    obtain ⟨L₁, C₁, hL₁, hb₁⟩ := h₁
    obtain ⟨L₂, C₂, hL₂, hb₂⟩ := h₂
    refine ⟨L₁ ++ L₂, max C₁ 0 + max C₂ 0, fun l hl => ?_, fun w g hg => ?_⟩
    · rcases List.mem_append.1 hl with h | h
      exacts [hL₁ l h, hL₂ l h]
    · set s₁ := (L₁.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      set s₂ := (L₂.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      have hs₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      have hs₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [List.map_append, List.sum_append, MultilinearMap.add_apply, Pi.add_apply]
      calc _ ≤ ‖T₁ (Function.update v τ w) g‖ + ‖T₂ (Function.update v τ w) g‖ := norm_add_le _ _
        _ ≤ C₁ * s₁ + C₂ * s₂ := add_le_add (hb₁ w g hg) (hb₂ w g hg)
        _ ≤ max C₁ 0 * s₁ + max C₂ 0 * s₂ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₁)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₂)
        _ ≤ (max C₁ 0 + max C₂ 0) * (s₁ + s₂) := by
          have := le_max_right C₁ 0; have := le_max_right C₂ 0; nlinarith
  | smul c T _ h =>
    obtain ⟨L, C, hL, hb⟩ := h
    refine ⟨L, ‖c‖ * C, hL, fun w g hg => ?_⟩
    rw [MultilinearMap.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb w g hg) (norm_nonneg _)

end GlobalTheory.Core.Mi.SepPer

namespace GlobalTheory.Core.Mi

open SepPer in

theorem sepCont_per_rTrans : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S) (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (φ : GA D B.A → ℂ), IsInfFam θ → IsStdChar D ψ (-1) → IsContAut B.A φ → ∀ T ∈ MultT θ M J χ, ∃ Λ : SmT M →ₗ[ℂ] ℂ, SepCont M Λ ∧ ∀ x, Λ x = B.per ψ φ (rTrans t (T x)) := by
  intro D θ ψ ρ B S M J χ t φ hθ hψ hφ T hT
  obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D ρ B
  obtain ⟨Cp, hadd, hbd⟩ := per_add_bound B hψ hφ Ω hΩc hΩ
  set T' : MMap M := PiTensorProduct.lift.symm T with hT'
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  have hTt : ∀ u : M.Vec, T (PiTensorProduct.tprod ℂ u) = T' u := by
    intro u
    have : T = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply T).symm
    rw [this, PiTensorProduct.lift.tprod]
  have hmem : ∀ x : SmT M, T x ∈ contLeft B.V := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [map_smul, hTt]
      exact (contLeft B.V).smul_mem r (mult_mem_contLeft θ M J χ hT'm u)
    | add x y hx hy =>
      rw [map_add]
      exact (contLeft B.V).add_mem hx hy
  let Λ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun x => B.per ψ φ (rTrans t (T x))
      map_add' := fun x y => by
        have e : rTrans t (T (x + y)) = rTrans t (T x) + rTrans t (T y) := by
          funext g; simp [rTrans]
        rw [e]
        exact hadd _ _ (rTrans_mem t (hmem x)) (rTrans_mem t (hmem y))
      map_smul' := fun c x => by
        have e : rTrans t (T (c • x)) = c • rTrans t (T x) := by
          funext g; simp [rTrans]
        have := GlobalTheory.HandHom.per_smul B ψ 1 c φ (rTrans t (T x))
        rw [one_smul, one_mul] at this
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [e, this] }
  refine ⟨Λ, fun τ v => ?_, fun x => rfl⟩
  have hΩt : IsCompact ((fun g => g * t) '' Ω) := hΩc.image (continuous_id.mul continuous_const)
  obtain ⟨L, Cu, hL, hb⟩ := mult_bound θ hθ M J χ hT'm _ hΩt τ v
  let ℓ₀ : M.sm τ →ₗ[ℂ] ℂ := (Λ.compMultilinearMap (PiTensorProduct.tprod ℂ)).toLinearMap v τ
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓw : ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w)) := by
    intro w
    have := congrArg (fun m => m w) hℓ
    simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
  refine ⟨ℓ, ⟨L, Cp * Cu, hL, fun w hw => ?_⟩, hℓw⟩
  have hw' : w ∈ M.sm τ := Submodule.subset_span hw
  have e := hℓw ⟨w, hw'⟩
  simp only at e
  rw [e]
  change ‖B.per ψ φ (rTrans t (T (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩))))‖ ≤ _
  have hK : ∀ x ∈ Ω, ‖rTrans t (T (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩))) x‖ ≤
      Cu * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum := by
    intro x hx
    rw [rTrans, hTt]
    exact hb ⟨w, hw'⟩ (x * t) ⟨x, hx, rfl⟩
  calc _ ≤ Cp * (Cu * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum) := hbd _ (rTrans_mem t (hmem _)) _ hK
    _ = _ := by ring

end GlobalTheory.Core.Mi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoxProductsOrthogonalSumTargetCartanFock
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

theorem frameLat_selfDual {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem box_sum_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∃ (sB : RealMat B) (LB : Lat B), (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧ IsSelfDualC B LB ∧ (∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA sB (o.boxT A Φ Φ')) ∧ ∀ (LA : Lat A) (Sf : Finset (FinPl D)) Φ Φ', IsSphOff ψ A W LA (frameLat W) Sf Φ → IsSphOff ψ A H LA (frameLat H) Sf Φ' → IsSphOff ψ A B LA LB Sf (o.boxT A Φ Φ') := by
  intro D ψ θ A B W H o sA sW sH hψ hθ hW hH
  refine ⟨sumMat o sW sH, sumLatO o (frameLat W) (frameLat H), GlobalTheory.T.isCartanInvolution_orthDecBlockSumRealMat D B W H o sW sH hW hH,
    GlobalTheory.T.orthDecSumLattice_selfDual D B W H o _ _ (frameLat_selfDual W) (frameLat_selfDual H),
    fun Φ Φ' h₁ h₂ => GlobalTheory.T.isPolynomialFockThetaVector_orthogonalBoxProduct D ψ θ A B W H o sA sW sH hψ hθ Φ Φ' h₁ h₂,
    fun LA Sf Φ Φ' h₁ h₂ => GlobalTheory.T.spherical_outside_box_product_orthDecSumLattice D ψ A B W H o LA _ _ Sf Φ Φ' h₁ h₂⟩

end GlobalTheory.Core.Rk.SumBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenRealDatumFiniteSumFockProductsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralEigen_realDatum_finite_sum_fockProducts : ∀ (D : D7), CenFock D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (χ' : GA D S → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k.om (a, 1) (fun u => C u v) = χ a • fun u => C u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k'.om (b, 1) (C u) = χ' b • C u) → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := by
  first | exact @GlobalTheory.SeeSaw.FinRank.biVac_sum_fock | exact GlobalTheory.SeeSaw.FinRank.biVac_sum_fock | (intros; apply GlobalTheory.SeeSaw.FinRank.biVac_sum_fock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEachStepSplitPlaceWithoutExcludedParams
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainNS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainNS

theorem chainNS_holds : ∀ D : D7, ChainNS D := by
  intro D c hc S' hS' B hB hBi k hk
  obtain ⟨p, hp, -, hpS, v, hv⟩ :=
    GlobalTheory.SplitChoice.exists_split_prime D (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) 1 (Finset.finite_toSet _) one_ne_zero
  have hvS : v ∉ S' := fun h => hpS v (Finset.mem_coe.2 h) hv
  refine ⟨v, hvS, GlobalTheory.SplitPlace.isSplit_of_splitsCompletely D p hp v hv, ?_⟩
  intro w hw β hβ k' hk'
  have hrt5 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt : D.R.r + 2 ≤ D.R.t := by omega
  have hwS : w ∉ GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    simp [GlobalTheory.LFun.above, hw, hvS]
  have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    have h := hv
    rw [← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
    exact h
  have hwc : w.under (𝓞 D.host.F) ∉ c.S := fun h => hvS (hw ▸ hS' h)
  set x := GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w with hx
  have hmem : x⁻¹ * β ∈ GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ w := by
    simp only [GlobalTheory.LFun.twist, Pi.inv_apply]
    exact Multiset.mem_map_of_mem _ hβ
  rw [chainPar_twist_chT] at hmem
  have key : ((x⁻¹ * β : ℂˣ) : ℂ) ≠ GlobalTheory.LFun.npow w ((k' : ℂ) / 2) := by
    have hN := GlobalTheory.T.small_entries_and_strings_avoid_excluded_norm_powers D.host.E w D.R.r D.R.t hrt k' hk'
    simp only [Pi.add_apply, Finset.sum_apply, Multiset.mem_add, Multiset.mem_sum] at hmem
    rcases hmem with h | ⟨i, hi, h⟩
    · simp only [GlobalTheory.LFun.twist, Pi.inv_apply] at h
      obtain ⟨b, hb, hb'⟩ := Multiset.mem_map.1 h
      rw [← hb']
      have hb1 := (hB w hwS).2 b hb
      have hb2 := (hBi w hwS).2 b⁻¹ (Multiset.mem_map_of_mem _ hb)
      have hu : ‖((GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) w : ℂˣ) : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
      refine hN.1 _ (Units.ne_zero _) ?_ ?_
      · rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul]
        exact hb1
      · rw [Units.val_mul, mul_inv, norm_mul, Units.val_inv_eq_inv_val, inv_inv, hu, one_mul]
        rw [Units.val_inv_eq_inv_val] at hb2
        exact hb2
    · have hi' := Finset.mem_Icc.1 hi
      exact hN.2 _ (GlobalTheory.LFun.norm_val _ _)
        (GlobalTheory.T.heckeCharQuotient_ne_one_completelySplitPrime D c hc i (k + 1) hi'.1 (by omega) (by omega) p hp w hpw hwc) _ h
  intro he
  apply key
  rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_comm]
  exact he

end GlobalTheory.ChainNS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwartStatement
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T : HSp D) (n : ℕ) (K : Subgroup (GA D T)), IsCompact (K : Set (GA D T)) → ∀ ν : Measure K, IsProbabilityMeasure ν → ∀ Φ ∈ schwartzA θ T.rank n, projS ν Φ ∈ schwartzA θ T.rank n := by
  first | exact @GlobalTheory.CompactAvgSchwartz.projS_mem | exact GlobalTheory.CompactAvgSchwartz.projS_mem | (intros; apply GlobalTheory.CompactAvgSchwartz.projS_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageThetaFamilySmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaAvgSmooth

open GlobalTheory.WeilVacMove

theorem key {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {n : ℕ} (L : (Fin n → ℝ) →+ WO S T)
    (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) (w : WO S T) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (t : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun t => f (w + L t)) t (Pi.single i 1) =
      dLine ψ S T (L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i)) f (w + L t) +
        -phase lam S T (L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i) 1) (w + L t) * f (w + L t) := by
  set M := L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i) with hMdef
  have hs : Continuous (AddMonoidHom.single (fun _ : Fin n => ℝ) i) := by
    refine continuous_pi fun j => ?_
    by_cases h : j = i
    · subst h; simp; exact continuous_id'
    · simpa [h] using continuous_const
  have hM : Continuous M := hL.comp hs
  have hM0 : ∀ s, (M s).map (finPart D) = 0 := fun s => hL0 _
  set x := w + L t with hx
  set c := phase lam S T (M 1) x with hc
  obtain ⟨hd, -⟩ := hasDerivAt_zero_and_isTheta hψ hM hM0 hf
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * c))) (-c) 0 := by
    have := ((HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const c).neg.cexp
    simpa using this
  have h1 := hexp.mul (hd x)
  have hsm : ∀ s : ℝ, s • (Pi.single i (1 : ℝ) : Fin n → ℝ) = Pi.single i s := by
    intro s
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have e1 : ∀ s : ℝ, Complex.exp (-((s : ℂ) * c)) * heisO ψ S T (M s) f x =
      f (w + L (t + s • Pi.single i 1)) := by
    intro s
    rw [heisO, psi_sympl_line hl hlam hM hM0, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
      one_mul, hsm, map_add, hx, add_assoc]
    rfl
  have hg : DifferentiableAt ℝ (fun t => f (w + L t)) (t + (0 : ℝ) • Pi.single i 1) :=
    ((hf.smooth n L hL hL0 w).differentiable (by simp)).differentiableAt
  have hl' : HasDerivAt (fun s : ℝ => t + s • (Pi.single i (1 : ℝ) : Fin n → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin n → ℝ)).const_add t
  have h2 := hg.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl'
  rw [zero_smul, add_zero] at h2
  have h3 : HasDerivAt (fun s : ℝ => f (w + L (t + s • Pi.single i 1)))
      (-c * heisO ψ S T (M 0) f x + Complex.exp (-(((0 : ℝ) : ℂ) * c)) * dLine ψ S T M f x) 0 := by
    have e : (fun s : ℝ => f (w + L (t + s • Pi.single i 1))) =
        fun s : ℝ => Complex.exp (-((s : ℂ) * c)) * heisO ψ S T (M s) f x := funext fun s => (e1 s).symm
    rw [e]
    exact h1
  have := h2.unique h3
  rw [this, map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
  ring

theorem avg_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Set (K → WO S T → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × WO S T => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, IsThetaFunO ψ S T (F k)) → (∀ F ∈ 𝒢, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => ∫ k, F k (w + L t) ∂μ := by
  intro D ψ hψ S T K _ _ _ _ μ _ 𝒢 hc hth hcl F hF n L hL hL0 w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hs : ∀ i, Continuous (AddMonoidHom.single (fun _ : Fin n => ℝ) i) := by
    intro i
    refine continuous_pi fun j => ?_
    by_cases h : j = i
    · subst h; simp; exact continuous_id'
    · simpa [h] using continuous_const
  let M : Fin n → ℝ →+ WO S T := fun i => L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i)
  have hM : ∀ i, Continuous (M i) := fun i => hL.comp (hs i)
  have hM0 : ∀ i s, (M i s).map (finPart D) = 0 := fun i s => hL0 _
  let φ : Fin n → (Fin n → ℝ) → ℂ := fun i t => -phase lam S T (M i 1) (w + L t)
  let 𝒢' : Set (K → (Fin n → ℝ) → ℂ) := {G | ∃ F ∈ 𝒢, G = fun k t => F k (w + L t)}
  have hφ : ∀ i, ContDiff ℝ ∞ (φ i) := by
    intro i
    have hc' : Continuous ((phase lam S T (M i 1)).comp L) :=
      hl.comp (continuous_symplOH S T hL continuous_const)
    have e : φ i = fun t => -(phase lam S T (M i 1) w + ((phase lam S T (M i 1)).comp L) t) := by
      funext t
      simp only [φ, map_add, AddMonoidHom.comp_apply]
    rw [e]
    exact (contDiff_const.add (contDiff_additive _ hc')).neg
  have hmem : (fun k t => F k (w + L t)) ∈ 𝒢' := ⟨F, hF, rfl⟩
  refine GlobalTheory.T.contDiff_compactAverage_of_closed_partials K μ n φ hφ 𝒢' ?_ ?_ ?_ _ hmem
  · rintro G ⟨F, hF, rfl⟩
    exact (hc F hF).comp (continuous_fst.prodMk (continuous_const.add (hL.comp continuous_snd)))
  · rintro G ⟨F, hF, rfl⟩ k
    exact ((hth F hF k).smooth n L hL hL0 w).differentiable (by simp)
  · rintro G ⟨F, hF, rfl⟩ i
    refine ⟨fun k t => GlobalTheory.WeilVacMove.dLine ψ S T (M i) (F k) (w + L t), ⟨_, hcl F hF (M i) (hM i) (hM0 i), rfl⟩,
      fun k t => ?_⟩
    exact GlobalTheory.ThetaAvgSmooth.key hψ hl hlam L hL hL0 w (F k) (hth F hF k) t i

end GlobalTheory.ThetaAvgSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombination_twoVariableModel_and_lineExtension : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''], (∀ (A S A' : HSp D) (FA : Frame k A.rank n') (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'') Λ c c' (Ξ₁ O₁ : SB (Matrix n n' k)) (Ξ₂ O₂ : SB (Matrix n'' n k)) (Ξ O : SB (Matrix n n' k × Matrix n'' n k)), p.IsBiModel ψ FA FS FA' Λ → p.IsCombAt ψ FA FS c Ξ₁.1 → p.IsCombAt ψ FS FA' c' Ξ₂.1 → IsOne O₁ → IsOne O₂ → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) → Λ Ξ = biComb ψ A S A' c c' (Λ O)) ∧ ∀ (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), IsStdChar D ψ (-1) → p.IsCoreFrame B s FA F₀ → (∀ T₀ c (Ξ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ F₀ FS T₀ → p.IsCombAt ψ FA FS c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toCols₁ * a fun r => x r (Sum.inr ())) → (∀ x, O.1 x = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ * a fun r => x r (Sum.inr ())) → T₀ Ψ = comb ψ B.V₀ S (c.mapDomain fun w => (B.o.resS S).symm (w, 0)) (T₀ O)) ∧ ∀ T₀ c (Ξ : Matrix n' n k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ FS F₀ T₀ → p.IsCombAt ψ FS FA c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toRows₁ * a (x (Sum.inr ()))) → (∀ x, O.1 x = Set.indicator {x : Matrix n' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toRows₁ * a (x (Sum.inr ()))) → T₀ Ψ = comb ψ S B.V₀ (c.mapDomain fun w => (B.o.resT S).symm (w, 0)) (T₀ O) := by
  first | exact @GlobalTheory.BiComb.comb_bimodel_and_line | exact GlobalTheory.BiComb.comb_bimodel_and_line | (intros; apply GlobalTheory.BiComb.comb_bimodel_and_line <;> assumption)
end

