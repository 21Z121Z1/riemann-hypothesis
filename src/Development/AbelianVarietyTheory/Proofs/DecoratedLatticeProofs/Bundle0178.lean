import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0344
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepRealThetaRuleOfNodesFarApart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.ChainParOfGap

theorem chainPar_of_nodeGap : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ k, ChainPar D k := by
  intro D h k
  unfold GlobalTheory.Chain.ChainPar
  intro τ
  obtain ⟨al, be, ga, de, hc, h1, h2⟩ := GlobalTheory.ArchRec.ParChain.parChain D k τ
  unfold GlobalTheory.ArchRec.Centred at hc
  unfold Formalism.MainNotions.SchurIrreducible.DataAR
  refine ⟨al, be, ga, de, ⟨hc.1, hc.2.2 h⟩, hc.2.1, ?_, ?_⟩
  · rw [h1]
    clear hc h1 h2 h
    congr 1
    unfold expT GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.alT
    rcases Nat.even_or_odd (k : ℕ) with hk | hk
    · have ho : Odd ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Odd (k : ℕ) := Nat.not_odd_iff_even.mpr hk
      have hne2 : ¬ Even ((k : ℕ) + 1) := Nat.not_even_iff_odd.mpr ho
      simp [ho, hk, hne, hne2] <;> ring
    · have ho : Even ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Even (k : ℕ) := Nat.not_even_iff_odd.mpr hk
      have hne2 : ¬ Odd ((k : ℕ) + 1) := Nat.not_odd_iff_even.mpr ho
      simp [ho, hk, hne, hne2] <;> ring
  · rw [h2]
    clear hc h1 h2 h
    congr 1
    unfold expS GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.alS
    rcases Nat.even_or_odd (k : ℕ) with hk | hk
    · have ho : Odd ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Odd (k : ℕ) := Nat.not_odd_iff_even.mpr hk
      have hne2 : ¬ Even ((k : ℕ) + 1) := Nat.not_even_iff_odd.mpr ho
      simp [ho, hk, hne, hne2] <;> ring
    · have ho : Even ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Even (k : ℕ) := Nat.not_even_iff_odd.mpr hk
      have hne2 : ¬ Odd ((k : ℕ) + 1) := Nat.not_odd_iff_even.mpr ho
      simp [ho, hk, hne, hne2] <;> ring

end GlobalTheory.Corev.ChainParOfGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepVectorExistsNonzeroVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepVecOK

theorem stepVec_exists_vac : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → (∃ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f) ∧ ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → IsThetaFunO c.ψ s.V s'.V f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO c.ψ s.V s'.V) c.θ τ (cplxO (cart s.M τ) (cart s'.M τ)) f) ∧ ∀ φ, IsThetaFunO c.ψ s.V s'.V (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f φ) := by
  classical
  intro D c hc k s s' hs hs'
  have hr : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + (k : ℕ) * D.R.t ≤ D.R.r + ((k : ℕ) + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  refine ⟨?_, fun ξ f₀ f h => ?_⟩
  · obtain ⟨f₀, hf₀⟩ := GlobalTheory.VacuumO.vacExists D c.ψ c.θ hc.std hc.inf s.V s'.V (cart s.M) (cart s'.M) hs.sigOK hs'.sigOK
      (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M) s.Λ s'.Λ hs.selfDual hs'.selfDual
    obtain ⟨_, ξL, hL⟩ := hs.lev
    have hsp : ∃ e : AE D, IsIdemSum e (s.L.Pg ∪ ∅) := by
      obtain ⟨e, he⟩ := hc.split
      refine ⟨e, ?_⟩
      rw [Finset.union_empty, hL]
      exact he
    obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.stepVecExists D c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L
      (c.chi ((k : ℕ) + 1)) ∅ 1 hs.selfDual hs'.selfDual hs.frame hs'.frame (Finset.disjoint_empty_right _) hsp f₀ hf₀
    exact ⟨1, f₀, f, hf⟩
  · obtain ⟨h1, h2, h3⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hs.selfDual hs'.selfDual hr h
    exact ⟨h1, h2, h3, fun φ => GlobalTheory.FockTheta.ptStable D c.ψ c.θ hc.std hc.inf s.V s'.V _ _ _ _ f φ h1⟩

end GlobalTheory.ChainOnto.StepVecOK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.StepExp

variable {D : D7}

theorem chrStep_exp' {c : Com D} (hc : c.Is) (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (c.chS ((k : ℕ) + 1)) τ (expS D k τ) ∧ HasInfExp D (c.chT ((k : ℕ) + 1)) τ (expT D k τ) := by
  have h1 : HasInfExp D (c.μ ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := hc.exp k τ
  have h2 : HasInfExp D c.η τ (1 / 2) := hc.chars.2.2.2.1 τ
  have h3 := GlobalTheory.Chain.StepVac.hasInfExp_mul h1 (GlobalTheory.Chain.StepVac.hasInfExp_inv h2)
  unfold Com.chS Com.chT Lift.chrStep expS expT
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, if_pos hk, if_pos hk, sub_zero, sub_eq_add_neg]
    exact ⟨h3, h1⟩
  · rw [if_neg (by rwa [Nat.odd_add_one, Nat.not_odd_iff_even]), if_neg hk, if_neg hk, sub_zero, sub_eq_add_neg]
    exact ⟨h1, h3⟩

theorem stepExpVac : ∀ D : D7, GlobalTheory.ChainOnto.ForStep D fun c k s s' p => ∀ hk : k < D.R.m,
    IsWeilExp c.ψ s.V s'.V (expS D ⟨k, hk⟩) (expT D ⟨k, hk⟩) p.ω ∧ IsVacVec c.ψ c.θ s.M s'.M p.f := by
  intro D _ c hc k _ s s' hs hs' p hp hk
  refine ⟨⟨c.chS (k + 1), c.chT (k + 1), hp.weil, fun τ => chrStep_exp' hc ⟨k, hk⟩ τ⟩, ?_⟩
  obtain ⟨ξ, f₀, hv⟩ := hp.vec
  have hr : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  obtain ⟨a, b, d⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hs.selfDual hs'.selfDual hr hv
  exact ⟨a, b, d⟩

end GlobalTheory.ChainOnto.StepExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsSumUniformLimitProductSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.DenseSum

theorem unifLimit_prodSpan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ f, IsThetaFunO ψ S T f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS T) (IsThetaFunO ψ A T) (IsThetaFunO ψ B T)) f := by
  intro D ψ hψ S A B T o f hf ε hε
  obtain ⟨n, P, g, hPc, hPl, hg, hfg⟩ := GlobalTheory.T.theta_function_orthogonal_sum_approx_finite_sums D ψ hψ S A B T o f hf (ε / 2) (by positivity)
  have hb : ∀ i, ∃ C : ℝ, ∀ v, ‖g i v‖ ≤ C := fun i =>
    GlobalTheory.IsoMean.isThetaFunO_bounded B T ψ hψ (g i) (hg i)
  choose C hC using hb
  set M : ℝ := 1 + ∑ i, |C i| with hMdef
  have hM : 0 < M := by
    have : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hδ : 0 < ε / (2 * M) := by positivity
  have hφ : ∀ i, ∃ φ : WO A T → ℂ, IsThetaFunO ψ A T φ ∧ ∀ u, ‖P i u - φ u‖ ≤ ε / (2 * M) := fun i =>
    GlobalTheory.T.theta_functions_dense_continuous_theta_law D ψ hψ A T (P i) (hPc i) (hPl i) _ hδ
  choose φ hφt hφa using hφ
  refine ⟨∑ i, fun w => φ i ((o.resS T) w).1 * g i ((o.resS T) w).2, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨φ i, g i, hφt i, hg i, rfl⟩
  · intro w
    have key : ‖∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2 -
        ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ ≤ ε / 2 := by
      rw [← Finset.sum_sub_distrib]
      calc _ ≤ ∑ i, ‖P i ((o.resS T) w).1 * g i ((o.resS T) w).2 - φ i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i, ε / (2 * M) * |C i| := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← sub_mul, norm_mul]
            exact mul_le_mul (hφa i _) ((hC i _).trans (le_abs_self _)) (norm_nonneg _) hδ.le
        _ = ε / (2 * M) * ∑ i, |C i| := by rw [Finset.mul_sum]
        _ ≤ ε / (2 * M) * M := by
            refine mul_le_mul_of_nonneg_left ?_ hδ.le
            rw [hMdef]; linarith
        _ = ε / 2 := by field_simp
    have hsum : (∑ i, fun w => φ i ((o.resS T) w).1 * g i ((o.resS T) w).2) w =
        ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2 := by
      simp [Finset.sum_apply]
    rw [hsum]
    calc ‖f w - ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2‖
        = ‖(f w - ∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2) +
          (∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2 - ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2)‖ := by
          congr 1; ring
      _ ≤ ε / 2 + ε / 2 := (norm_add_le _ _).trans (add_le_add (hfg w) key)
      _ = ε := by ring

end GlobalTheory.DenseSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.ThetaSwap

open GlobalTheory.Grow GlobalTheory.Size

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}

theorem thetaKO_left_fst (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ GQ S, ∀ g h, thetaKO om (γ * g) h f = thetaKO om g h f := fun γ hγ g h => by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

theorem thetaKO_le_quotHeight {θ : InfFam D} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    (hf : IsThetaFunO ψ S T f) :
    ∃ (K : ℝ) (A : ℕ), 0 ≤ K ∧ ∀ g h, ‖thetaKO om g h f‖ ≤ K * (quotHeight S g * quotHeight T h) ^ A := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne S T
  obtain ⟨C, hC0, hC⟩ := (H S T rfl rfl).real ψ hθ hU
  have hb := (hC χS χT om hω μ 𝓕 hμ f hl).2
  have hK : 0 ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * 4 ^ A := by positivity
  refine ⟨_, A, hK, fun g h => ?_⟩
  obtain ⟨γ, hγ, h1⟩ := exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := exists_height_le_two_mul_quotHeight T h
  rw [← thetaKO_left_fst hω hf γ hγ g h, ← GlobalTheory.Chain.LiftConv.thetaKO_left hω hf (γ * g) γ' hγ' h]
  refine (hb _ _).trans ?_
  have e : C * (sobO ψ θ μ 𝓕 d f).toReal * 4 ^ A * (quotHeight S g * quotHeight T h) ^ A =
      C * (sobO ψ θ μ 𝓕 d f).toReal * (2 * quotHeight S g * (2 * quotHeight T h)) ^ A := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos (height_pos S _) (height_pos T _)).le
    (mul_le_mul h1 h2 (height_pos T _).le (by linarith [quotHeight_pos S g])) A) (by positivity)

end GlobalTheory.ChainOnto.ThetaSwap

namespace GlobalTheory.ChainOnto.ThetaSwap

open GlobalTheory.Grow GlobalTheory.Size

theorem integrable_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D S)} {X : Set (GA D S)} {ν' : Measure (GA D T)}
    {X' : Set (GA D T)} (hν : ν.IsHaarMeasure) (hX : IsFundamentalDomain (GQ S) X ν) (hν' : ν'.IsHaarMeasure)
    (hX' : IsFundamentalDomain (GQ T) X' ν') {G : GA D S → ℂ} {F : GA D T → ℂ} (hG : RapidDec S G)
    (hF : RapidDec T F) :
    Integrable (Function.uncurry fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g))
      ((ν'.restrict X').prod (ν.restrict X)) := by
  obtain ⟨-, -, -, hS2, hSB⟩ := Formalism.IndefR.Eqv.ga_facts D S
  obtain ⟨-, -, -, hT2, hTB⟩ := Formalism.IndefR.Eqv.ga_facts D T
  have : IsFiniteMeasure (ν.restrict X) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol S ν X hν hX).ne
  have : IsFiniteMeasure (ν'.restrict X') :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol T ν' X' hν' hX').ne
  obtain ⟨K, A, hK, hb⟩ := thetaKO_le_quotHeight hθ hω hf
  obtain ⟨B, hB⟩ := hG.decay A
  obtain ⟨B', hB'⟩ := hF.decay A
  have hc : Continuous (Function.uncurry fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g)) := by
    have h1 : Continuous fun p : GA D T × GA D S => thetaKO om p.2 p.1 f :=
      (hω.om_cont f hf 0).comp (continuous_snd.prodMk continuous_fst)
    exact (h1.mul (hF.continuous.comp continuous_fst)).mul
      (Complex.continuous_conj.comp (hG.continuous.comp continuous_snd))
  refine Integrable.of_bound hc.aestronglyMeasurable (K * B * B') (.of_forall fun p => ?_)
  obtain ⟨h, g⟩ := p
  have hq := (pow_pos (quotHeight_pos S g) A).le
  have hq' := (pow_pos (quotHeight_pos T h) A).le
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) hq).trans (hB g)
  calc ‖Function.uncurry (fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g)) (h, g)‖
        = ‖thetaKO om g h f‖ * ‖F h‖ * ‖G g‖ := by simp [Function.uncurry, norm_mul]
    _ ≤ K * (quotHeight S g * quotHeight T h) ^ A * ‖F h‖ * ‖G g‖ := by gcongr; exact hb g h
    _ = K * (‖G g‖ * quotHeight S g ^ A) * (‖F h‖ * quotHeight T h ^ A) := by ring
    _ ≤ K * B * B' := by
        gcongr
        · exact hB g
        · exact hB' h

theorem integral_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ →
    IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ (ν : Measure (GA D S)) (X : Set (GA D S))
    (ν' : Measure (GA D T)) (X' : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) X ν →
    ν'.IsHaarMeasure → IsFundamentalDomain (GQ T) X' ν' → ∀ (G : GA D S → ℂ) (F : GA D T → ℂ),
    GlobalTheory.Grow.RapidDec S G → GlobalTheory.Grow.RapidDec T F →
    ∫ h in X', ∫ g in X, thetaKO om g h f * F h * conj (G g) ∂ν ∂ν' =
      ∫ g in X, ∫ h in X', thetaKO om g h f * F h * conj (G g) ∂ν' ∂ν := by
  intro D ψ θ S T χS χT om hθ hω f hf ν X ν' X' hν hX hν' hX' G F hG hF
  have : IsFiniteMeasure (ν.restrict X) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol S ν X hν hX).ne
  have : IsFiniteMeasure (ν'.restrict X') :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol T ν' X' hν' hX').ne
  exact integral_integral_swap (integrable_prod hθ hω hf hν hX hν' hX' hG hF)

end GlobalTheory.ChainOnto.ThetaSwap

example : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ (ν : Measure (GA D S)) (X : Set (GA D S)) (ν' : Measure (GA D T)) (X' : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) X ν → ν'.IsHaarMeasure → IsFundamentalDomain (GQ T) X' ν' → ∀ (G : GA D S → ℂ) (F : GA D T → ℂ), GlobalTheory.Grow.RapidDec S G → GlobalTheory.Grow.RapidDec T F → ∫ h in X', ∫ g in X, thetaKO om g h f * F h * conj (G g) ∂ν ∂ν' = ∫ g in X, ∫ h in X', thetaKO om g h f * F h * conj (G g) ∂ν' ∂ν :=
  GlobalTheory.ChainOnto.ThetaSwap.integral_swap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem pet_val_sum {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (y : s.CC c) (w : SmT s.M) (n : ℕ)
    (ys : Fin n → s.CC c) (ws : Fin n → SmT s.M) :
    s.pet (PiLocalization₂.val y w) (∑ i, PiLocalization₂.val (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i) := by
  have hs : ∀ i, s.pet (PiLocalization₂.val y w) (PiLocalization₂.val (ys i) (ws i)) = ip y (ys i) * ipD w (ws i) :=
    fun i => h.schur y (ys i) w (ws i)
  rw [← Finset.sum_congr rfl (fun i _ => hs i)]
  simp only [PiLocalization₂.pet, Lift.pet, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact integral_finset_sum _ (fun i _ => h.integ y (ys i) w (ws i))

theorem stepUp : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  intro D hFin hPV hSpan hAdj hPar hNe
  intro hgap c hc k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' u B hB hL
  have hk' : k + 1 ≤ D.R.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := hFin c hc (k + 1) hk' s' hs'
  obtain ⟨x, hx, -⟩ := GlobalTheory.T.hermitian_adjoint_exists_unique_of_posDef (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
  obtain ⟨φ, v, hv, hF⟩ := hNe hgap c hc k hk s s' hs hs' p hp u B hB hL
  have key := GlobalTheory.T.mem_range_adjoint_of_mem_span_evaluation_values (GA D s'.V) (SmT s'.M) (s'.CC c) (s'.CC c).subtype s'.KF ipD' ip' s'.pet
    hM'.hermD hM'.posD hM'.herm hM'.pos (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x
    (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v) (hSpan hgap c hc k hk s s' hs hs' p hp u φ v hv)
    (fun y w hw => by
      rw [hx y]
      exact (hAdj hgap c hc k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)) hF
  obtain ⟨-, w₀, -, hFx⟩ := key
  have hPF := hPar hgap c hc k hk s s' hs hs' p hp u B φ hB v hv hF
  refine ⟨x, hx, hPV c hc (k + 1) hk' s' hs' x w₀ _ ?_ ?_⟩
  · have : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
    rw [← this]; exact hF
  · have : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
    rw [← this]; exact hPF

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterInjectivePlacewise
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem chainPar_inj_at (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : chainPar c B k w = chainPar c B' k w) : B w = B' w := by
  induction k with
  | zero => simpa [chainPar] using h
  | succ k ih =>
    apply ih
    rw [chainPar_succ, chainPar_succ] at h
    simp only [stepPar] at h
    have h2 := add_right_cancel h
    exact Multiset.map_injective (mul_right_injective _) h2

theorem chainPar_inj : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)),
    chainPar c B k w = chainPar c B' k w → B w = B' w :=
  chainPar_inj_at

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := by
  intro w hw
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have h := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  exact (GlobalTheory.SmoothCyclic.sm_eq M τ).ge (h.2.2.1 w hw)

theorem tprod_eq_zero_of_kFin_off (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) (hΛ : SepCont M Λ)
    (h0 : ∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) (s : Finset D.what₂.Tau) :
    ∀ v : M.Vec, (∀ τ, τ ∉ s → IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)) → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  induction s using Finset.induction_on with
  | empty => exact fun v hv => h0 v fun τ => hv τ (Finset.notMem_empty τ)
  | insert a s ha ih =>
    intro v hv
    obtain ⟨ℓ, hℓ, hℓv⟩ := hΛ a v
    have hk : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M a, ℓ w = 0 := by
      intro w hw
      rw [hℓv ⟨w, kFin_le_sm hHC M a hw⟩]
      refine ih _ fun τ hτ => ?_
      by_cases e : τ = a
      · subst e
        rw [Function.update_self]
        exact hw
      · rw [Function.update_of_ne e]
        exact hv τ (by simp [e, hτ])
    have := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D V S M a ℓ hℓ hk (v a) (v a).2
    rw [hℓv (v a), Function.update_eq_self] at this
    exact this

theorem eq_zero_of_sepCont : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ), SepCont M Λ → (∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) → Λ = 0 := by
  intro hHC D V S M Λ hΛ h0
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
  exact tprod_eq_zero_of_kFin_off hHC M Λ hΛ h0 Finset.univ v fun τ hτ => absurd (Finset.mem_univ τ) hτ

example : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ), SepCont M Λ → (∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) → Λ = 0 := eq_zero_of_sepCont

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilConjugationAdjointRuleStandardChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilConjAdjoint

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid

variable {D : D7} {S T : HSp D}

theorem conjTarget_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjTarget om (g, negGA T h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjTarget] using this

theorem conjSource_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjSource om (negGA S g, h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjSource] using this

theorem conjAdjoint_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem conjAdjoint_holds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ S T : HSp D, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.ConjAdjoint ψ S T := by
  intro D ψ hψ S T
  obtain ⟨hθ, hH⟩ := GlobalTheory.T.thetaHeisenberg_conjugation_negHermitianSpace D ψ hψ S T
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T
  refine ⟨hθ, hH, fun χS χT om H => ?_, fun χS χT om H => ?_, d1, d2, d3, d4, fun χS χT om H => ?_⟩
  · have H1 := (GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces D ψ S T χS χT om H).1
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjTarget_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S (negSp T) _ _ om' _ H' H1 _ _ ((hθ f).1.2 hf)
  · have H1 := (GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces D ψ S T χS χT om H).2
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjSource_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ (negSp S) T _ _ om' _ H' H1 _ _ ((hθ f).2.2 hf)
  · have H1 := GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS χT om H
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjAdjoint_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ T S _ _ om' _ H' H1 _ _ ((d3 f).2 hf)

end GlobalTheory.WeilConjAdjoint
end

