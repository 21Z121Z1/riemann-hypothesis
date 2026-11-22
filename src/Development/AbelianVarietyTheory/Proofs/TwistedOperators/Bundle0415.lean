import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0321
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0408
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelParsevalThetaInnerProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixParseval

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem parseval : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → Continuous (fun u : Mx D W.rank r => ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') ∧ Integrable (fun u : Mx D W.rank r => ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') μ ∧ ∫ w in 𝓕₀, f₁ w * starRingEnd ℂ (f₂ w) ∂μ₀ = ∫ u : Mx D W.rank r, (∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μ₀ 𝓕₀ hμ₀ μ' 𝓕' hμ' f₁ f₂ hf₁ hf₂
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ, hμ'.2.2]; exact ENNReal.one_lt_top⟩
  let R : (WO V W → ℂ) → WO V' W → Mx D W.rank r → ℂ := fun f x u =>
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x
  let h : WO V' W → Mx D W.rank r → ℂ := fun x u => R f₁ x u * starRingEnd ℂ (R f₂ x u)
  obtain ⟨hc₁, M₁, hM₁⟩ := GlobalTheory.T.restrictedHeisenbergTheta_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₁ hf₁
  obtain ⟨hc₂, M₂, hM₂⟩ := GlobalTheory.T.restrictedHeisenbergTheta_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₂ hf₂
  have hhc : Continuous (Function.uncurry h) := hc₁.mul (Complex.continuous_conj.comp hc₂)
  have hhb : ∀ x u, ‖h x u‖ ≤ M₁ * M₂ := fun x u => by
    show ‖R f₁ x u * starRingEnd ℂ (R f₂ x u)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hM₁ x u) (hM₂ x u) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ x u))
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf₂
  have hYr : μ.real 𝓨 = 1 := by simp [Measure.real, hμ.2.2]
  have hsq : ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ Cf : ℝ, (∀ w, ‖f w‖ ≤ Cf) → ∀ x u,
      Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2) ∧
      ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 ≤ Cf ^ 2 := by
    intro f hf Cf hCf x u
    obtain ⟨hs1, hs2⟩ := GlobalTheory.T.parseval_mixedModel_isotropic_thetaProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f f hf hf x u
    have e : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
        ‖R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u))‖ = ‖R f x (ξ.map (incA D) + u)‖ ^ 2 :=
      fun ξ => by rw [norm_mul, Complex.norm_conj, sq]
    have hsum : Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2) :=
      hs1.congr e
    refine ⟨hsum, ?_⟩
    have e2 : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
        R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u)) =
          ((‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ) := fun ξ => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hI := hs2.tsum_eq
    have hI' : ((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ) =
        ∫ y in 𝓨, f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x +
          GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) * starRingEnd ℂ (f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y +
          GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u)) ∂μ := by
      rw [Complex.ofReal_tsum, ← hI]
      exact tsum_congr fun ξ => (e2 ξ).symm
    have hnn : 0 ≤ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 :=
      tsum_nonneg fun _ => by positivity
    have hb : ∀ w, ‖f w * starRingEnd ℂ (f w)‖ ≤ Cf ^ 2 := fun w => by
      rw [norm_mul, Complex.norm_conj, ← sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCf w) 2
    calc ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2
        = ‖((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ Cf ^ 2 * (μ.restrict 𝓨).real Set.univ := by
          rw [hI']
          exact norm_integral_le_of_norm_le_const (.of_forall fun y => hb _)
      _ = Cf ^ 2 := by simp [Measure.real, Measure.restrict_apply_univ, hμ.2.2]
  have hb : ∀ x u, Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧
      ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2 := by
    intro x u
    obtain ⟨s1, t1⟩ := hsq f₁ hf₁ C₁ hC₁ x u
    obtain ⟨s2, t2⟩ := hsq f₂ hf₂ C₂ hC₂ x u
    have hle : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤
        (‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2 + ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 := fun ξ => by
      show ‖R f₁ x (ξ.map (incA D) + u) * starRingEnd ℂ (R f₂ x (ξ.map (incA D) + u))‖ ≤ _
      rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖R f₁ x (ξ.map (incA D) + u)‖ - ‖R f₂ x (ξ.map (incA D) + u)‖)]
    have hs' := (s1.add s2).div_const 2
    refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs', ?_⟩
    calc ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖
        ≤ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
            (‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2 + ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs').tsum_le_tsum hle hs'
      _ = ((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2) +
            ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 := by
          rw [tsum_div_const, s1.tsum_add s2]
      _ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2 := by linarith
  obtain ⟨hint, hEq⟩ := GlobalTheory.T.integral_parametric_unfold_rationalTranslates D W.rank r (WO V' W) (μ'.restrict 𝓕') μ 𝓨 hμ h hhc _ hb
  have a1 : ∀ x, Continuous (h x) := fun x => hhc.uncurry_left x
  have a2 : ∀ u, Continuous (fun x => h x u) := fun u => hhc.uncurry_right u
  have a3 : ∀ u, AEStronglyMeasurable (fun x => h x u) (μ'.restrict 𝓕') := fun u => (a2 u).aestronglyMeasurable
  haveI : FirstCountableTopology (Mx D W.rank r) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hG : Continuous (fun u => ∫ x, h x u ∂(μ'.restrict 𝓕')) :=
    continuous_of_dominated (bound := fun _ => M₁ * M₂) a3
      (fun u => .of_forall fun x => hhb x u) (integrable_const _) (.of_forall a1)
  refine ⟨hG, hint, ?_⟩
  show _ = ∫ u, (∫ x, h x u ∂(μ'.restrict 𝓕')) ∂μ
  rw [hEq]
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated D V V' W r C B hs C' h1 h2 h3 μ 𝓨 hμ
    μ₀ 𝓕₀ hμ₀.1 hμ₀.2.1 μ' 𝓕' hμ'.1 hμ'.2.1
  have hκ1 : κ = 1 := by
    have e := hκ (fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩ (fun _ _ _ => rfl)
    simp only [setIntegral_const, Measure.real, hμ₀.2.2, hμ.2.2, hμ'.2.2, ENNReal.toReal_one, one_smul] at e
    rw [Complex.real_smul, mul_one] at e
    exact_mod_cast e.symm
  let H : WO V W → ℂ := fun w => f₁ w * starRingEnd ℂ (f₂ w)
  have hHc : Continuous H := hf₁.cont.mul (Complex.continuous_conj.comp hf₂.cont)
  have hHb : ∃ b : ℝ, ∀ w, ‖H w‖ ≤ b := ⟨C₁ * C₂, fun w => by
    show ‖f₁ w * starRingEnd ℂ (f₂ w)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC₁ w) (hC₂ w) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ w))⟩
  have hHp : ∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w := by
    rintro γ ⟨g, rfl⟩ w
    show f₁ (ratW W V g + w) * starRingEnd ℂ (f₂ (ratW W V g + w)) = f₁ w * starRingEnd ℂ (f₂ w)
    rw [hf₁.quasi g w, hf₂.quasi g w, map_mul]
    have hu : ∀ a, ψ a * starRingEnd ℂ (ψ a) = 1 := fun a => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1]; norm_num
    calc ψ (-symplOH V W (ratW W V g) w) * f₁ w * (starRingEnd ℂ (ψ (-symplOH V W (ratW W V g) w)) * starRingEnd ℂ (f₂ w))
        = (ψ (-symplOH V W (ratW W V g) w) * starRingEnd ℂ (ψ (-symplOH V W (ratW W V g) w))) *
            (f₁ w * starRingEnd ℂ (f₂ w)) := by ring
      _ = _ := by rw [hu, one_mul]
  show ∫ w in 𝓕₀, H w ∂μ₀ = _
  rw [hκ H hHc hHb hHp, hκ1, one_smul]
  refine integral_congr_ae (.of_forall fun t => ?_)
  have hInt : Integrable (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t +
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x)) ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) := by
    obtain ⟨b, hb'⟩ := hHb
    have hcont : Continuous (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t +
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x)) :=
      hHc.comp ((continuous_const.add ((continuous_fst).matrix_mul continuous_const)).add
        ((continuous_snd).matrix_mul continuous_const))
    exact Integrable.of_bound hcont.aestronglyMeasurable b (.of_forall fun p => hb' _)
  show ∫ y, ∫ x, H _ ∂(μ'.restrict 𝓕') ∂(μ.restrict 𝓨) = _
  haveI : SFinite (μ'.restrict 𝓕') := instSFiniteOfSigmaFinite
  haveI : SFinite (μ.restrict 𝓨) := instSFiniteOfSigmaFinite
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (.of_forall fun x => ?_)
  have hp := (GlobalTheory.T.parseval_mixedModel_isotropic_thetaProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f₁ f₂ hf₁ hf₂ x t).2
  refine Eq.trans ?_ hp.tsum_eq.symm
  refine integral_congr_ae (.of_forall fun y => ?_)
  show H _ = H _
  congr 1
  abel

end GlobalTheory.MixParseval

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicAndConstantTerm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.parabolic_and_constant_term

section Star

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem starFn_tensor (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ) :
    starFn (tensor σ J fa ff) = tensor σ J (fun w => starFn (fa w)) (fun v => starFn (ff v)) := by
  funext g
  simp only [starFn, tensor, map_mul, map_prod, map_inv]
  congr 1
  exact MonoidHom.map_finprod_of_injective (starRingEnd ℂ).toMonoidHom (starRingEnd ℂ).injective _

theorem starFn_unitLoc (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) :
    starFn (unitLoc σ J L v) = unitLoc σ J L v := by
  funext g
  by_cases hg : g ∈ stabLoc σ J L v
  · simp [starFn, unitLoc, hg, Set.indicator_of_mem, inv_mem hg]
  · have : g⁻¹ ∉ stabLoc σ J L v := fun h => hg (by simpa using inv_mem h)
    simp [starFn, unitLoc, hg, this]

theorem isFinFamily_starFn {L : Submodule (𝓞 E) (Fin n → E)} {ff : ∀ v, GLoc σ J v → ℂ}
    (h : IsFinFamily σ J L ff) : IsFinFamily σ J L (fun v => starFn (ff v)) :=
  ⟨fun v => starFn_mem_SB (h.1 v), h.2.mono fun v hv => by simp only [hv, starFn_unitLoc]⟩

end Star

theorem inConjParabolic_mono {k : Type} [Field k] {r : ℕ} {H H' : Subgroup (GL (Fin r) k)} (h : H ≤ H') {a : ℕ}
    (h' : InConjParabolic H' a) : InConjParabolic H a :=
  let ⟨g, hg⟩ := h'; ⟨g, fun p hp => hg p (h hp)⟩

theorem parabolicAtSplitPlaces : ParabolicAtSplitPlaces := by
  intro D V hodd T 𝔉 hP
  let i : Fin (𝔉.k + 1) := ⟨1, Nat.succ_lt_succ hP⟩
  have hi : i ≠ 0 := Fin.ne_of_val_ne one_ne_zero
  have hW := 𝔉.isIsotropic hi
  obtain ⟨h0, h2⟩ := GlobalTheory.T.totallyIsotropic_dim_bounds_oddRank D V hodd _ hW
  refine ⟨_, h0, h2, fun v => ?_⟩
  have hle : parAt 𝔉 (T.frame v) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v.1) (𝔉.X i)).map
      ((T.frame v).equiv : GLoc D.sp.cm.sig V.gram v.1 →* GL (Fin V.rank) (Fv D.host.F v.1)) :=
    Subgroup.map_mono (𝔉.par_le_parab _ _ i)
  obtain ⟨h3, h4⟩ := GlobalTheory.T.isotropicStabilizer_splitPlace_inConjParabolics D V v.1 (T.frame v) _ hW
  exact ⟨inConjParabolic_mono hle h3, inConjParabolic_mono hle h4⟩

theorem testFnConstTermVanish : TestFnConstTermVanish := by
  intro D V hodd S M T hH U μa _ μf _ f hf 𝔉 hP
  obtain ⟨a, ha0, ha2, hpar⟩ := parabolicAtSplitPlaces D V hodd T 𝔉 hP
  obtain ⟨v, hv⟩ := hH a ha0 (by omega)
  obtain ⟨fa, ff, hfa, hff, rfl⟩ := hf
  obtain ⟨h, hh, e⟩ := hff.2.1 v
  have hA : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hfa.mem
  have hF := hff.isFinFamily
  have he := (T.frame v).idem_mem (μf v.1) (T.τ v)
  constructor
  · refine GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local D V 𝔉 fa ff hA hF v.1 fun ν _ x y => ?_
    exact (GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB he hh) (ff v.1) (Or.inr e)
      ν x y).2
  · rw [starFn_tensor]
    refine GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local D V 𝔉 _ _ (fun w => starFn_mem_ccArch (hA w)) (isFinFamily_starFn hF) v.1 fun ν _ x y => ?_
    have e' : starFn (ff v.1) = GlobalTheory.AutomorphicL2Unitary.conv (μf v.1) ((T.frame v).idem (μf v.1) (T.τ v))
        (GlobalTheory.AutomorphicL2Unitary.conv (μf v.1) (starFn h) ((T.frame v).idem (μf v.1) (T.τ v))) := by
      rw [e, starFn_conv, starFn_conv]
      simp only [TypeData.idem, SplitAt.starFn_idem]
    exact (GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB (starFn_mem_SB hh) he) _
      (Or.inl e') ν x y).2

theorem parabolicAndConstTerm : ParabolicAndConstTerm := ⟨parabolicAtSplitPlaces, testFnConstTermVanish⟩

end GlobalTheory.Proof.parabolic_and_constant_term

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGLStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicProduct_hasFiniteLength_GL : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), HasFiniteLength π₁ → HasFiniteLength π₂ → IsSmooth π₁ → IsSmooth π₂ → HasFiniteLength (prod₂ π₁ π₂) := by
  first | exact @GlobalTheory.ProdLength.prod₂_hasFiniteLength | exact GlobalTheory.ProdLength.prod₂_hasFiniteLength | (intros; apply GlobalTheory.ProdLength.prod₂_hasFiniteLength <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumOverRationalHomThetaLawZeroCoreStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSumOverRationalHom_thetaLaw_zeroCore : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), poinX ψ d T β (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * poinX ψ d T β w := by
  first | exact @GlobalTheory.BumpMixQuasi.poinX_quasi | exact GlobalTheory.BumpMixQuasi.poinX_quasi | (intros; apply GlobalTheory.BumpMixQuasi.poinX_quasi <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudoCoefficientUnitaryPqStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudo_coefficient_unitary_pq : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.CharacterRegularityFiniteLength → GlobalTheory.Published.PseudoCoefficientExistence → GlobalTheory.Published.CuspidalOrbitalIntegrals → GlobalTheory.Published.PseudoCoefficientUpq := by
  first | exact @GlobalTheory.Published.pseudoCoefficientUpq_of_hypotheses | exact GlobalTheory.Published.pseudoCoefficientUpq_of_hypotheses | (intros; apply GlobalTheory.Published.pseudoCoefficientUpq_of_hypotheses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorInnerProductEqFinprodLocalInnerProduct
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor.PureScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  rw [wAt_eq_smul, smul_zero]

theorem wAt_neg_wAt_self {m n : ℕ} (q : Place D) (w : Mx D m n) : wAt q (-(wAt q w)) = -(wAt q w) := by
  have hq : idem D q * idem D q = idem D q := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 q
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hq]

theorem wAt_neg_wAt_ne {m n : ℕ} {p q : Place D} (hpq : p ≠ q) (w : Mx D m n) : wAt p (-(wAt q w)) = 0 := by
  have hpq' : idem D p * idem D q = 0 := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q hpq
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hpq', zero_smul, neg_zero]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem ip_base (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) : ipO μ 𝓕 f₀ f₀ = 1 := by
  have hself : ipO μ 𝓕 f₀ f₀ = (nrm2 μ 𝓕 f₀ : ℂ) :=
    (GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f₀ f₀ (base_theta hb) (base_theta hb)).2.2.2.2.1
  rw [hself, restrictedTensorBasePoint_norm_sq hb hμ, Complex.ofReal_one]

theorem finite_mulSupport_ip (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {x₁ x₂ : Place D → WO S T → ℂ} (h₁ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₁)
    (h₂ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₂) :
    (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite := by

  refine (h₁.2.union h₂.2).subset fun p hp => ?_
  rw [Function.mem_mulSupport] at hp
  by_contra hout
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hout
  exact hp (by rw [hout.1, hout.2]; exact ip_base hb hμ)

private theorem heisO_zero_twisted_operators (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext u
  simp [heisO, symplOH, symplO, hO]

theorem pureTensor_innerProduct_eq_finprod_local_of_finset (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (s : Finset (Place D)) :
    ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), (∀ p, p ∉ s → x₁ p = f₀) →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ →
      ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  classical
  have hθ₀ : IsThetaFunO ψ S T f₀ := base_theta hb

  have hsymm : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) :=
    fun f g hf hg => (GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.1
  have hadj : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ w,
      ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g) :=
    fun f g hf hg w => ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.2.2.2.2.2.1 w).2
  induction s using Finset.induction_on with
  | empty =>

    intro x₁ x₂ f₁ f₂ hx h₁ h₂
    have hx₁ : x₁ = fun _ => f₀ := funext fun p => hx p (by simp)
    subst hx₁
    have hf₁ : f₁ = f₀ :=
      (GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique h₁
        (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ).1
    subst hf₁
    obtain ⟨hfin, hprod⟩ := h₂.2.2 0
    simp only [wAt_zero, heisO_zero_twisted_operators] at hfin hprod
    rw [hsymm f₂ f₁ h₂.2.1 hθ₀, hprod, map_finprod _ hfin]
    exact finprod_congr fun p => (hsymm (x₂ p) f₁ (h₂.1.1 p).1 hθ₀).symm
  | insert q s hq ih =>
    intro x₁ x₂ f₁ f₂ hx h₁ h₂

    have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update x₁ q f₀) := by
      refine ⟨fun p => ?_, h₁.1.2.subset fun p hp => ?_⟩
      · by_cases hpq : p = q
        · subst hpq
          rw [Function.update_self]
          exact base_isLocal hb p
        · rw [Function.update_of_ne hpq]
          exact h₁.1.1 p
      · by_cases hpq : p = q
        · subst hpq
          simp at hp
        · simpa [Function.update_of_ne hpq] using hp
    have hoff : ∀ p, p ∉ s → Function.update x₁ q f₀ p = f₀ := by
      intro p hp
      by_cases hpq : p = q
      · subst hpq
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hpq]
        exact hx p (by simp [hpq, hp])
    obtain ⟨g₁, hg₁, -⟩ := GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ hres

    obtain ⟨f', hf', hc⟩ := GlobalTheory.T.pureTensor_update_factor_from_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ (Function.update x₁ q f₀) x₁ g₁ q hg₁
      (Function.update_self _ _ _) (fun p hp => (Function.update_of_ne hp _ _).symm) (h₁.1.1 q)
    have hf'₁ : f' = f₁ := (GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique hf' h₁
    subst hf'₁
    have hθq : IsThetaFunO ψ S T (x₂ q) := (h₂.1.1 q).1
    have key := hc f₂ (x₂ q) (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x₁ p) (x₂ p)) h₂.2.1 hθq (fun w => by
      rw [hadj g₁ f₂ hg₁.2.1 h₂.2.1]
      have hpw := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₂ f₂ h₂ (-(wAt q w))
      rw [ih _ _ _ _ hoff hg₁ hpw, ← mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ hres hpw.1),
        Function.update_self, wAt_neg_wAt_self, ← hadj f₀ (x₂ q) hθ₀ hθq, mul_comm]
      congr 1
      refine finprod_congr fun p => finprod_congr fun hp => ?_
      rw [Function.update_of_ne hp, wAt_neg_wAt_ne hp, heisO_zero_twisted_operators])
    rw [key, mul_comm]
    exact mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ h₁.1 h₂.1)

end

theorem ip_pure_eq_finprod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite ∧ ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₁ x₂ f₁ f₂ h₁ h₂
  refine ⟨finite_mulSupport_ip hb hμ h₁.1 h₂.1, ?_⟩

  exact pureTensor_innerProduct_eq_finprod_local_of_finset hb hμ h₁.1.2.toFinset x₁ x₂ f₁ f₂
    (fun p hp => by simpa [Set.Finite.mem_toFinset] using hp) h₁ h₂

end GlobalTheory.PlaceTensor.PureScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalClassTermEqVolumeMulProdOrbitalIntegralsStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalClassTerm_eq_volume_mul_prod_orbitalIntegrals : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) (qa : ∀ w : InfinitePlace F, XSet P w.Completion J), (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v).1) → (∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w).1) → Integrable (descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * ((∏ᶠ v, orbCls (μf v) (dtf v) (ff v) (qf v)) * ∏ w, orbCls (μa w) (dta w) (fa w) (qa w)) := by
  first | exact @GlobalTheory.TrClassTerm.class_term | exact GlobalTheory.TrClassTerm.class_term | (intros; apply GlobalTheory.TrClassTerm.class_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalTranslateSumBoundedRapidDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalTranslateSum_bounded_rapidDecay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (c : WO S T → ℂ), (∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, c w ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T, ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) → ∃ C : ℝ, ∀ w : WO S T, Summable (fun γ : ratL T S => ‖c ((γ : WO S T) + w)‖) ∧ ∑' γ : ratL T S, ‖c ((γ : WO S T) + w)‖ ≤ C := by
  first | exact @GlobalTheory.LatticeTranslateSum.sum_translates_bounded | exact GlobalTheory.LatticeTranslateSum.sum_translates_bounded | (intros; apply GlobalTheory.LatticeTranslateSum.sum_translates_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointPreservesHeckeEigenvectorsMatcheStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftAdjoint_preserves_heckeEigenvectors_matchedPair : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (cX c0 : List ℤ →₀ ℂ), GlobalTheory.Hk3.MatchE R t P cX c0 → ∀ (x : R.HE.H) (l : ℂ), h P c0 x = l • x → h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
  first | exact @GlobalTheory.Hk3.SysE.matched_keeps_eigen | exact GlobalTheory.Hk3.SysE.matched_keeps_eigen | (intros; apply GlobalTheory.Hk3.SysE.matched_keeps_eigen <;> assumption)
end

