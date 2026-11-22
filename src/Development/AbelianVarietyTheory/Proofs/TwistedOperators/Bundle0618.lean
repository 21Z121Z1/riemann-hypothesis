import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0482
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0360
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepPointMulPeriodUnipotentGLMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralLeOfTsum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FlatSup

theorem lintegral_le_of_tsum {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [ν.IsMulLeftInvariant] {𝓤 : Set G} (h : IsFundamentalDomain Γ 𝓤 ν)
    (h1 : ν 𝓤 = 1) (f : G → ENNReal) (hf : Measurable f) (B : ENNReal) (hB : ∀ u, ∑' γ : Γ, f (γ.1 * u) ≤ B) :
    ∫⁻ u, f u ∂ν ≤ B := by
  rw [h.lintegral_eq_tsum'' f, ← lintegral_tsum]
  · calc _ ≤ ∫⁻ _ in 𝓤, B ∂ν := lintegral_mono fun u => hB u
      _ = B := by rw [setLIntegral_const, h1, mul_one]
  · exact fun γ => (hf.comp (measurable_const_mul γ.1)).aemeasurable

theorem rat_cancel {D : D7} {m ρ : ℕ} {x : Matrix (Fin m) (Fin ρ) D.host.E} (hx : LinearIndependent D.host.E x.transpose)
    {a b : Mx D ρ ρ} (ha : a ∈ ratMx D ρ ρ) (hb : b ∈ ratMx D ρ ρ)
    (h : (rat x : Mx D m ρ) ⬝ a = (rat x : Mx D m ρ) ⬝ b) : a = b := by
  obtain ⟨a, rfl⟩ := mem_ratMx.1 ha
  obtain ⟨b, rfl⟩ := mem_ratMx.1 hb
  rw [← rat_mul, ← rat_mul] at h
  have h2 := rat_injective h
  have hi : Function.Injective x.mulVec := Matrix.mulVec_injective_iff.2 hx
  refine congrArg rat (Matrix.ext fun i j => ?_)
  have h3 : x *ᵥ (fun k => a k j) = x *ᵥ (fun k => b k j) := by
    funext l
    exact congrFun (congrFun h2 l) j
  exact congrFun (hi h3) i

theorem uni_bound (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (s : Step ψ V V₀ W W₀ ρ σ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : LinearIndependent D.host.E x.transpose)
    (Φ : WO V W → ℂ) (hΦ : IsThetaFunO ψ V W Φ) : ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ g h (w : WO V₀ W),
      ∫⁻ u : UX D ρ, ‖dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1) w‖ₑ ∂s.vU.ν ≤
        ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.mixedCoordinate_absSum_weilTranslate_moderateGrowth D ψ V W s.χV s.χW s.om s.weil V₀ ρ dV s.vS Φ hΦ
  obtain ⟨om', hW'⟩ := (GlobalTheory.T.weilDatum_descends_to_wittCore D ψ V W s.χV s.χW s.om s.weil).1 V₀ ρ dV
  have hMS := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ V V₀ W ρ dV s.χV s.χW s.om om' s.weil hW' s.vS.μ s.vS.𝓕 s.vS.covol
  have hmix := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ V V₀ W W₀ ρ σ dV dW s.vS s.vT s.χV s.χW s.om s.weil Φ hΦ).1
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.UnitU.cocompact D ρ
  obtain ⟨c, hc⟩ := exists_height_le_of_isCompact V (hK.image (dV.continuous_levi.comp continuous_subtype_val))
  have hc'1 : 1 ≤ max c 1 := le_max_right _ _
  have hC₀0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0 * max c 1 ^ A, A, mul_nonneg hC₀0 (pow_nonneg (zero_le_one.trans hc'1) _), fun g h w => ?_⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : Countable (UXQ D ρ) := (GlobalTheory.UnitU.rational D ρ).1
  obtain ⟨hH, 𝓤, h𝓤, h1⟩ := s.vU.unit
  have hval : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hxu : Continuous fun u : UX D ρ => (rat x : Mx D W.rank ρ) ⬝ u.1.1 := continuous_const.matrix_mul hval
  refine lintegral_le_of_tsum (UXQ D ρ) s.vU.ν h𝓤 h1 _ ?_ _ fun u => ?_
  · have hf : Continuous fun u : UX D ρ => (((g, h), ((rat x : Mx D W.rank ρ) ⬝ u.1.1, w)) :
        (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) := continuous_const.prodMk (hxu.prodMk continuous_const)
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2.enorm.measurable
  · obtain ⟨γ₀, hγ₀, k, hk, rfl⟩ := hcov u
    have hp : ((dV.levi k.1 * g, h) : GA D V × GA D W) = (dV.levi k.1, 1) * (g, h) := by simp
    have hom : s.om (dV.levi k.1 * g, h) Φ = s.om (dV.levi k.1, 1) (s.om (g, h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    let φ : UXQ D ρ → ratMx D W.rank ρ := fun γ =>
      ⟨(rat x : Mx D W.rank ρ) ⬝ (γ.1 * γ₀).1.1, ratMx_mul (rat_mem x) (mul_mem γ.2 hγ₀).1⟩
    have hφ : Function.Injective φ := fun a b hab => by
      have h3 := rat_cancel hx (mul_mem a.2 hγ₀).1 (mul_mem b.2 hγ₀).1 (congrArg Subtype.val hab)
      exact Subtype.ext (mul_right_cancel (Subtype.ext (Units.ext h3)))
    have key : ∀ γ : UXQ D ρ, dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ (γ.1 * (γ₀ * k)).1.1) =
        dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (dV.levi k.1 * g, h) Φ) (φ γ) := by
      intro γ
      rw [hom, GlobalTheory.Unf.TermLaw.mixS_levi_uni dV (hMS _ (s.weil.om_pres _ _ hΦ)) k.2, ← mul_assoc]
      congr 1
      exact (Matrix.mul_assoc _ _ _).symm
    simp only [key]
    refine (ENNReal.tsum_comp_le_tsum_of_injective hφ
      (fun y : ratMx D W.rank ρ => ‖dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (dV.levi k.1 * g, h) Φ) y w‖ₑ)).trans
      ((hC _ h w).trans (ENNReal.ofReal_le_ofReal ?_))
    have hk' : height V (dV.levi k.1) ≤ max c 1 := (hc _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
    have hkg : height V (dV.levi k.1 * g) ≤ max c 1 * height V g :=
      (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right hk' (height_pos V g).le)
    have hx0 : 0 ≤ height V (dV.levi k.1 * g) * height W h := mul_nonneg (height_pos V _).le (height_pos W h).le
    have hx1 : height V (dV.levi k.1 * g) * height W h ≤ max c 1 * (height V g * height W h) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkg (height_pos W h).le
    calc C * (height V (dV.levi k.1 * g) * height W h) ^ A ≤ max C 0 * (height V (dV.levi k.1 * g) * height W h) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx0 _)
      _ ≤ max C 0 * (max c 1 * (height V g * height W h)) ^ A :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 _) hC₀0
      _ = _ := by rw [mul_pow, mul_assoc]

theorem sfinite_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (ν : Measure G) [ν.IsHaarMeasure] : SFinite ν := inferInstance

theorem sfinite_fin {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν] : SFinite ν := inferInstance

theorem flat_sup_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h y w, ‖flatS dV dW s (rat x) y (s.om (g, h) Φ) w‖ ≤ C * (height V g * height W h) ^ A := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x hx Φ hΦ
  obtain ⟨C, A, hC0, hC⟩ := uni_bound D ψ V V₀ W W₀ ρ σ dV dW s x hx Φ hΦ
  refine ⟨C, A, fun g h y w => ?_⟩
  have hn : ∀ a, ‖ψ a‖ = 1 := s.weil.std.1.2.1
  have hne : ∀ a, ‖ψ a‖ₑ = 1 := fun a => by rw [← ofReal_norm, hn, ENNReal.ofReal_one]
  have hmix := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ V V₀ W W₀ ρ σ dV dW s.vS s.vT s.χV s.χW s.om s.weil Φ hΦ).1
  have hT := s.vT.covol
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  obtain ⟨j1, j2, j3, j4, -⟩ := lattice_Mx D σ V₀.rank
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D σ V₀.rank) := ⟨rfl⟩
  haveI := s.vU.unit.1
  haveI : IsFiniteMeasure (s.vT.μ.restrict s.vT.𝓕) := ⟨by rw [Measure.restrict_apply_univ, hT.2.2]; exact ENNReal.one_lt_top⟩
  haveI := sfinite_haar s.vU.ν
  haveI := sfinite_fin (s.vT.μ.restrict s.vT.𝓕)
  let F : UX D ρ → Mx D σ V₀.rank → ENNReal := fun u ξ =>
    ‖dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1) (dW.incX V₀ ξ + dW.incAdj V₀ y + dW.inc0 V₀ w)‖ₑ
  have hval : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hxu : Continuous fun u : UX D ρ => (rat x : Mx D W.rank ρ) ⬝ u.1.1 := continuous_const.matrix_mul hval
  have hX : Continuous (dW.incX V₀) := continuous_const.matrix_mul continuous_id
  have hFm : Measurable (Function.uncurry F) := by
    have hf : Continuous fun p : UX D ρ × Mx D σ V₀.rank => (((g, h), ((rat x : Mx D W.rank ρ) ⬝ p.1.1.1,
        dW.incX V₀ p.2 + dW.incAdj V₀ y + dW.inc0 V₀ w)) : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk
        (((hX.comp continuous_snd).add continuous_const).add continuous_const))
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2.enorm.measurable
  have h1 : ∀ u : UX D ρ, ‖flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (rat x) y (s.om (g, h) Φ) w u‖ₑ ≤
      ∫⁻ ξ in s.vT.𝓕, F u ξ ∂s.vT.μ := by
    intro u
    unfold flatFun evalAt
    have e1 : ‖star (psiUni ψ u.1)‖ₑ = 1 := by
      rw [← ofReal_norm, norm_star, show ‖psiUni ψ u.1‖ = 1 from hn _, ENNReal.ofReal_one]
    rw [enorm_mul, e1, one_mul]
    unfold GlobalTheory.MixModel.HypDec.mixT
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun ξ => le_of_eq ?_)
    simp only [F]
    rw [dW.integrandT_eq, enorm_mul, hne, one_mul]
  have h2 : ‖flatS dV dW s (rat x) y (s.om (g, h) Φ) w‖ₑ ≤ ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
    unfold flatS flatAt
    refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono h1).trans ?_)
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    calc _ ≤ ∫⁻ _ in s.vT.𝓕, ENNReal.ofReal (C * (height V g * height W h) ^ A) ∂s.vT.μ :=
          lintegral_mono fun ξ => hC g h _
      _ = _ := by rw [setLIntegral_const, hT.2.2, mul_one]
  rw [← ofReal_norm] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 (pow_nonneg
    (mul_nonneg (height_pos V g).le (height_pos W h).le) _))).1 h2

end GlobalTheory.FlatSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemISupJointEigenspacesInfOfStableSubmodule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem mem_iSup_jointEigen_inf_of_stable : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (G P : Submodule ℂ E) (C : Finset (ι → ℂ)),
    (∀ i, ∀ x ∈ G, F i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x) → P ≤ G → (∀ i, ∀ x ∈ P, F i x ∈ P) →
    (∀ x ∈ G, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h}) →
    ∀ x ∈ P, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F G P C hFG hadd hsmul hPG hFP hdec
  have hF0 : ∀ i, F i 0 = 0 := by
    intro i
    have := hsmul i 0 0 G.zero_mem
    simpa using this
  obtain ⟨V, hV⟩ : ∃ V : (ι → ℂ) → Submodule ℂ E,
      ∀ c x, x ∈ V c ↔ (x ∈ G ∧ ∀ i, F i x = c i • x) :=
    ⟨fun c =>
      { carrier := {h | h ∈ G ∧ ∀ i, F i h = c i • h}
        add_mem' := by
          rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
          refine ⟨G.add_mem hx hy, fun i => ?_⟩
          rw [hadd i x hx y hy, hx' i, hy' i, smul_add]
        zero_mem' := ⟨G.zero_mem, fun i => by rw [hF0 i, smul_zero]⟩
        smul_mem' := by
          rintro a x ⟨hx, hx'⟩
          refine ⟨G.smul_mem a hx, fun i => ?_⟩
          rw [hsmul i a x hx, hx' i]
          exact smul_comm _ _ _ }, fun c x => Iff.rfl⟩
  have hVG : ∀ c, V c ≤ G := fun c x hx => ((hV c x).1 hx).1
  have hSG : ∀ s : Finset (ι → ℂ), (⨆ c ∈ s, V c) ≤ G := fun s => iSup₂_le fun c _ => hVG c
  have hmemS : ∀ (s : Finset (ι → ℂ)) c, c ∈ s → V c ≤ ⨆ c ∈ s, V c := fun s c hc =>
    le_iSup₂_of_le (f := fun c (_ : c ∈ s) => V c) c hc le_rfl
  have hT : ∀ (i : ι) (b : ℂ) (s : Finset (ι → ℂ)), ∀ z ∈ ⨆ c ∈ s, V c,
      F i z - b • z ∈ ⨆ c ∈ s, V c := by
    intro i b s
    obtain ⟨M, hM⟩ : ∃ M : Submodule ℂ E,
        ∀ v, v ∈ M ↔ (v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c) :=
      ⟨{ carrier := {v | v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c}
         add_mem' := by
           rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
           refine ⟨G.add_mem hx hy, ?_⟩
           have : F i (x + y) - b • (x + y) = (F i x - b • x) + (F i y - b • y) := by
             rw [hadd i x hx y hy, smul_add]; abel
           rw [this]; exact Submodule.add_mem _ hx' hy'
         zero_mem' := ⟨G.zero_mem, by simp [hF0 i]⟩
         smul_mem' := by
           rintro a x ⟨hx, hx'⟩
           refine ⟨G.smul_mem a hx, ?_⟩
           have : F i (a • x) - b • (a • x) = a • (F i x - b • x) := by
             rw [hsmul i a x hx, smul_sub, smul_comm b a x]
           rw [this]; exact Submodule.smul_mem _ a hx' }, fun v => Iff.rfl⟩
    have hle : (⨆ c ∈ s, V c) ≤ M := iSup₂_le fun c hc v hv => by
      rw [hM]
      obtain ⟨hvG, hv'⟩ := (hV c v).1 hv
      refine ⟨hvG, ?_⟩
      rw [hv' i, ← sub_smul]
      exact hmemS s c hc ((V c).smul_mem _ hv)
    intro z hz
    exact ((hM z).1 (hle hz)).2
  have hB : ∀ (a : ι → ℂ) (s : Finset (ι → ℂ)), a ∉ s → ∀ y ∈ V a, ∀ z ∈ ⨆ c ∈ s, V c,
      y + z ∈ P → y ∈ P := by
    intro a s
    induction s using Finset.induction_on with
    | empty =>
      intro _ y _ z hz hyz
      simp at hz
      rw [hz, add_zero] at hyz; exact hyz
    | insert b t hbt ih =>
      intro ha y hy z hz hyz
      rw [Finset.mem_insert, not_or] at ha
      obtain ⟨hab, hat⟩ := ha
      rw [Finset.iSup_insert, Submodule.mem_sup] at hz
      obtain ⟨zb, hzb, zt, hzt, rfl⟩ := hz
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
      obtain ⟨hyG, hy'⟩ := (hV a y).1 hy
      obtain ⟨hzbG, hzb'⟩ := (hV b zb).1 hzb
      have hztG := hSG t hzt
      have hP1 : F i (y + (zb + zt)) - b i • (y + (zb + zt)) ∈ P :=
        P.sub_mem (hFP i _ hyz) (P.smul_mem _ hyz)
      have heq : F i (y + (zb + zt)) - b i • (y + (zb + zt))
          = (a i - b i) • y + (F i zt - b i • zt) := by
        rw [hadd i y hyG _ (G.add_mem hzbG hztG), hadd i zb hzbG zt hztG, hy' i, hzb' i]
        simp only [smul_add, sub_smul]; abel
      rw [heq] at hP1
      have hy2 : (a i - b i) • y ∈ V a := (V a).smul_mem _ hy
      have h3 := ih hat _ hy2 _ (hT i (b i) t zt hzt) hP1
      have hne : a i - b i ≠ 0 := sub_ne_zero.2 hi
      have h4 := P.smul_mem (a i - b i)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
  have hspan : ∀ c, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h} = V c := fun c =>
    le_antisymm (Submodule.span_le.2 fun x hx => (hV c x).2 hx)
      fun x hx => Submodule.subset_span ((hV c x).1 hx)
  have hmain : ∀ s : Finset (ι → ℂ), ∀ x ∈ P, x ∈ ⨆ c ∈ s, V c →
      x ∈ ⨆ c ∈ s, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx; simpa using hx
    | insert a s has ih =>
      intro x hxP hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      have hyP : y ∈ P := hB a s has y hy z hz hxP
      have hzP : z ∈ P := by
        have := P.sub_mem hxP hyP; simpa using this
      rw [Finset.iSup_insert]
      exact Submodule.mem_sup.2 ⟨y, Submodule.subset_span ⟨hyP, ((hV a y).1 hy).2⟩, z, ih z hzP hz, rfl⟩
  intro x hx
  have h := hdec x (hPG hx)
  simp only [hspan] at h
  exact hmain C x hx h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.NormSum.CoordAlg

open Classical Formalism.UG Formalism.UG.P Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem

theorem exists_prime_integralOver_gt (D : D7) (N : ℕ) (h : GA D N) (Q : ℕ) :
    ∃ p : ℕ, Q < p ∧ p.Prime ∧ IntegralOver D p h := by
  set g : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hg
  choose m hm0 hm using fun ij : Fin N × Fin N => denom (F := ℚ) (E := D.host.E) (g ij.1 ij.2)
  set M := ∏ ij, m ij with hMdef
  have hM0 : 0 < M := Finset.prod_pos fun ij _ => hm0 ij
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + Q + 1)
  have hpM' : ¬ p ∣ M := fun hd => by have := Nat.le_of_dvd hM0 hd; omega
  obtain ⟨v, hv, hw⟩ := exists_place p hp
  have hMv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hm'
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM'))).map
      (Int.castRingHom (𝓞 ℚ))
    refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hm')) (Ideal.mul_mem_left _ _ (by simpa using hv))
  have hi : ∀ i j, afsplitEps D.host.E v * g i j ∈ OhE D := fun i j => eps_mul_mem v M hMv _ (by
    rw [hMdef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ _) (hm (i, j)))
  obtain ⟨k, hk, hint, htriv⟩ := exists_int (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) v
    (h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) h.2 (Units.inv_eq_of_mul_eq_one_left ((mem_GA D _).1 h.2)) hi
  refine ⟨p, by omega, hp, ⟨k, hk⟩, (mem_intG _).2 hint, fun i j l => ?_⟩
  have := zero_at (F := ℚ) (E := D.host.E) v p hp hw (g i j - (1 : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) l
  rw [← htriv i j] at this
  exact this

theorem coord_isAlgebraic : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ (D : D7) (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q)
    (h : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n), IsAlgebraic ℚ (P.coord h U) := by
  intro _hPr hI D δ t0 Q P h U
  obtain ⟨S, dl, hL⟩ := GlobalTheory.NormSum.Denom.exists_letters D
  obtain ⟨p, hpQ, hp, k', hk', htr⟩ := exists_prime_integralOver_gt D P.d h Q
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ0 := P.level_pos
  have hsp : p ∣ Q → SplitIn D p := fun hd => absurd (Nat.le_of_dvd hQ0 hd) (by omega)
  obtain ⟨hterm, -, -⟩ := GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D (hI D) ⊤ δ t0 Q P.crv P.pt0 P hQ0
  have hmem : P.coord h U ∈ Qbar := by
    unfold Pair.coord
    refine finsum_induction (· ∈ Qbar) (zero_mem _) (fun x y => add_mem) (fun x => ?_)
    refine mul_mem (inv_mem (natCast_mem _ _)) ?_
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := (hI D).rep P.a p hp x.out
    rw [← hterm γ (Subgroup.subset_closure ⟨γ', h1⟩) k (Subgroup.subset_closure h2)]
    exact (CoordBound.term_bound_of_jets GlobalTheory.T.jets_torsion_translates_cm_theta_product D (hI D) S dl hL δ t0 Q P p hsp
      (CoordBound.nonempty_place p).some _ h k' hk' h3 htr U).1
  exact mem_algebraicClosure_iff.1 hmem

end GlobalTheory.NormSum.CoordAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitAny
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.OrbitAny

open GlobalTheory.FinPl.SplitOrbit

theorem orbitAny : ∀ (D : D7) (V₀ A L : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (L₀ : Lat V₀) (LA : Lat A) (LL : Lat L) (v : GlobalTheory.FinPl.Pl D), IsSelfDualC V₀ L₀ → IsSelfDualC A LA → IsSelfDualC L LL → OrthAt o L₀ LA LL v → ∀ γ ∈ grpAt V₀ (· = v), (∀ a : AE D, a • ratV (vecB o ζ) ∈ latA V₀ L₀ (· = v) → mt V₀ γ⁻¹ *ᵥ (a • ratV (vecB o ζ)) ∈ latA V₀ L₀ (· = v)) → ∃ a ∈ grpAt A (· = v), ∃ κ, InK V₀ L₀ (· = v) κ ∧ γ = o.emb (a, 1) * κ := by
  intro D V₀ A L o ζ hζ L₀ LA LL v hL₀ hLA hLL hO γ hγ hz
  have hT := GlobalTheory.FinPl.TamePlaces.tame D v
  have hM := isSDAt_pre_unitary (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D V₀ L₀ v hL₀) γ⁻¹
  obtain ⟨hA, hsplit⟩ := split_of_le o hM (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D L LL v hLL) (line_le o hζ hO _ hz)
  obtain ⟨a, ha, hmv⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D A v _ _ hT (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D A LA v hLA) hA
  exact ⟨a, ha, (o.emb (a, 1))⁻¹ * γ, ⟨mul_mem (inv_mem (emb_mem_grpAt o ha)) hγ,
    moves_of_split o hO γ a hsplit hmv⟩, (mul_inv_cancel_left _ _).symm⟩

end GlobalTheory.AscFin.OrbitAny

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairChangeBasis
section
namespace GlobalTheory.TracePairingBasisChange

open Matrix

theorem pair_eq_trace {K : Type} [Field K] {n d : ℕ} (X Y : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM X Y = Matrix.trace (Xᵀ * Y) := by
  unfold GlobalTheory.FlipMatch.pairM
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem pair_change_basis {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin d) (Fin d) K) (b : GL (Fin n) K) (c : GL (Fin d) K)
    (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM
                 ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K))
                 (-(Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B *
                   (↑c : Matrix (Fin d) (Fin d) K))) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  rw [pair_eq_trace, Matrix.mul_neg, Matrix.trace_neg, neg_inj]
  have hb : Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K) * Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hc : (↑c : Matrix (Fin d) (Fin d) K) * (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv c

  have key : Matrix.transpose ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K)) *
      (Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B * (↑c : Matrix (Fin d) (Fin d) K)) =
      (↑c⁻¹ : Matrix (Fin d) (Fin d) K) * ((Matrix.transpose P * (A * (Q * Matrix.transpose B))) * (↑c : Matrix (Fin d) (Fin d) K)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K)), hb, Matrix.one_mul]
  rw [key, Matrix.trace_mul_comm, Matrix.mul_assoc, hc, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.TracePairingBasisChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerDownArrowTransportAdjointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realIntertwiner_downArrow_transport_adjoint : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χ : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S.V T.V) (f : WO S.V T.V → ℂ), IsInfFam θ → GlobalTheory.Grid.IsWeil ψ true S.V T.V χ χ ω →
    GlobalTheory.Grid.IsVac ψ θ true S T f →
    ∃ (ω₀ : GlobalTheory.Grid.WRep T.V S.V) (f₀ : WO T.V S.V → ℂ) (χ₀ : (AE D)ˣ →* Circle)
      (e : GlobalTheory.Grid.Pol S T ≃ₗ[ℂ] PolF D S.V.rank T.V.rank),
      IsWeilDatumO ψ T.V S.V χ₀ χ₀ ω₀ ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D χ₀ τ (-a)) ∧
      IsVacVec ψ θ T.M S.M f₀ ∧
      ∀ It : PolF D S.V.rank T.V.rank →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M, IsItW θ T.M S.M ω₀ (ptOf ψ θ T.M S.M f₀) It →
        GlobalTheory.Grid.IsIntw θ T.M S.M ω.swap (GlobalTheory.Grid.fock ψ θ true S T f) (It ∘ₗ e.toLinearMap) := by
  first | exact @GlobalTheory.AdjTr.downArrow_transport | exact GlobalTheory.AdjTr.downArrow_transport | (intros; apply GlobalTheory.AdjTr.downArrow_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepPointMulPeriodUnipotentGLMeasurePreservingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepPoint_mul_periodUnipotent_GL_measurePreserving : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n' (c + 1), ∀ κ : GL n' k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, stepPt x₀ e * (v * embX (c + 1) κ).val = stepPt (x₀ * κ.val) (φ e) := by
  first | exact @GlobalTheory.TopLevelInv.stepPt_mul_symN_embX | exact GlobalTheory.TopLevelInv.stepPt_mul_symN_embX | (intros; apply GlobalTheory.TopLevelInv.stepPt_mul_symN_embX <;> assumption)
end

