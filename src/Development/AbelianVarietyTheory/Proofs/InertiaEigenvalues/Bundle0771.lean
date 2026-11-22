import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermDependsOnlyOnIsotropicMeansStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledLagrangian_term_depends_only_on_isotropic_means : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), IsLagFrame W Y C → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ f₁ f₁' f₂ : WO V W → ℂ, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₁' → IsThetaFunO ψ V W f₂ → (∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, f₁ (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f₁' (HMul.hMul (I.map (incA D)) y + x) ∂ν) → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C f₁' f₂ := by
  first | exact @GlobalTheory.LagMeans.lagTerm_eq_of_means | exact GlobalTheory.LagMeans.lagTerm_eq_of_means | (intros; apply GlobalTheory.LagMeans.lagTerm_eq_of_means <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaIntegralSobolevContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.DownLift.Sobolev₂

open GlobalTheory.Size GlobalTheory.Grow
open scoped ComplexOrder

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem integrableOn_extV (R : RealDat D A Ks) (hm : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hc := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hK := hc.choose_spec.1
  have hKc := hc.choose_spec.2
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hFc : Continuous (R.extV i t y) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t y (γ * h) = R.extV i t y h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  have hlc : Continuous fun h => l (R.extV i t y h) := l.continuous_of_finiteDimensional.comp hFc
  have hH : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfd : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have : IsFiniteMeasure ((R.νV i t).restrict (R.fdV i t)) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol (Vc D i) (R.νV i t) (R.fdV i t)
      hH hfd).ne
  have hb := hK.exists_bound_of_continuousOn hlc.continuousOn
  have hbd : ∀ h, ‖l (R.extV i t y h)‖ ≤ hb.choose := by
    intro h
    obtain ⟨γ, hγ, c, hc, e⟩ := hKc h
    rw [e, hFi γ hγ c]
    exact hb.choose_spec c hc
  exact Integrable.of_bound hlc.aestronglyMeasurable hb.choose (.of_forall hbd)

set_option maxHeartbeats 1000000 in

theorem downInt_sobolev_cont : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) (ε : ℝ), 0 < ε → ∃ (d : ℕ) (δ : ENNReal), 0 < δ ∧ ∀ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ → ‖downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g‖ < ε := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y μ 𝓕 hμ f hf l g ε hε
  have hm := hG.core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hG.core.thP.ωP i t
  have hψ := hω.std
  have hpt := hG.core.thP.pt_theta i t
  have hvP : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hpt 1
    rwa [RealDat.ptP, GlobalTheory.FiniteFock.pureTensorO_one] at this
  obtain ⟨U₀, hU₀, hl₀⟩ := isTheta_iff_level.1 hvP
  obtain ⟨U₁, hU₁, hl₁⟩ := isTheta_iff_level.1 hf
  have hUo : IsOpen ((U₁ ⊓ U₀ : AddSubgroup (WO (Vc D i) (Wc D i))) : Set (WO (Vc D i) (Wc D i))) := by
    rw [AddSubgroup.coe_inf]; exact hU₁.inter hU₀
  have hptl : ∀ P, R.ptP i t P ∈ thetaLevel R.ψ (Vc D i) (Wc D i) U₀ := fun P =>
    ⟨hpt P, fun u hu h0 => by
      have e := ((GlobalTheory.FinTranslate.finite_translate D R.ψ R.θ _ _ hψ hθ _ hvP).2 u h0).2
      unfold RealDat.ptP
      rw [← e, hl₀.2 u hu h0]⟩
  have hfl : f ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := thetaLevel_anti inf_le_left hl₁
  have hpl : ∀ P, R.ptP i t P ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P =>
    thetaLevel_anti inf_le_right (hptl P)
  have hml : ∀ P, f - R.ptP i t P ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P => sub_mem hfl (hpl P)
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (Vc D i).rank (Wc D i).rank
  obtain ⟨C, hC0, hC⟩ := (H (Vc D i) (Wc D i) rfl rfl).real R.ψ hθ hUo
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  obtain ⟨HK, hHK⟩ := hK.exists_bound_of_continuousOn (continuous_height (Vc D i)).continuousOn
  have hHK0 : 0 ≤ HK := by
    obtain ⟨γ, -, c, hc, -⟩ := hKc 1
    exact (norm_nonneg _).trans (hHK c hc)
  have hg0 := height_pos (Wc D i) g
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * (HK * height (Wc D i) g) ^ Ae := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ by positivity
  have hbound : ∀ φ ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀), ∀ h,
      ‖thetaKO (R.ωP i t) h g φ‖ ≤ B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by
    intro φ hφ h
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hKc h
    rw [GlobalTheory.ChainOnto.ThetaSwap.thetaKO_left_fst hω hφ.1 γ hγ c g]
    have h1 := (hC _ _ (R.ωP i t) hω μ 𝓕 hμ φ hφ).2 c g
    have hc1 : height (Vc D i) c ≤ HK := (Real.le_norm_self _).trans (hHK c hc)
    have hc0 := height_pos (Vc D i) c
    have hs : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d φ).toReal := ENNReal.toReal_nonneg
    have h2 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (height (Vc D i) c * height (Wc D i) g) ^ Ae ≤
        C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hc0 hg0).le
        (mul_le_mul_of_nonneg_right hc1 hg0.le) Ae) (mul_nonneg hC0 hs)
    have h3 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae =
        B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by rw [hB]; ring
    exact h1.trans (h2.trans_eq h3)
  have hl1 : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := integrableOn_extV R hm i t y l
  have hint : ∀ φ ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀),
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g φ * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := fun φ hφ =>
    Integrable.bdd_mul hl1 ((hω.om_cont φ hφ.1 0).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (.of_forall (hbound φ hφ))
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∫ h in R.fdV i t, ‖l (R.extV i t y h)‖ ∂(R.νV i t) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hMdef ▸ integral_nonneg fun _ => norm_nonneg _
  have hpos : 0 < B * M + 1 := by positivity
  refine ⟨d, ENNReal.ofReal (ε / (B * M + 1)), ENNReal.ofReal_pos.2 (by positivity), fun P hP => ?_⟩
  have hs := ENNReal.toReal_lt_of_lt_ofReal hP
  have hs0 : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := ENNReal.toReal_nonneg
  have e : downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g =
      ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h) ∂(R.νV i t) := by
    have i1 := hint f hfl
    have i2 := hint (R.ptP i t P) (hpl P)
    have e1 := integral_sub i1 i2
    refine e1.symm.trans (integral_congr_ae (.of_forall fun h => ?_))
    have e2 : R.ωP i t (h, g) (f - R.ptP i t P) = R.ωP i t (h, g) f - R.ωP i t (h, g) (R.ptP i t P) :=
      LinearMap.map_sub _ _ _
    show thetaKO (R.ωP i t) h g f * l (R.extV i t y h) - thetaKO (R.ωP i t) h g (R.ptP i t P) * l (R.extV i t y h) =
      thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h)
    refine (sub_mul _ _ _).symm.trans (congrArg (· * l (R.extV i t y h)) ?_)
    exact (congrFun e2 0).symm
  rw [e]
  have hle := norm_integral_le_of_norm_le (μ := (R.νV i t).restrict (R.fdV i t))
    (f := fun h => thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h))
    (hl1.norm.const_mul (B * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal))
    (.of_forall fun h => by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbound _ (hml P) h) (norm_nonneg _)))
  rw [integral_const_mul, ← hMdef] at hle
  calc _ ≤ _ := hle
    _ ≤ (B * M + 1) * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := by nlinarith
    _ < (B * M + 1) * (ε / (B * M + 1)) := by gcongr
    _ = ε := by field_simp

end GlobalTheory.DownLift.Sobolev₂
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonicalInertTensorCompletionEquivStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_inert_tensor_completion_equiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∃ e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L, (∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) = Dv.σw (e x)) ∧ (∀ x, x ∈ Formalism.UG.tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ↔ e x ∈ Formalism.UG.intL (w.adicCompletion L)) ∧ ∀ z : AL L, e (compAt L v z) = F.κ z w := by
  first | exact @GlobalTheory.InertTransferCanon.exists_canonical_equiv | exact GlobalTheory.InertTransferCanon.exists_canonical_equiv | (intros; apply GlobalTheory.InertTransferCanon.exists_canonical_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDoubledLagrangianOfRationalUnitaryFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SWLagTerms.LagrangianFrames

section Blocks

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem row_rel (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) :
    B * fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ = fromBlocks G⁻¹ 0 0 (-G⁻¹) := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have h1 : fromBlocks G 0 0 (-G) * fromBlocks G⁻¹ 0 0 (-G⁻¹) = 1 := by
    rw [fromBlocks_multiply]; simp [Matrix.mul_nonsing_inv _ hu, fromBlocks_one]
  have h2 : fromBlocks G⁻¹ 0 0 (-G⁻¹) * fromBlocks G 0 0 (-G) = 1 := by
    rw [fromBlocks_multiply]; simp [Matrix.nonsing_inv_mul _ hu, fromBlocks_one]
  have hL : (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) * B = 1 := by
    calc (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) * B
        = fromBlocks G⁻¹ 0 0 (-G⁻¹) * (Bᴴ * fromBlocks G 0 0 (-G) * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hB, h2]
  have hR : B * (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) = 1 := mul_eq_one_comm.1 hL
  calc B * fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ
      = B * (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) * fromBlocks G⁻¹ 0 0 (-G⁻¹) := by
        simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
    _ = fromBlocks G⁻¹ 0 0 (-G⁻¹) := by rw [hR, Matrix.one_mul]

theorem blocks_rel (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) :
    B.toBlocks₁₁ * G⁻¹ * B.toBlocks₁₁ᴴ - B.toBlocks₁₂ * G⁻¹ * B.toBlocks₁₂ᴴ = G⁻¹ ∧
    B.toBlocks₁₁ * G⁻¹ * B.toBlocks₂₁ᴴ - B.toBlocks₁₂ * G⁻¹ * B.toBlocks₂₂ᴴ = 0 ∧
    B.toBlocks₂₁ * G⁻¹ * B.toBlocks₁₁ᴴ - B.toBlocks₂₂ * G⁻¹ * B.toBlocks₁₂ᴴ = 0 ∧
    B.toBlocks₂₁ * G⁻¹ * B.toBlocks₂₁ᴴ - B.toBlocks₂₂ * G⁻¹ * B.toBlocks₂₂ᴴ = -G⁻¹ := by
  have h := row_rel G hG B hB
  rw [← fromBlocks_toBlocks B, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, zero_sub, ← sub_eq_add_neg] at h
  exact h

end Blocks

section Blocks2

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem form_eq (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) :
    (B.toBlocks₁₁ - B.toBlocks₂₁) * G⁻¹ * (B.toBlocks₁₁ - B.toBlocks₂₁)ᴴ =
      (B.toBlocks₂₂ - B.toBlocks₁₂) * G⁻¹ * (B.toBlocks₂₂ - B.toBlocks₁₂)ᴴ := by
  obtain ⟨h11, h12, h21, h22⟩ := blocks_rel G hG B hB
  set a := B.toBlocks₁₁
  set b := B.toBlocks₁₂
  set c := B.toBlocks₂₁
  set d := B.toBlocks₂₂
  rw [← sub_eq_zero, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub]
  have : (a - c) * G⁻¹ * (aᴴ - cᴴ) - (d - b) * G⁻¹ * (dᴴ - bᴴ) =
      (a * G⁻¹ * aᴴ - b * G⁻¹ * bᴴ) + (c * G⁻¹ * cᴴ - d * G⁻¹ * dᴴ) - (a * G⁻¹ * cᴴ - b * G⁻¹ * dᴴ) -
        (c * G⁻¹ * aᴴ - d * G⁻¹ * bᴴ) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [this, h11, h12, h21, h22]; abel

theorem adj_form (G : Matrix n n K) (hG : G.det ≠ 0) (hH : Gᴴ = G) (M : Matrix n n K) :
    (G⁻¹ * Mᴴ * G)ᴴ * G * (G⁻¹ * Mᴴ * G) = G * (M * G⁻¹ * Mᴴ) * G := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, hH,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem ker_trivial (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) (v : n → K)
    (h1 : (G⁻¹ * (B.toBlocks₂₂ - B.toBlocks₁₂)ᴴ * G) *ᵥ v = 0)
    (h2 : (G⁻¹ * (B.toBlocks₁₁ - B.toBlocks₂₁)ᴴ * G) *ᵥ v = 0) : v = 0 := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have hrow := row_rel G hG B hB
  set w := G *ᵥ v
  have k1 : (B.toBlocks₂₂ - B.toBlocks₁₂)ᴴ *ᵥ w = 0 := by
    have := congrArg (G *ᵥ ·) h1
    simpa [w, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this
  have k2 : (B.toBlocks₁₁ - B.toBlocks₂₁)ᴴ *ᵥ w = 0 := by
    have := congrArg (G *ᵥ ·) h2
    simpa [w, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this
  have hx : Bᴴ *ᵥ Sum.elim w (-w) = 0 := by
    rw [← fromBlocks_toBlocks B, fromBlocks_conjTranspose, fromBlocks_mulVec]
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mulVec] at k1 k2
    ext (i | i)
    · have := congrFun k2 i
      simp only [Pi.sub_apply, Pi.zero_apply] at this
      simp only [Sum.elim_inl, Pi.zero_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_neg, Pi.add_apply,
        Pi.neg_apply]
      linear_combination this
    · have := congrFun k1 i
      simp only [Pi.sub_apply, Pi.zero_apply] at this
      simp only [Sum.elim_inr, Pi.zero_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_neg, Pi.add_apply,
        Pi.neg_apply]
      linear_combination -this
  have hK : fromBlocks G⁻¹ 0 0 (-G⁻¹) *ᵥ Sum.elim w (-w) = 0 := by
    rw [← hrow, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hw : w = 0 := by
    have := congrArg (fun x => fromBlocks G 0 0 (-G) *ᵥ x) hK
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, fromBlocks_multiply] at this
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      Matrix.mul_nonsing_inv _ hu, neg_zero, fromBlocks_one, Matrix.one_mulVec] at this
    funext i; exact congrFun this (Sum.inl i)
  have : G⁻¹ *ᵥ w = v := by simp [w, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  rw [← this, hw, Matrix.mulVec_zero]

end Blocks2

variable {D : D7}

theorem unitary_of_mt (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (h : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) :
    g₀ᴴ * (GlobalTheory.Doubling.dblSp W).gram * g₀ = (GlobalTheory.Doubling.dblSp W).gram := by
  have hγ : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ) *
      (GlobalTheory.Doubling.dblSp W).gram.map (incA D) * Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ =
      (GlobalTheory.Doubling.dblSp W).gram.map (incA D) := γ.2
  have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g₀.map (incA D)) = g₀ᴴ.map (incA D) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    simp [sigR, CMData.sig, inclR]; rfl
  rw [h, hc, ← Matrix.map_mul, ← Matrix.map_mul] at hγ
  exact Matrix.map_injective
    (Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)) hγ

theorem star_dot' (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (x x' : Fin W.rank → D.host.E) :
    star (c *ᵥ x) ⬝ᵥ W.gram *ᵥ (c *ᵥ x') = star x ⬝ᵥ (cᴴ * W.gram * c) *ᵥ x' := by
  rw [Matrix.star_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

theorem blk_unitary (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (h : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) :
    (blk W g₀)ᴴ * fromBlocks W.gram 0 0 (-W.gram) * blk W g₀ = fromBlocks W.gram 0 0 (-W.gram) := by
  have hU := unitary_of_mt W γ g₀ h
  rw [show (GlobalTheory.Doubling.dblSp W).gram = GlobalTheory.Doubling.dblGram finSumFinEquiv W.gram from GlobalTheory.Doubling.gram_hdbl W]
    at hU
  have := congrArg (fun X => X.submatrix finSumFinEquiv finSumFinEquiv) hU
  simp only [← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _, Matrix.conjTranspose_submatrix,
    GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.submatrix_blkMat] at this
  exact this

theorem exists_lag_isLagFrame_frameOf (D : D7) (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∃ Y : Lag W, IsLagFrame W Y (frameOf W g₀) := by
  intro h
  have hB := blk_unitary W γ g₀ h
  have hG : (HSpace.gram W).det ≠ 0 := Formalism.L2.Theta.gram_det_ne W
  have hH : (HSpace.gram W)ᴴ = HSpace.gram W := Matrix.ext fun i j => W.herm.eq _ _
  set C := frameOf W g₀ with hC
  have h1 : C.1 = (HSpace.gram W)⁻¹ * ((blk W g₀).toBlocks₂₂ - (blk W g₀).toBlocks₁₂)ᴴ * HSpace.gram W := rfl
  have h2 : C.2 = (HSpace.gram W)⁻¹ * ((blk W g₀).toBlocks₁₁ - (blk W g₀).toBlocks₂₁)ᴴ * HSpace.gram W := rfl
  let φ : (Fin W.rank → D.host.E) →ₗ[D.host.E] (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) :=
    LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2)
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun v hv => ?_
    have e1 : C.1 *ᵥ v = 0 := congrArg Prod.fst hv
    have e2 : C.2 *ᵥ v = 0 := congrArg Prod.snd hv
    rw [h1] at e1
    rw [h2] at e2
    exact ker_trivial _ hG _ hB v e1 e2
  let Y : Lag W := ⟨LinearMap.range φ, by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    show star (C.1 *ᵥ x) ⬝ᵥ W.gram *ᵥ (C.1 *ᵥ y) = star (C.2 *ᵥ x) ⬝ᵥ W.gram *ᵥ (C.2 *ᵥ y)
    rw [star_dot', star_dot', h1, h2, adj_form _ hG hH, adj_form _ hG hH, form_eq _ hG _ hB]⟩
  refine ⟨Y, ?_⟩
  have hs := congrArg (Submodule.map φ) (Pi.basisFun D.host.E (Fin W.rank)).span_eq
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at hs
  refine Eq.trans ?_ hs
  congr 2
  funext j
  ext a <;> simp [φ, Matrix.mulVec, dotProduct, Pi.single_apply]

end GlobalTheory.SWLagTerms.LagrangianFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRankinSelbergPlaceSetSupersetTotallyCo
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

noncomputable section

namespace GlobalTheory.RSNonvan.GoodSet

variable {E : Type} [Field E] [NumberField E]

theorem psiLoc_cond (w : HeightOneSpectrum (𝓞 E))
    (hw : FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0) (x : w.adicCompletion E) :
    (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w := by
  have key : (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔
      ∀ a ∈ w.adicCompletionIntegers E, GroundTheory.Global.localAdelicChar E w (a * x) = 1 := by
    refine forall_congr' fun y => imp_congr Iff.rfl ?_
    change GlobalTheory.StdCharConductor.psi E (sFin E (sLoc E w (x * y))) = 1 ↔ _
    rw [GlobalTheory.StdCharConductor.psi_loc_eq_one_iff, mul_comm]
  rw [key, GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff, GroundTheory.Global.mem_localInvDifferent_iff_valued, hw]
  change _ ↔ x ∈ w.adicCompletionIntegers E
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rfl

theorem finite_sameBelow (u : HeightOneSpectrum (𝓞 E)) :
    {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}.Finite := by
  set N : ℕ := Ideal.absNorm u.asIdeal
  have hN : N ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm u
    omega
  have hI : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset fun w' hw' => ?_
  simp only [Set.mem_setOf_eq] at hw' ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  have h1 : ((N : ℤ)) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem u.asIdeal
  rw [← hw', Ideal.mem_comap, map_natCast] at h1
  exact h1

variable [IsTotallyComplex E]

theorem exists_isGood_superset (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' := by
  classical
  have hD : {w : HeightOneSpectrum (𝓞 E) | FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0}.Finite :=
    FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  set T₁ : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hD.toFinset
  set S : Set (HeightOneSpectrum (𝓞 E)) := {w' | ∃ u ∈ T₁, Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}
  have hS : S.Finite := by
    have : S = ⋃ u ∈ T₁, {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
        Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal} := by
      ext w'
      simp [S]
    rw [this]
    exact T₁.finite_toSet.biUnion fun u _ => finite_sameBelow u
  have hT₁ : ∀ w ∈ T₁, w ∈ hS.toFinset := fun w hw => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨w, hw, rfl⟩
  refine ⟨hS.toFinset, fun w hw => hT₁ w (Finset.mem_union_left _ hw), ?_, ?_⟩
  · intro w hw w' hw'
    rw [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨u, hu, hwu⟩ := hw
    exact ⟨u, hu, hw'.trans hwu⟩
  · intro w hw x
    refine psiLoc_cond w ?_ x
    by_contra h
    exact hw (hT₁ w (Finset.mem_union_right _ (by simpa using h)))

end GlobalTheory.RSNonvan.GoodSet

theorem GlobalTheory.RSNonvan.exists_isGood_superset_all : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' :=
  fun _ _ _ _ T => GlobalTheory.RSNonvan.GoodSet.exists_isGood_superset T

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstColumnInvFiniteMemCompactOnSupportStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstColumn_inv_finite_mem_compact_on_support : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := by
  first | (exact @GlobalTheory.NmUnfCol.finite_first_col_inv_compact) | (exact GlobalTheory.NmUnfCol.finite_first_col_inv_compact) | (intros; apply GlobalTheory.NmUnfCol.finite_first_col_inv_compact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByUnitaryIntegralPointsOfLevelFixedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_by_unitaryIntegralPoints_of_level_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ U0 : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w n → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ φ ∈ U, (∀ g, ∀ κ ∈ U0, φ (F.j (g * κ)) = φ (F.j g)) → ∀ x : locU n w, p x ∈ Formalism.UG.KU σ n → RU L n x.val φ = φ := by
  first | exact @GlobalTheory.UnramDict.fixed_of_mem_KU | exact GlobalTheory.UnramDict.fixed_of_mem_KU | (intros; apply GlobalTheory.UnramDict.fixed_of_mem_KU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLowerStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramClass_vacuumCombination_orbitSum_mod_lower : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ i : D.nd.Loc, ClassSum (M.loc i) → TypeOrth D i := by
  first | exact @GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum | exact GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum | (intros; apply GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum <;> assumption)
end

