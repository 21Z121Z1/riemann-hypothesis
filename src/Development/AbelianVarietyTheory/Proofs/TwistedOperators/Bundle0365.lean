import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0333
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceIntegratedOpMulEqZeroOfIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevSeminormWeilThetaPolynomialInHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
noncomputable section

open GlobalTheory.KernelSeminorm GlobalTheory.Size GlobalTheory.FockCompare GlobalTheory.ThetaGrowth
open scoped NNReal

namespace GlobalTheory.WeilSobolev

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem sobO_om_le (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (g : GA D S) (h : GA D T) {ρ : ℝ≥0}
    (hρ : ∀ a, ‖mov θ g⁻¹ h⁻¹ (letter a)‖ ≤ ρ) (d : ℕ) :
    ∀ f, IsThetaFunO ψ S T f → sobO ψ θ μ 𝓕 d (om (g, h) f) ≤
      ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d * sobO ψ θ μ 𝓕 d f := by
  induction d with
  | zero =>
    intro f hf
    rw [sobO_zero, sobO_zero, l2O_om_apply_eq_of_isThetaFunO hom hμ h𝓕 hf, pow_zero, one_mul]
  | succ d ih =>
    intro f hf
    have e1 : sobO ψ θ μ 𝓕 (d + 1) (om (g, h) f) =
        l2O μ 𝓕 (om (g, h) f) + ∑ a, sobO ψ θ μ 𝓕 d (heisDer ψ θ a (om (g, h) f)) :=
      Translate.wordSum_succ _ _ d _
    have e2 : ∀ a, sobO ψ θ μ 𝓕 d (heisDer ψ θ a (om (g, h) f)) ≤
        ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
          (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d *
        (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (d + 1) f) := by
      intro a
      rw [← dv_letter hc hom.std a, dv_om hom hc g h (letter a) hf]
      refine (ih _ (theta_dv hc hom.std _ hf)).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      exact sobO_dvL_le hc hom.std d (hρ a) ⟨f, hf⟩
    have e3 : l2O μ 𝓕 (om (g, h) f) ≤ sobO ψ θ μ 𝓕 (d + 1) f := by
      rw [l2O_om_apply_eq_of_isThetaFunO hom hμ h𝓕 hf]
      exact (sobO_zero (ψ := ψ) (θ := θ)).ge.trans (sobO_mono (Nat.zero_le _))
    rw [e1]
    refine (add_le_add e3 (Finset.sum_le_sum fun a _ => e2 a)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h1 : (1 : ℝ≥0∞) ≤ ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d :=
      one_le_pow₀ (ENNReal.one_le_coe_iff.2 le_self_add)
    rw [pow_succ]
    generalize sobO ψ θ μ 𝓕 (d + 1) f = s at *
    generalize ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d = q at *
    calc s + (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : ℝ≥0∞) *
          (q * (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * s))
        ≤ q * s + (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : ℝ≥0∞) *
          (q * (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * s)) :=
          add_le_add (le_mul_of_one_le_left' h1) le_rfl
      _ = _ := by push_cast; ring

theorem sobO_weil_le_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕) (k : ℕ),
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ y ∈ C₁, ∀ h : GA D X,
      (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (y, h) Φ)).toReal ≤
        C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁ μ 𝓕 hμ k
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ : IsStdChar D ψ (-1) := hω.std
  obtain ⟨B, hB⟩ := (hC₁.image (continuous_ofSgn_symm ε M)).exists_bound_of_continuousOn
    (GlobalTheory.RatCount.continuous_normInf hθ (sgn ε M)).continuousOn
  obtain ⟨CT, hCT⟩ := (GlobalTheory.SmoothForms.normInf_mul_le_and_le_height D θ X).2
  obtain ⟨L, hL, hL0⟩ : ∃ L : ℝ, (∀ a, ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖ ≤ L) ∧ 0 ≤ L :=
    ⟨∑ a, ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖,
      fun a => Finset.single_le_sum (f := fun a => ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a), by positivity⟩
  obtain ⟨c0, hc0, hc0'⟩ : ∃ c0 : ℝ, c0 = |CT| * L * |B| ∧ 0 ≤ c0 := ⟨_, rfl, by positivity⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, K = (Fintype.card (D.what₂.Tau × Fin X.rank × Fin (sgn ε M).rank × Bool) : ℝ≥0) :=
    ⟨_, rfl⟩
  refine ⟨k, (1 + (K : ℝ) * K * c0) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal,
    by positivity, fun y hy h => ?_⟩
  have hy' : (ofSgn ε M).symm y ∈ (ofSgn ε M).symm '' C₁ := ⟨y, hy, rfl⟩
  have eω : ω (y, h) Φ = (ω.toSgn ε) ((ofSgn ε M).symm y, h) Φ := by
    simp [WRep.toSgn]
  have hH : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ X h
  obtain ⟨H, hH'⟩ : ∃ H : ℝ, H = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := ⟨_, rfl⟩
  rw [← hH'] at hH ⊢
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = c0 * H := ⟨⟨c0 * H, by positivity⟩, rfl⟩
  have hρ : ∀ a, ‖mov θ ((ofSgn ε M).symm y)⁻¹ h⁻¹ (letter a)‖ ≤ ρ := by
    intro a
    refine (norm_mov_le_normInf _ _ _).trans ?_
    rw [inv_inv, GlobalTheory.RatCount.normInf_inv]
    have h1 : normInf θ X h ≤ |CT| * H := (hCT h).trans (by rw [← hH']; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have h2 : normInf θ (sgn ε M) ((ofSgn ε M).symm y) ≤ |B| :=
      (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB _ hy').trans (le_abs_self _))
    have h3 := GlobalTheory.RatCount.normInf_nonneg θ X h
    have h4 := GlobalTheory.RatCount.normInf_nonneg θ (sgn ε M) ((ofSgn ε M).symm y)
    rw [hρdef]
    calc normInf θ X h * ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖ * normInf θ (sgn ε M) ((ofSgn ε M).symm y)
        ≤ (|CT| * H) * L * |B| := by gcongr; exact hL a
      _ = c0 * H := by rw [hc0]; ring
  have key := GlobalTheory.WeilSobolev.sobO_om_le hω hc hμ.1 hμ.2.1 ((ofSgn ε M).symm y) h hρ k Φ hΦ
  rw [eω]
  have hs := sobO_ne_top hψ hθ hμ.1 hμ.2.1 hΦ k
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hs) key).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ← hK]
  have hQ : ((1 + K * (K * ρ) : ℝ≥0) : ℝ) ≤ (1 + (K : ℝ) * K * c0) * H := by
    push_cast
    rw [hρdef]
    have : (0 : ℝ) ≤ K := K.2
    nlinarith [mul_nonneg (mul_nonneg this this) hc0']
  calc _ ≤ ((1 + (K : ℝ) * K * c0) * H) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (NNReal.coe_nonneg _) hQ k) ENNReal.toReal_nonneg
    _ = (1 + (K : ℝ) * K * c0) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal * H ^ k := by
        rw [mul_pow]; ring

end GlobalTheory.WeilSobolev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TemperedKFiniteCoefficients
section
noncomputable section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
namespace GlobalTheory.TempKFin

theorem isTemperedKFin_of_isTempered : GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → GlobalTheory.Orb.IsTempered μ π → IsTemperedKFin ε μ π := by
  intro hadm n ε μ _ U _ _ _ π hπ hirr ⟨v, hv0, hv⟩ S hS hSK s hs s' hs' e he
  obtain ⟨φ, hφc, hφS, hφR⟩ := GlobalTheory.T.exists_K_projector_finite_dim hadm n ε U π hπ hirr S hS hSK
  set D : Submodule ℂ U := Submodule.span ℂ (Set.range fun g => π g v) with hD
  have hDdense : D.topologicalClosure = ⊤ := by
    have hinv : ∀ g, ∀ w ∈ D.topologicalClosure, π g w ∈ D.topologicalClosure := by
      intro g w hw
      have hmap : ∀ x ∈ (D : Set U), π g x ∈ (D : Set U) := by
        intro x hx
        have hle : D ≤ D.comap ((π g : U →L[ℂ] U) : U →ₗ[ℂ] U) := by
          rw [hD, Submodule.span_le]
          rintro _ ⟨h, rfl⟩
          exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
        exact hle hx
      have hw' : w ∈ closure (D : Set U) := by rwa [← Submodule.topologicalClosure_coe]
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      exact map_mem_closure (π g).continuous hw' hmap
    rcases hirr.2 D.topologicalClosure ⟨D.isClosed_topologicalClosure, hinv⟩ with h | h
    · exfalso
      apply hv0
      have : v ∈ D.topologicalClosure := D.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  have hint : ∀ u : U, Integrable (fun k : KG ε => φ k • π k u) (muK ε) := fun u =>
    (hφc.smul ((hπ.continuous_apply u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let T : U →ₗ[ℂ] U :=
    { toFun := fun u => ∫ k, φ k • π k u ∂(muK ε)
      map_add' := fun a b => by
        simp only [map_add, smul_add]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        simp only [smul_comm (φ _) c]
        exact integral_smul c _ }
  have hTapp : ∀ u, T u = ∫ k, φ k • π k u ∂(muK ε) := fun u => rfl
  have hTc : Continuous T := by
    refine AddMonoidHomClass.continuous_of_bound T (∫ k, ‖φ k‖ ∂(muK ε)) fun u => ?_
    calc ‖T u‖ ≤ ∫ k, ‖φ k‖ * ‖u‖ ∂(muK ε) :=
          norm_integral_le_of_norm_le ((hφc.norm.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).mul_const _)
            (Eventually.of_forall fun k => by rw [norm_smul, hπ.norm_apply])
      _ = (∫ k, ‖φ k‖ ∂(muK ε)) * ‖u‖ := integral_mul_const _ _
  haveI hR : FiniteDimensional ℂ (LinearMap.range T) := by
    rw [← Submodule.span_eq (LinearMap.range T), LinearMap.coe_range]
    exact hφR
  have hsurj : ∀ x : U, ∃ u ∈ D, T u = T x := by
    intro x
    haveI : FiniteDimensional ℂ (D.map T) := Submodule.finiteDimensional_of_le (LinearMap.map_le_range)
    have hcl : IsClosed ((D.map T : Submodule ℂ U) : Set U) := Submodule.closed_of_finiteDimensional _
    have hx : x ∈ closure (D : Set U) := by
      rw [← Submodule.topologicalClosure_coe, hDdense]; trivial
    have : T x ∈ closure ((D.map T : Submodule ℂ U) : Set U) := by
      rw [Submodule.map_coe]
      exact image_closure_subset_closure_image hTc ⟨x, hx, rfl⟩
    rw [hcl.closure_eq] at this
    obtain ⟨u, hu, hTu⟩ := this
    exact ⟨u, hu, hTu⟩
  obtain ⟨u, hu, hTu⟩ := hsurj s
  obtain ⟨u', hu', hTu'⟩ := hsurj s'
  rw [hTapp, hTapp, hφS s hs] at hTu
  rw [hTapp, hTapp, hφS s' hs'] at hTu'
  have hp : (1 : ℝ) ≤ 2 + e := by linarith
  have h0 := GlobalTheory.T.integrable_matrixCoeff_cyclic_span n ε μ U π hπ (2 + e) hp v (hv e he) u hu u' hu'
  have h1 := GlobalTheory.T.integrable_matrixCoeff_K_average_right n ε μ U π hπ (2 + e) hp φ hφc u u' h0
  have h2 := GlobalTheory.T.integrable_matrixCoeff_K_average_left n ε μ U π hπ (2 + e) hp φ hφc (∫ k, φ k • π k u ∂(muK ε)) u' h1
  rw [hTu, hTu'] at h2
  exact h2

end GlobalTheory.TempKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoSlopeMetaplecticLiftSchwartz
section
open scoped Matrix

namespace GlobalTheory.RealWeil

theorem tendsto_slope_omS_schwartz :
    ∀ (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] (pr : G →* Matrix.symplecticGroup l ℝ)
    (om : G →* (GlobalTheory.RealWeil.L2 l ≃ₗᵢ[ℂ] GlobalTheory.RealWeil.L2 l)) (omS : G →* (GlobalTheory.RealWeil.Sch l →L[ℂ] GlobalTheory.RealWeil.Sch l)),
    (∀ (g : G) (w : l ⊕ l → ℝ) (f : GlobalTheory.RealWeil.L2 l),
      om g (GlobalTheory.RealWeil.rho w f) = GlobalTheory.RealWeil.rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) →
    (∀ (g : G) (f : GlobalTheory.RealWeil.Sch l), om g (f.toLp 2) = (omS g f).toLp 2) →
    ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ γ : ℝ → G, γ 0 = 1 →
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
    (∀ f : GlobalTheory.RealWeil.Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((GlobalTheory.RealWeil.quad X f).toLp 2) 0) →
    ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (omS (γ t) f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (GlobalTheory.RealWeil.quad X f)) := by
  intro l _ _ G _ pr om omS h3 h4 X hX γ h0 hγ h6 f
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hb⟩ := exists_seminorm_le (l := l) k n
  have key : ∀ r, Filter.Tendsto
      (fun t : ℝ => ‖schwartzToL2 l (A r (t⁻¹ • (omS (γ t) f - f) - quad X f))‖) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    intro r
    have h := hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_toLp_omS h3 h4 hX h0 hγ h6 (hA r) f)
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    refine h.congr fun t => ?_
    have e : ∀ (B : Sch l →L[ℂ] L2 l) (u v w : Sch l) (s : ℝ), B (s • (u - v) - w) = s • (B u - B v) - B w := by
      intro B u v w s
      rw [B.map_sub, B.map_smul_of_tower, B.map_sub]
    have e1 : omS (γ 0) f = f := by rw [h0, omS.map_one]; rfl
    rw [zero_add, e1]
    exact congrArg norm (e ((schwartzToL2 l).comp (A r)) _ _ _ _).symm
  have hs := tendsto_finset_sum Finset.univ fun r _ => key r
  rw [Finset.sum_const_zero] at hs
  filter_upwards [hs.eventually (gt_mem_nhds hε)] with t ht
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  exact (hb _).trans_lt ht

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorLatticeMulTransposeStableIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.LatStab

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gen_mul_transpose {n d : ℕ} (x : Fin n → E) (y : Fin d → E) (a : AF F)
    (K : Matrix (Fin d) (Fin d) (AE F E)) :
    (a • incM F (Matrix.vecMulVec x y)) * Kᵀ =
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i))
        (a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i))) := by
  ext i j
  simp only [incM, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply,
    Matrix.transpose_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, map_mul, Finset.smul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  ring

theorem vecMulVec_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : Fin n → E) (hx : x ∈ X.L) (u : Fin d → AE F E)
    (hu : u ∈ AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)}) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u ∈ latAtV X W w := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨b, hb, hbi, y', hy', rfl⟩ := hu
    apply AddSubgroup.subset_closure
    refine ⟨b, hb, hbi, x, hx, y', hy', ?_⟩
    ext i j
    simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul]
    rw [mul_smul_comm]
  | zero =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact zero_mem _
  | add u v _ _ hu hv =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (u + v) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u +
          Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) v := by
      ext i j; simp [Matrix.vecMulVec_apply, mul_add]
    rw [this]; exact add_mem hu hv
  | neg u _ hu =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (-u) =
        -Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact neg_mem hu

theorem mul_transpose_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (K : Matrix (Fin d) (Fin d) (AE F E))
    (hK : ∀ a : AF F, At (evFin F w) a → evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)})
    (γ : Matrix (Fin n) (Fin d) (AE F E)) (hγ : γ ∈ latAtV X W w) : γ * Kᵀ ∈ latAtV X W w := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    rw [gen_mul_transpose]
    exact vecMulVec_mem X W w x hx _ (hK a ha hai y hy)
  | zero => simp
  | add u v _ _ hu hv => rw [Matrix.add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [Matrix.neg_mul]; exact neg_mem hu

theorem latAtV_mul_transpose_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (K K' : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), K' * K = 1 →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K' *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    ∀ γ, γ * Kᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w := by
  intro F E _ _ _ _ _ n d X W w K K' hKK hK hK' γ
  constructor
  · intro h
    have h2 := mul_transpose_mem X W w K' hK' _ h
    rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, hKK, Matrix.transpose_one, Matrix.mul_one] at h2
  · exact mul_transpose_mem X W w K hK γ

end GlobalTheory.LatStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPointsPartEigenformsCoefficientFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftPoints_part_eigenforms_coefficientField : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → (R.toCx3 F).H3W F.cr false → ∀ i p, ∃ a, ∀ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p → GlobalTheory.ConjScalar.EigK R.toRealDat i a (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) := by
  first | exact @GlobalTheory.ZPartEig.points_eig | exact GlobalTheory.ZPartEig.points_eig | (intros; apply GlobalTheory.ZPartEig.points_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicIndepCovolumeMeasure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerRestrict

theorem res_indep_covol : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ μ' : Measure (Mx D W.rank r)) (𝓨 𝓨' : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ' 𝓨' → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ' 𝓨' f = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs d _ _ ψ f hf μ μ' 𝓨 𝓨' h h'
  funext x
  exact GlobalTheory.MixModel.covolOne_integral_eq h h' (fun y => f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x))
    (fun γ hγ y => periodic_iso hs hf x γ hγ y)

end GlobalTheory.TowerRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopLineFromSeparation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows posDef_dual)
open GlobalTheory.SepRows
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopLineProof

theorem bilin_prop {X Y ι κ : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (fx : ι → X) (fy : κ → Y)
    (hx : Submodule.span ℂ (Set.range fx) = ⊤) (hy : Submodule.span ℂ (Set.range fy) = ⊤) (b b₀ : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (f : ι → κ → ℂ) (l l₀ : ℂ) (hb : ∀ i j, b (fx i) (fy j) = f i j * l) (hb₀ : ∀ i j, b₀ (fx i) (fy j) = f i j * l₀)
    (hne : b₀ ≠ 0) : b = (l / l₀) • b₀ := by
  have hl₀ : l₀ ≠ 0 := by
    rintro rfl
    refine hne (LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_)
    simp [hb₀]
  refine LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hb, hb₀, smul_eq_mul]
  field_simp

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem coefPlus_is (G : GridData L sc) {θ : InfFam D} (hθ : IsInfFam θ) : (coefPlus G θ).Is := by
  obtain ⟨hc, hs⟩ := GlobalTheory.CoefModel.realGL_laws hθ (G.V (.top 0))
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  refine GlobalTheory.CoefModel.coefOf_is _ _ _ (fun h hh => ?_) (fun h τ => ?_) (fun τ => ?_) (fun g hg => ?_)
  · have : GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom (G.V (.top 0)) h) = 1
      rw [show infHom (G.V (.top 0)) h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, this, map_one]
  · exact GlobalTheory.CoefModel.invTr_unitary (g := GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h τ)
      (GlobalTheory.RecDictModel.archM_unitary (G.V (.top 0)) (hθ τ) h)
  · refine ((hc τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h⁻¹ τ : Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ) = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (invTrK g) fun τ => by
      have := GlobalTheory.CoefModel.invTr_unitary (hg τ)
      rwa [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.FunObj.posDef_Xp G (tauE D τ)).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, e]
    exact funext fun τ => GlobalTheory.CoefModel.invTr_invTr _

end GlobalTheory.TopLineProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceIntegratedOpMulEqZeroOfIsotypicStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_integratedOp_mul_eq_zero_of_isotypic : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f : G → ℂ), Integrable f μ → ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (δ : G →* (X →L[ℂ] X)) (π : G →* (H →L[ℂ] H)), IsIrrUnitary δ → IsUnitaryRep π → GlobalTheory.AutMult.IsIsotypic δ π → ∀ [SecondCountableTopology G] (Q : H →L[ℂ] H), (∀ g, Q * π g = π g * Q) → HasTrace (repOp δ μ f) 0 → IsTraceClass (repOp π μ f * Q) → trace (repOp π μ f * Q) = 0 := by
  first | exact @GlobalTheory.trace_repOp_mul_eq_zero_of_isIsotypic | exact GlobalTheory.trace_repOp_mul_eq_zero_of_isIsotypic | (intros; apply GlobalTheory.trace_repOp_mul_eq_zero_of_isIsotypic <;> assumption)
end

