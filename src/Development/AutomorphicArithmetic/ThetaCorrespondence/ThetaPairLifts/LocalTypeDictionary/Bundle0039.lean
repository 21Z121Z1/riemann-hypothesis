import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0713
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0782
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0004
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0785
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0700
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0034
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormGKIsotypicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0761
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0006
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistFockJetThetaRational
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0023
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0766
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0666
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanProductRuleDerivative
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ArchProdRule
open Filter Topology
open scoped Classical in
theorem archimedean_hasDerivAt_prod : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)),
    (∀ i, γ i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W) →
    ∀ T : Fin k → ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ i t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ i (Multiplicative.ofAdd t))) ⇑f ⇑(T i t f)) →
    (∀ i s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i (s + t) f = T i s (T i t f)) →
    (∀ i (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i 0 f = f) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (c : Fin k → ℂ),
    (∀ i, HasDerivAt (fun t : ℝ => T i t f y) (c i) 0) →
    HasDerivAt (fun t : ℝ => (List.ofFn fun i => T i t).prod f y) (∑ i, c i) 0 := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW k γ hγ T hT hadd h0 f y c hc
  have hQ : ∀ i g, ∃ q, Tendsto (fun t : ℝ => t⁻¹ • (T i t g - g)) (𝓝[≠] 0) (𝓝 q) := fun i g =>
    _root_.GlobalTheory.T.schwartz_function_slope_estimate hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i) g
  choose Q hQ using hQ
  have hcont : ∀ i t, Continuous (T i t) := fun i =>
    _root_.GlobalTheory.T.archimedean_weil_representation_continuous hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i)
  have hprod := slope_prod k T Q hcont h0 hQ f
  let ev : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
  have hev : ∀ (s : ℝ) (g h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), ev (s • (g - h)) = s • (g y - h y) := by
    intro s g h
    rw [ContinuousLinearMap.map_smul_of_tower, map_sub]
    rfl
  have hevq : ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), ev g = g y := fun g => rfl
  have hci : ∀ i, c i = Q i f y := by
    intro i
    have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hc i)
    have h2 := (ev.continuous.tendsto _).comp (hQ i f)
    rw [hevq] at h2
    simp only [zero_add, h0] at h1
    refine tendsto_nhds_unique h1 (h2.congr fun t => ?_)
    exact hev _ _ _
  have hsum : (∑ i, c i) = ev (∑ i, Q i f) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (hci i).trans (hevq _).symm
  rw [hasDerivAt_iff_tendsto_slope_zero, hsum]
  have hp0 : (List.ofFn fun i => T i 0).prod = 1 := by
    have e : (fun i => T i 0) = fun _ => (1 : Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) :=
      funext fun i => LinearMap.ext (h0 i)
    rw [e, List.ofFn_const, List.prod_replicate, one_pow]
  have h1 := (ev.continuous.tendsto _).comp hprod
  refine h1.congr fun t => ?_
  simp only [Function.comp_apply, zero_add, hp0]
  exact hev _ _ _
end GlobalTheory.ArchProdRule
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_product_rule_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)),
    (∀ i, γ i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W) →
    ∀ T : Fin k → ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ i t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ i (Multiplicative.ofAdd t))) ⇑f ⇑(T i t f)) →
    (∀ i s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i (s + t) f = T i s (T i t f)) →
    (∀ i (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i 0 f = f) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (c : Fin k → ℂ),
    (∀ i, HasDerivAt (fun t : ℝ => T i t f y) (c i) 0) →
    HasDerivAt (fun t : ℝ => (List.ofFn fun i => T i t).prod f y) (∑ i, c i) 0 := by
  first | exact @_root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod | exact _root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod | (intros; apply _root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanSumSizeOppositeConjugate
section
section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.SumSize.OppConj
namespace GlobalTheory.SumSize.OppConj
theorem archimedean_sum_size_opposite_conjugate : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfRowK :=
  fun hP hI hD hDp => infRowK_of (_root_.GlobalTheory.T.conj_mean_kernel_pairing hP hI hD hDp)
end GlobalTheory.SumSize.OppConj
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_bound_opposite_conjugation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfRowK := by
  first | exact @_root_.GlobalTheory.SumSize.OppConj.archimedean_sum_size_opposite_conjugate | exact _root_.GlobalTheory.SumSize.OppConj.archimedean_sum_size_opposite_conjugate | (intros; apply _root_.GlobalTheory.SumSize.OppConj.archimedean_sum_size_opposite_conjugate <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomSpannedByClassSums
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.BotSpan
theorem classSums_span_bottom : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (H : Finset (GA D WW)) (K : Finset (FVar D WW.rank A.rank →₀ ℕ)) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧
      (∀ h ∈ H, h ∈ GfC WW) ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ c : GA D WW → (FVar D WW.rank A.rank →₀ ℕ) → ℂ, (∀ a b, c a b ∈ M₀) ∧
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h' := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  classical
  obtain ⟨K, hK⟩ := _root_.GlobalTheory.T.bottomClassSum_finite_support hP hI hL hX
  obtain ⟨M₁, hM₁, hr⟩ := _root_.GlobalTheory.T.realTranslate_preserves_rationalAction hP hI hL hX
  obtain ⟨J, M₂, hJ, hM₂, hl⟩ := _root_.GlobalTheory.T.bottomForm_rightTranslate_level hP hI hL hX
  obtain ⟨H, hH, hc⟩ := _root_.GlobalTheory.T.bottomClasses_finite hP hI hL hX J hJ
  refine ⟨H, K, M₁ ⊔ M₂, IntermediateField.finiteDimensional_sup M₁ M₂, hH, ?_⟩
  intro t h hh k
  obtain ⟨γ, hγ, r, hrI, h₀, hh₀, κ, hκJ, hκf, rfl⟩ := hc h hh
  have hx : h₀ * κ ∈ GfC WW := mul_mem (hH h₀ hh₀) hκf
  have hγr : γ * r ∈ GfC WW := by
    have e : γ * r = (γ * r * h₀ * κ) * (h₀ * κ)⁻¹ := by group
    rw [e]; exact mul_mem hh (inv_mem hx)
  obtain ⟨c, hcM, hcE⟩ := hr t γ hγ r hrI hγr (h₀ * κ) k
  obtain ⟨ℓ, hℓM, hℓ⟩ := hl t κ hκJ hκf
  have e1 : X.I W.ψ W.θ t (MvPolynomial.monomial k 1) (γ * r * h₀ * κ) =
      ∑ k' ∈ c.support, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ := by
    have e0 : γ * r * h₀ * κ = γ * ((h₀ * κ) * r) := by
      rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC WW hrI hx]; simp only [mul_assoc]
    rw [e0, _root_.GlobalTheory.T.bottomIntegral_leftInvariant_rationalPoints hP hI hL hX t _ γ hγ, hcE]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [hℓ, mul_assoc]
  refine ⟨fun h' k' => if h' = h₀ then c k' * ℓ else 0, fun a b => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact mul_mem ((le_sup_left : M₁ ≤ M₁ ⊔ M₂) (hcM b)) ((le_sup_right : M₂ ≤ M₁ ⊔ M₂) hℓM)
    · exact zero_mem _
  rw [e1, Finset.sum_eq_single_of_mem h₀ hh₀ (fun b _ hb => by simp [hb])]
  simp only [if_true]
  calc ∑ k' ∈ c.support, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀
      = ∑ k' ∈ c.support ∪ K, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        Finset.sum_subset Finset.subset_union_left fun k' _ hk' => by
          rw [Finsupp.notMem_support_iff.1 hk', zero_mul, zero_mul]
    _ = ∑ k' ∈ K, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        (Finset.sum_subset Finset.subset_union_right fun k' _ hk' => by
          rw [hK t h₀ (hH h₀ hh₀) k' hk', mul_zero]).symm
end GlobalTheory.BotSpan
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_spanned_by_classSums : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (H : Finset (GA D WW)) (K : Finset (FVar D WW.rank A.rank →₀ ℕ)) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧
      (∀ h ∈ H, h ∈ GfC WW) ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ c : GA D WW → (FVar D WW.rank A.rank →₀ ℕ) → ℂ, (∀ a b, c a b ∈ M₀) ∧
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h' := by
  first | exact @_root_.GlobalTheory.BotSpan.classSums_span_bottom | exact _root_.GlobalTheory.BotSpan.classSums_span_bottom | (intros; apply _root_.GlobalTheory.BotSpan.classSums_span_bottom <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFiniteSumGelfandKirillovMultiplicity
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
namespace GlobalTheory.CuspGK
theorem exists_finite_sum_gelfandKirillov_multiplicity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ → (∀ τ, IsTypeAt θ V τ (S τ) ψ) →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ (n : ℕ) (F : Fin n → MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ))
      (u : Fin n → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, (∀ u, IsAutFunSm θ V (F l u)) ∧ (∀ u, IsCuspFun V (F l u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F l (Function.update u τ w) = rTr V (atTau θ V τ g) (F l u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F l (Function.update u τ w) = Rder θ V τ X (F l u))) ∧ ∀ g, ψ g = ∑ l, F l (u l) g := by
  have I1 := _root_.GlobalTheory.T.cuspForms_eq_iSup_irreducible_gK
  have I2 := _root_.GlobalTheory.T.cuspForm_gK_submodule_of_type
  have I3 := _root_.GlobalTheory.T.cuspForm_gK_isotypic_decomposition
  intro hP D θ V S M hθ ψ hA hC hT hW
  have hψ : IsKFinCuspOfType θ M ψ := ⟨hA, hC, hT, hW⟩
  have h1 := I1 hP θ V S M hθ ψ hA hC hW
  have hle : (⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ gkGen θ M ψ ∧ IsIrrGKSub θ M A), A) ≤ multSpan θ M :=
    iSup_le fun A => iSup_le fun hA' =>
      I3 hP θ V S M hθ A hA'.2 fun f hf => I2 hP θ V S M hθ ψ hψ f (hA'.1 hf)
  obtain ⟨n, F, u, hF, hsum⟩ := exists_sum_of_mem_multSpan θ M (hle h1)
  exact ⟨n, F, u, fun l => ⟨(hF l).aut, (hF l).cusp, (hF l).equivK, (hF l).equivLie⟩, hsum⟩
end GlobalTheory.CuspGK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_gelfandKirillov_finite_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ → (∀ τ, IsTypeAt θ V τ (S τ) ψ) →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ (n : ℕ) (F : Fin n → MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ))
      (u : Fin n → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, (∀ u, IsAutFunSm θ V (F l u)) ∧ (∀ u, IsCuspFun V (F l u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F l (Function.update u τ w) = rTr V (atTau θ V τ g) (F l u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F l (Function.update u τ w) = Rder θ V τ X (F l u))) ∧ ∀ g, ψ g = ∑ l, F l (u l) g := by
  first | exact @_root_.GlobalTheory.CuspGK.exists_finite_sum_gelfandKirillov_multiplicity | exact _root_.GlobalTheory.CuspGK.exists_finite_sum_gelfandKirillov_multiplicity | (intros; apply _root_.GlobalTheory.CuspGK.exists_finite_sum_gelfandKirillov_multiplicity <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsRationalMoveOfJets
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.RatMoveJets
theorem exists_rational_move_of_jets : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (r : FinPt ch.G p.small) (r' : FinPt ch.G p.big), GlobalTheory.MovedKappaEx.RatFin _ r → GlobalTheory.MovedKappaEx.RatFin _ r' →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime],
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small (r * x)) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big (r' * y)) (stdL D _) →
        GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (r * x) (r' * y) (c * κ) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hJ r r' hr hr'
  obtain ⟨hns, hnb⟩ := hp.nodes
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_unitaryCoordinate_of_rationalPoint_definiteVertex ch.S.toGridChoice _ hns r hr
  obtain ⟨U', hU'⟩ := GlobalTheory.T.exists_unitaryCoordinate_of_rationalPoint_definiteVertex ch.S.toGridChoice _ hnb r' hr'
  have hlx := GlobalTheory.T.vertexLatticeCoords_rationalPoint_mul_eq_coordMatrix ch.S.toGridChoice _ r U hU x
  have hly := GlobalTheory.T.vertexLatticeCoords_rationalPoint_mul_eq_coordMatrix ch.S.toGridChoice _ r' U' hU' y
  have hd := _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hP hI ch hch p hp x y
  obtain ⟨ε, hm, hu, hj⟩ := _root_.GlobalTheory.T.twist_fock_jetTheta_rational hP hI ch hch p hp x y _ (hd.const_mul κ) ((jetKap_iff ch p x y κ).1 hJ) r r' U U' hU hU'
  obtain ⟨hsd, hsd'⟩ := _root_.GlobalTheory.MovedSD.moved_series_decomposition hP hI ch hch p hp x y
  obtain ⟨ε', hm', hu', hB⟩ := _root_.GlobalTheory.T.twist_pairing_rational_pullback_eq hP hI ch.S.Z.crv ch.S.Z.pt0 (ch.S.Z.e0_is p hp) (GlobalTheory.FunObj.even_rank_mul ch.G p hp) _ _
    hsd hsd' (srcU p U U') (tgtU p U U')
  have hst : GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p (r * x) (r' * y) =
        SDLat.smulLat (srcU p U U').1 (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) ∧
      GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p (r * x) (r' * y) =
        SDLat.smulLat (tgtU p U U').1 (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y) := by
    cases p <;> exact ⟨by first | exact hlx | exact hly, by first | exact hlx | exact hly⟩
  have hq : ∀ (q : ℕ) [Fact q.Prime],
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small (r * x)) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big (r' * y)) (stdL D _) →
      GlobalTheory.MovedKappaEx.UnitAt q ε' := by
    intro q _ h1 h2 h3 h4
    rw [hlx] at h3
    rw [hly] at h4
    cases p <;> first
      | exact hu' q h2 h1 h4 h3
      | exact hu' q h1 h2 h3 h4
  refine ⟨ε * ε', GlobalTheory.FamilyTieProof.mod1All_mul' hm hm', fun q _ h1 h2 h3 h4 => unitAt_mul hm hm' (hu q h1 h2 h3 h4) (hq q h1 h2 h3 h4), ?_⟩
  rw [jetKap_iff, hst.1, hst.2]
  have e : (fun z => ε * ((fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)
        (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)
        (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK ch.S.Z.δ) (srcU p U U').1 (tgtU p U U').1 z))) =
      fun z => ε * ε' * κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
        (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (SDLat.smulLat (srcU p U U').1 (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y))
          (SDLat.smulLat (tgtU p U U').1 (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))) (ch.S.Z.e0 p) z := by
    funext z
    simp only
    rw [hB z]
    ring
  rw [e] at hj
  intro k
  rw [hj k]
end GlobalTheory.RatMoveJets
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_jet_move_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (r : FinPt ch.G p.small) (r' : FinPt ch.G p.big), GlobalTheory.MovedKappaEx.RatFin _ r → GlobalTheory.MovedKappaEx.RatFin _ r' →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime],
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small (r * x)) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big (r' * y)) (stdL D _) →
        GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (r * x) (r' * y) (c * κ) := by
  first | exact @_root_.GlobalTheory.RatMoveJets.exists_rational_move_of_jets | exact _root_.GlobalTheory.RatMoveJets.exists_rational_move_of_jets | (intros; apply _root_.GlobalTheory.RatMoveJets.exists_rational_move_of_jets <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtThetaSumAlongLineYDirection
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDerY
theorem hasDerivAt_thetaSum_along_line_y_direction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hG hW γ hγ f f₁ r hR hD u
  by_cases hf : f = 0
  ·
    subst hf
    have hR0 : Rest (evI F) (⇑(0 : SInf F (Fin n × Fin d))) r := hR
    have ht0 : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) r = 0 := by
      funext x; simp [tens]
    have h1 : tens (evI F) (⇑f₁) r = 0 := by
      funext x
      have h := hD r hR0 x
      simp only [ht0, map_zero] at h
      exact (h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))).trans rfl
    have hrho0 : M.co.rho ψ u 0 = 0 := by
      funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hth0 : GlobalTheory.WeilM.thetaSum F (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := by
      simp [GlobalTheory.WeilM.thetaSum]
    simp only [ht0, h1, map_zero, hrho0, hth0]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)
  obtain ⟨c, g, hc, hlim⟩ := _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M ψ χX χW om hψ hG hW γ hγ f r hR
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.ThetaSchrCont.exists_clm_hasSum M ψ hψ u f r hR hf
  have hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r))))
      = fun t => Λ (c t) := by
    funext t
    rw [hc t]
    exact (hΛ (c t)).tsum_eq
  have ev : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      Continuous fun s : SInf F (Fin n × Fin d) => s y := by
    intro y
    have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
    exact (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ) y).comp h1
  have hg : tens (evI F) (⇑g) r = tens (evI F) (⇑f₁) r := by
    funext x
    have h1 := hD r hR x
    have h2 : HasDerivAt (fun t : ℝ => tens (evI F) (⇑(c t)) r x) (tens (evI F) (⇑g) r x) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      refine ((((ev _).tendsto g).comp hlim).mul_const (r x)).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, tens]
      rw [slope_def_module]
      simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
      ring
    have h3 : (fun t : ℝ => tens (evI F) (⇑(c t)) r x) =
        fun t => om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) (⇑f) r) x := by
      funext t; rw [hc t]
    rw [h3] at h2
    exact h2.unique h1
  have hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (tens (evI F) (⇑f₁) r)) = Λ g := by
    rw [← hg]; exact (hΛ g).tsum_eq
  rw [hcurve, hend, hasDerivAt_iff_tendsto_slope]
  refine (Λ.continuous.tendsto g |>.comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp [slope_def_module, map_sub, map_smul]
end GlobalTheory.ThetaLineDerY
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSum_differentiable_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineDerY.hasDerivAt_thetaSum_along_line_y_direction | exact _root_.GlobalTheory.ThetaLineDerY.hasDerivAt_thetaSum_along_line_y_direction | (intros; apply _root_.GlobalTheory.ThetaLineDerY.hasDerivAt_thetaSum_along_line_y_direction <;> assumption)
end
end

