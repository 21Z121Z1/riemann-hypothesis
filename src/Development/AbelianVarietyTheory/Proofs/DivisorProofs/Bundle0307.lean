import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0281
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZero
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory

theorem sqOpen_of_two_ne_zero : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2 : K) ≠ 0 → SqOpen K := by
  intro K _ _ h2 V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  set c := ‖(2:K)⁻¹‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set ρ := min (ε / 2) (1 / (4 * c + 1)) with hρ
  have hρ0 : 0 < ρ := lt_min (by linarith) (by positivity)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρc : 2 * ρ * c ≤ 1 / 2 := by
    have h1 : ρ ≤ 1 / (4 * c + 1) := min_le_right _ _
    have h4 : 0 < 4 * c + 1 := by positivity
    have h5 : ρ * (4 * c + 1) ≤ 1 := by rwa [le_div_iff₀ h4] at h1
    nlinarith
  set δ := ρ / (2 * c + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hcδ : c * δ ≤ ρ / 2 := by
    have h : 0 < 2 * c + 1 := by positivity
    have h' : δ * (2 * c + 1) = ρ := div_mul_cancel₀ _ (ne_of_gt h)
    nlinarith
  refine ⟨Metric.closedBall 1 δ, Metric.closedBall_mem_nhds _ hδ0, ?_⟩
  intro r hr
  have hr' : ‖r - 1‖ ≤ δ := by simpa [dist_eq_norm] using hr
  set f : K → K := fun μ => μ - (μ ^ 2 - r) * (2:K)⁻¹ with hfdef
  have h22 : (2:K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hdiff : ∀ μ₁ μ₂ : K, f μ₁ - f μ₂ = (μ₁ - μ₂) * ((1 - μ₁) + (1 - μ₂)) * (2:K)⁻¹ := by
    intro μ₁ μ₂
    simp only [hfdef]
    linear_combination (-(μ₁ - μ₂)) * h22
  have hf1 : f 1 - 1 = (r - 1) * (2:K)⁻¹ := by
    simp only [hfdef]; ring
  set s := Metric.closedBall (1:K) ρ with hs
  have hlip : ∀ μ₁ ∈ s, ∀ μ₂ ∈ s, ‖f μ₁ - f μ₂‖ ≤ (1 / 2) * ‖μ₁ - μ₂‖ := by
    intro μ₁ h1 μ₂ h2'
    rw [hdiff, norm_mul, norm_mul]
    have a1 : ‖1 - μ₁‖ ≤ ρ := by
      rw [norm_sub_rev]; simpa [hs, dist_eq_norm] using h1
    have a2 : ‖1 - μ₂‖ ≤ ρ := by
      rw [norm_sub_rev]; simpa [hs, dist_eq_norm] using h2'
    have a3 : ‖(1 - μ₁) + (1 - μ₂)‖ ≤ 2 * ρ := (norm_add_le _ _).trans (by linarith)
    have a4 : 0 ≤ ‖μ₁ - μ₂‖ := norm_nonneg _
    have a5 : 0 ≤ ‖(1 - μ₁) + (1 - μ₂)‖ := norm_nonneg _
    calc ‖μ₁ - μ₂‖ * ‖(1 - μ₁) + (1 - μ₂)‖ * c ≤ ‖μ₁ - μ₂‖ * (2 * ρ) * c := by gcongr
      _ = ‖μ₁ - μ₂‖ * (2 * ρ * c) := by ring
      _ ≤ ‖μ₁ - μ₂‖ * (1 / 2) := by gcongr
      _ = (1 / 2) * ‖μ₁ - μ₂‖ := by ring
  have h1s : (1:K) ∈ s := Metric.mem_closedBall_self hρ0.le
  have hmaps : Set.MapsTo f s s := by
    intro μ hμ
    have hl := hlip μ hμ 1 h1s
    have hμ' : ‖μ - 1‖ ≤ ρ := by simpa [hs, dist_eq_norm] using hμ
    have hf1' : ‖f 1 - 1‖ ≤ c * δ := by
      rw [hf1, norm_mul, mul_comm]; gcongr
    have key : ‖f μ - 1‖ ≤ ρ := by
      calc ‖f μ - 1‖ = ‖(f μ - f 1) + (f 1 - 1)‖ := by congr 1; ring
        _ ≤ ‖f μ - f 1‖ + ‖f 1 - 1‖ := norm_add_le _ _
        _ ≤ (1 / 2) * ρ + c * δ := by gcongr; exact hl.trans (by gcongr)
        _ ≤ ρ := by linarith
    simpa [hs, dist_eq_norm] using key
  have hcomplete : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hcon : ContractingWith (1 / 2 : NNReal) (hmaps.restrict f s s) := by
    constructor
    · rw [← NNReal.coe_lt_coe]; push_cast; norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
      push_cast
      exact hlip _ x.2 _ y.2
  obtain ⟨μ, hμs, hfix, -⟩ :=
    hcon.exists_fixedPoint' hcomplete hmaps h1s (edist_ne_top _ _)
  refine ⟨μ, hball (Metric.closedBall_subset_ball hρε hμs), ?_⟩
  have hfix' : f μ = μ := hfix
  have hz : (μ ^ 2 - r) * (2:K)⁻¹ = 0 := by
    simp only [hfdef] at hfix'
    linear_combination -hfix'
  rcases mul_eq_zero.1 hz with h | h
  · linear_combination h
  · exact absurd h (inv_ne_zero h2)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeWeightTwoLatticeSumStatement
section
open NumberField Complex
open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_heckeWeightTwoLatticeSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 → Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by
  first | exact @GlobalTheory.HeckeTwo.summable_latSum | exact GlobalTheory.HeckeTwo.summable_latSum | (intros; apply GlobalTheory.HeckeTwo.summable_latSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHilbertEisensteinWeightTwoQSeriesStatement
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_hilbertEisensteinWeightTwoQSeries : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) := by
  first | exact @GlobalTheory.HeckeTwoSum.summable_qClass | exact GlobalTheory.HeckeTwoSum.summable_qClass | (intros; apply GlobalTheory.HeckeTwoSum.summable_qClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSeminormGaussianConvolutionSeriesTermStatement
section
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_seminorm_gaussianConvolutionSeriesTerm : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ)
    (t : ℕ → SchwartzMap E ℂ), (∀ j y, t j y = GlobalTheory.ConvSeries.term b c h j y) →
    ∀ (k n : ℕ), Summable (fun j => SchwartzMap.seminorm ℂ k n (t j)) := by
  first | exact @GlobalTheory.ConvSeries.summable_seminorm_term | exact GlobalTheory.ConvSeries.summable_seminorm_term | (intros; apply GlobalTheory.ConvSeries.summable_seminorm_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfTraceOfSmulMemRangeStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_injective_of_trace_eq_of_smul_mem_range : ∀ (S A B : Type) [CommRing S] [IsLocalRing S] [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A] [Algebra.Etale S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B] [Algebra.Etale S B] (φ : A →ₐ[S] B), Function.Injective φ → ∀ s : S, s ≠ 0 → (∀ b : B, s • b ∈ φ.range) → (∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x) → Function.Surjective φ := by
  first | exact @GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range | exact GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range | (intros; apply GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticHolPartDetNeZeroAndIsSymmStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by
  first | exact @GlobalTheory.SympBlocks.det_ne_zero_and_isSymm | exact GlobalTheory.SympBlocks.det_ne_zero_and_isSymm | (intros; apply GlobalTheory.SympBlocks.det_ne_zero_and_isSymm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIsLocalRingOfUniquePrimeOverStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [IsLocalRing L] [Algebra.IsIntegral P T] (𝔐 : Ideal T) [𝔐.IsPrime],
    𝔐.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) →
    (∀ 𝔔 : Ideal T, 𝔔.IsPrime → 𝔔.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) → 𝔔 = 𝔐) →
    (∀ y : L, ∃ a : P, y - algebraMap P L a ∈ maximalIdeal L) →
    IsLocalRing (TensorProduct P T L) := by
  first | (exact @GlobalTheory.tensor_isLocalRing_of_unique_prime_over) | (exact GlobalTheory.tensor_isLocalRing_of_unique_prime_over) | (intros; apply GlobalTheory.tensor_isLocalRing_of_unique_prime_over  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLocalizationAtPrimeIsDomainOfIsLocalRingEtStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale : ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R] [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
    IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) → IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  first | (exact @GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (exact GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (intros; apply GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionIntertwiningStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_projection_intertwining : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (f : RL p O Λ →+* O) (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (π π' : (Fin h → C) →ₗ[C] (Fin N → C)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) (Y : Matrix (Fin N) (Fin N) (RL p O Λ)), IsProj C e f π → IsProj C e' f π' → IsMat e e' X Y → ∀ z, π' (redC C X z) = Y.map ((algebraMap O C).comp f) *ᵥ π z := by
  first | exact @GlobalTheory.DetInv.proj_redC_intertwine | exact GlobalTheory.DetInv.proj_redC_intertwine | (intros; apply GlobalTheory.DetInv.proj_redC_intertwine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopMulDescendedSubmoduleOfUnitCocycleEqTop
section
open TensorProduct GlobalTheory.EtC

namespace GlobalTheory.DescTop

theorem top_mul_descMod_eq_top (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (u : (B ⊗[A] B)ˣ) (hu : UCoc A B u) : (⊤ : Submodule A B) * descMod A B u = ⊤ := by
  set F : B →ₗ[A] B ⊗[A] B := (LinearMap.mulLeft A (u : B ⊗[A] B)) ∘ₗ
    (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap with hF
  set G : B →ₗ[A] B ⊗[A] B := (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap with hG
  set f13 := Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  set f12 := Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)
  set f23 := (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))
  have hD : descMod A B u = LinearMap.ker (F - G) := by
    rw [← LinearMap.eqLocus_eq_ker_sub]; rfl
  have hLF : LinearMap.lTensor B F = (LinearMap.mulLeft A (f23 (u : B ⊗[A] B))) ∘ₗ f13.toLinearMap := by
    apply TensorProduct.ext'
    intro c b
    simp [hF, f23, f13, Algebra.TensorProduct.tmul_mul_tmul]
  have hLG : LinearMap.lTensor B G = f12.toLinearMap := by
    apply TensorProduct.ext'
    intro c b
    simp [hG, f12]

  have hinv : f23 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) := by
    have h1 : f13 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : f12 (u : B ⊗[A] B) * f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hc : f13 (u : B ⊗[A] B) = f12 (u : B ⊗[A] B) * f23 (u : B ⊗[A] B) := hu
    calc f23 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)
        = f23 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) *
            (f12 (u : B ⊗[A] B) * f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)) := by rw [h2, mul_one]
      _ = (f13 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)) * f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) := by
            rw [hc]; ring
      _ = f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) := by rw [h1, one_mul]
  have hex := Module.Flat.lTensor_exact B (LinearMap.exact_subtype_ker_map (F - G))
  have hy : ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) ∈
      LinearMap.range (LinearMap.lTensor B (LinearMap.ker (F - G)).subtype) := by
    rw [← hex.linearMap_ker_eq, LinearMap.mem_ker, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero,
      hLF, hLG]
    simpa using hinv
  obtain ⟨z, hz⟩ := hy
  have hmem : ∀ w : B ⊗[A] LinearMap.ker (F - G),
      Algebra.TensorProduct.lmul' A (LinearMap.lTensor B (LinearMap.ker (F - G)).subtype w) ∈
        (⊤ : Submodule A B) * descMod A B u := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
      exact Submodule.mul_mem_mul Submodule.mem_top (by rw [hD]; exact m.2)
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  have hv := hmem z
  rw [hz] at hv
  set v := Algebra.TensorProduct.lmul' A (((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)) with hvdef
  have hvu : IsUnit v := (Units.isUnit (u⁻¹)).map (Algebra.TensorProduct.lmul' A (S := B))
  obtain ⟨w, hw⟩ := hvu.exists_left_inv
  have hle : (⊤ : Submodule A B) * ((⊤ : Submodule A B) * descMod A B u) ≤ (⊤ : Submodule A B) * descMod A B u := by
    rw [← mul_assoc]; first
      | exact Submodule.mul_le_mul le_top le_rfl
      | exact mul_le_mul_right' le_top _
      | (gcongr; exact le_top)
  rw [eq_top_iff]
  intro b _
  have : b = (b * w) * v := by rw [mul_assoc, hw, mul_one]
  rw [this]
  exact hle (Submodule.mul_mem_mul Submodule.mem_top hv)

end GlobalTheory.DescTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointRowSumEqQExpansionSeriesStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (b : ZMod N) (d : ℕ+), 1 ≤ e → (∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * ch N (((j : ℕ) : ZMod N) * b) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) ∧ ∑' m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ((-1) ^ (e + 1) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * ch N (-(((j : ℕ) : ZMod N) * b)) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) := by
  first | exact @GlobalTheory.WpFam.torsion_row_series | exact GlobalTheory.WpFam.torsion_row_series | (intros; apply GlobalTheory.WpFam.torsion_row_series <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorBaseChangeZmod
section
open CategoryTheory Limits
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocAcyc

def zmodTensorAct (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type)
    [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)) :
    Multiplicative (ZMod q) →* (B ⊗[U] D ≃ₐ[B] B ⊗[U] D) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add]
  map_mul' g h := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add]

@[simp] theorem zmodTensorAct_tmul (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (b : B) (x : D) (g : Multiplicative (ZMod q)) :
    zmodTensorAct U B q D act g (b ⊗ₜ x) = b ⊗ₜ act g x := by simp [zmodTensorAct]

theorem isZModTorsor_tensorBase (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (hq : 0 < q) (hD : IsZModTorsor U D q act) :
    IsZModTorsor B (B ⊗[U] D) q (zmodTensorAct U B q D act) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨h1, h2, h3, h4⟩ := hD
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id U D))
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) with hΦ
  set ΦB := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D) (fun _ => AlgHom.id B (B ⊗[U] D)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D)
        (fun g => (zmodTensorAct U B q D act g).toAlgHom)) with hΦB
  let e1 := TensorProduct.AlgebraTensorModule.distribBaseChange U B D D
  let L := (LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B
  let e2 := TensorProduct.piRight U U B (fun _ : Multiplicative (ZMod q) => D)
  have key : ∀ z, ΦB (e1 z) = e2 (L z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        funext g
        simp [e1, L, e2, hΦ, hΦB, Algebra.TensorProduct.productMap_apply_tmul]
      | add w w' hw hw' =>
        simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | add z w hz hw => simp only [map_add, hz, hw]
  have : (ΦB : _ → _) = e2 ∘ L ∘ e1.symm := by
    funext w
    simpa using key (e1.symm w)
  rw [this]
  exact e2.bijective.comp (L.bijective.comp e1.symm.bijective)

theorem exists_isZModTorsor_tensorBase : ∀ (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type) [CommRing D]
    [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)), 0 < q →
    GlobalTheory.LocAcyc.IsZModTorsor U D q act →
    ∃ actB : Multiplicative (ZMod q) →* (TensorProduct U B D ≃ₐ[B] TensorProduct U B D),
      GlobalTheory.LocAcyc.IsZModTorsor B (TensorProduct U B D) q actB :=
  fun U B _ _ _ q D _ _ act hq hD => ⟨_, isZModTorsor_tensorBase U B q D act hq hD⟩

end GlobalTheory.LocAcyc
end
end

