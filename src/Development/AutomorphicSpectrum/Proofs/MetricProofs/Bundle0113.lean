import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AffineChartIdealPrimeAndSaturated
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0103
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQContinuousAtAndLocalSolution
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQHermitianAndRealPairing
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentSpanRelIndexCriterion
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AffineChartIdealPrimeAndSaturatedStatement
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_chart_ideal_prime_and_saturated : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k), IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → (SncRes.ideal Q p).IsPrime ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a → (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareXiIntersectionStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_square_xi_intersection : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ T : Fin (d + 1) → HermLine Q.ιW, (∀ j, IsSmoothHerm (T j)) → II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₀ (Fin.cons X₀ T)) - II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₁ (Fin.cons X₁ T)) = 2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.algebraic_square_xi_intersection | exact GlobalTheory.CompanionTheory.Relay.algebraic_square_xi_intersection | (intros; apply GlobalTheory.CompanionTheory.Relay.algebraic_square_xi_intersection <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AmpleOnGenericFibreOfSemipositive
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (N A : HermLine J) (a' : K → ℤ) (m p : ℕ), IsSemipositiveH P N → IsSmoothHerm A → (∀ k, 0 < a' k) → 1 ≤ m → 1 ≤ p → (m : ℤ) • A.a = N.a + (p : ℤ) • a' → AmpleOnGenericFibre P A := by
  first | exact @LevelTowerAlt.ample_generic_fibre_of_combination | exact LevelTowerAlt.ample_generic_fibre_of_combination
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundaryOnPrimes
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead

theorem aeval_eq_image {σ E : Type} [CommRing E] [Algebra ℚ E] (π : MvPolynomial σ ℂ →+* E)
    (G : MvPolynomial σ ℚ) :
    aeval (fun q => π (X q)) G = π (map (algebraMap ℚ ℂ) G) := by
  have h : (aeval (fun q => π (X q)) : MvPolynomial σ ℚ →ₐ[ℚ] E).toRingHom =
      π.comp (map (algebraMap ℚ ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact DFunLike.congr_fun (RingHom.ext_rat
        ((aeval (fun q => π (X q)) : MvPolynomial σ ℚ →ₐ[ℚ] E).toRingHom.comp C)
        ((π.comp (map (algebraMap ℚ ℂ))).comp C)) r
    · intro i
      simp
  exact DFunLike.congr_fun h G

theorem aeval_int_eq {σ Ω : Type} [CommRing Ω] [Algebra ℚ Ω] (τ : σ → Ω)
    (g : MvPolynomial σ ℤ) : aeval τ g = aeval τ (map (Int.castRingHom ℚ) g) := by
  have h : (aeval τ : MvPolynomial σ ℤ →ₐ[ℤ] Ω).toRingHom =
      (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom.comp (map (Int.castRingHom ℚ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact DFunLike.congr_fun (RingHom.ext_int
        ((aeval τ : MvPolynomial σ ℤ →ₐ[ℤ] Ω).toRingHom.comp C)
        (((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom.comp
          (map (Int.castRingHom ℚ))).comp C)) r
    · intro i
      simp
  exact DFunLike.congr_fun h g

theorem map_map_int {σ : Type} (g : MvPolynomial σ ℤ) :
    map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℂ) g := by
  rw [MvPolynomial.map_map,
    RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ)]

theorem read_in_field {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (τ : σ → Ω)
    (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (Js : Set (MvPolynomial σ ℤ)) (e n : ℕ)
    (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ)
    (hF : aeval τ F ≠ 0) (hS : S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)))
    (hz : ∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i))
    (hprime : ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q))
    (𝔮 : Ideal (MvPolynomial σ ℂ))
    (hker : ∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ 𝔮)
    (hFq : map (algebraMap ℚ ℂ) F ∉ 𝔮)
    (E : Type) [Field E] [Algebra ℚ E] (π : MvPolynomial σ ℂ →+* E)
    (hπ : ∀ p, π p = 0 ↔ p ∈ 𝔮) :
    (∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮 := by
  have hau : ∀ G : MvPolynomial σ ℚ,
      aeval (fun q => π (X q)) G = π (map (algebraMap ℚ ℂ) G) := aeval_eq_image π
  have hunit : IsUnit (aeval (fun q => π (X q)) F) := by
    rw [hau]
    exact IsUnit.mk0 _ (fun h => hFq ((hπ _).1 h))
  obtain ⟨φ, hφ⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.Kext.exists_algHom_adjoin_inv Ω σ τ F S E (fun q => π (X q)) hF hS
    (fun G hG => by rw [hau]; exact (hπ _).2 (hker G hG)) hunit
  have hτS : ∀ q, τ q ∈ S := fun q => by
    rw [hS]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)
  let τS : σ → S := fun q => ⟨τ q, hτS q⟩
  have hcoe : ∀ G : MvPolynomial σ ℚ, ((aeval τS G : S) : Ω) = aeval τ G := by
    intro G
    have h : S.val.comp (aeval τS) = aeval τ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [τS]
    exact DFunLike.congr_fun h G
  have hq : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmem : ∀ s, s ∈ RingHom.ker φ ↔ φ s = 0 := fun s => RingHom.mem_ker
  have hleft : (∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔
      (∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ RingHom.ker φ) := by
    constructor
    · intro h g hg s hs
      rw [hmem, hφ (map (Int.castRingHom ℚ) g) s (by rw [hs, aeval_int_eq]), hau, map_map_int]
      exact (hπ _).2 (h g hg)
    · intro h g hg
      have hs := hcoe (map (Int.castRingHom ℚ) g)
      have h0 := h g hg (aeval τS (map (Int.castRingHom ℚ) g)) (by rw [hs, aeval_int_eq])
      rw [hmem, hφ _ _ hs, hau, map_map_int] at h0
      exact (hπ _).1 h0
  have hright : ∀ i, z i ∈ RingHom.ker φ ↔ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮 := by
    intro i
    have hzi : φ (z i * (aeval τS F) ^ N i) = aeval (fun q => π (X q)) (Z i) :=
      hφ _ _ (by push_cast; rw [hcoe, hz])
    have hfS : φ (aeval τS F) = aeval (fun q => π (X q)) F := hφ _ _ (hcoe F)
    rw [map_mul, map_pow, hfS] at hzi
    have hf0 : aeval (fun q => π (X q)) F ≠ 0 := hunit.ne_zero
    rw [hmem, ← hπ, ← hau, ← hzi]
    simp [hf0]
  rw [hleft, hprime _ hq]
  exact exists_congr fun i => and_congr_right fun _ => hright i

theorem boundary_on_primes : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (Js : Set (MvPolynomial σ ℤ)) (e n : ℕ) (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ), aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) → (∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i)) → (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → ∀ 𝔮 : Ideal (MvPolynomial σ ℂ), 𝔮.IsPrime → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ 𝔮) → map (algebraMap ℚ ℂ) F ∉ 𝔮 → ((∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮) := by
  intro Ω _ _ σ τ F S Js e n z Z N hF hS hz hprime 𝔮 h𝔮 hker hFq
  have : IsDomain (MvPolynomial σ ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let π : MvPolynomial σ ℂ →+* FractionRing (MvPolynomial σ ℂ ⧸ 𝔮) :=
    (algebraMap (MvPolynomial σ ℂ ⧸ 𝔮) (FractionRing (MvPolynomial σ ℂ ⧸ 𝔮))).comp
      (Ideal.Quotient.mk 𝔮)
  have hπ : ∀ p, π p = 0 ↔ p ∈ 𝔮 := by
    intro p
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let _ : Algebra ℚ (FractionRing (MvPolynomial σ ℂ ⧸ 𝔮)) :=
    (π.comp ((C : ℂ →+* MvPolynomial σ ℂ).comp (algebraMap ℚ ℂ))).toAlgebra
  exact read_in_field τ F S Js e n z Z N hF hS hz hprime 𝔮 hker hFq _ π hπ

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQContinuousAtAndLocalSolutionStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartQ_continuousAt_and_local_solution : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) (Pr : Matrix (Fin g) (Fin g) ℝ), IsChart L bas A T0 B c ρ → IsKerProj (∑ j, B j) Pr → ContinuousAt (chartQ Pr A T0) 0 ∧ ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ w ∈ logCover L.a_le, ‖expCover a w‖ < ρ' → ∀ y : Fin g → ℂ, ∃ p : Fin g → ℂ, p - y ∈ Submodule.span ℂ {u | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) ∧ u = L.P w x} ∧ (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) → p ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w x) = 0) ∧ ∀ y' : Fin g → ℂ, y' ⬝ᵥ L.H (expCover a w) *ᵥ star p = y' ⬝ᵥ chartQ Pr A T0 (expCover a w) *ᵥ star y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQHermitianAndRealPairingStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartQ_hermitian_and_real_pairing : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) (Pr : Matrix (Fin g) (Fin g) ℝ), IsChart L bas A T0 B c ρ → IsKerProj (∑ j, B j) Pr → (chartQ Pr A T0 0).IsHermitian ∧ (∀ x x' : chartW bas B, (chartPer bas A T0 B x ⬝ᵥ chartQ Pr A T0 0 *ᵥ star (chartPer bas A T0 B x')).im = L.E x x') ∧ (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) → chartQ Pr A T0 0 *ᵥ star (chartPer bas A T0 B x) = 0) ∧ ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ chartQ Pr A T0 0 *ᵥ star v).re ∧ ((v ⬝ᵥ chartQ Pr A T0 0 *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) ∧ p = chartPer bas A T0 B x}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm.limit_form | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm.limit_form | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm.limit_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentSpanRelIndexCriterionStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenComponent_span_relIndex_criterion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ) (s₀ : 𝓞 E →+* ℂ) (r k : ℕ) (y : Fin r → Λ) (q p : Fin k → Fin g → ℂ), (∀ a, y a ∈ I) → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → (∀ c, q c ∈ eigSp R.B s₀) → (∀ c, p c - q c ∈ Submodule.span ℂ (R.P '' (I : Set Λ))) → (∀ c, ∀ x ∈ I, R.ip (R.P x) (p c) = 0) → (R.gram (Fin.append (fun a => eigComp R.B s₀ (R.P (y a))) q)).det = (R.gram fun a => eigComp R.B s₀ (R.P (y a))).det * (Matrix.of fun c c' => R.ip (p c) (q c')).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.IsoSplit.gram_append_split | exact GlobalTheory.CompanionTheory.Ar.Cusp.IsoSplit.gram_append_split | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.IsoSplit.gram_append_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolutionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_rows_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBlockFieldEq
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

theorem x_chart_ne_of_pt (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk}
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF : M.GoodAt F (mCoordIdeal zb))
    (k : NonPluckerBlocks M.blk) : M.x ⟨k, F.c k⟩ ≠ 0 := fun h => hF.1 k (by
  have h1 : (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∈ mCoordIdeal M.x := by
    show mConeMap M.x (X ⟨k, F.c k⟩) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h2 : zb ⟨k, F.c k⟩ = 0 := by simpa using hz.2 _ h1
  show mConeMap zb (X ⟨k, F.c k⟩) = 0
  rw [mConeMap, aeval_X, h2, map_zero, zero_mul])

theorem transPt_ratio_base [CharZero Φ'] {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (k : K) (h : ∀ p, M.blk p ≠ some k) (i i₂ : ι k) :
    transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y' := by
  have e : ∀ m : ι k, transPt Cv ⟨k, m⟩ = y' ⟨(Cv.v ⟨⟨k, h⟩, m⟩).1.1, (Cv.v ⟨⟨k, h⟩, m⟩).2⟩ := fun m => by
    have h1 := transPt_base Cv ⟨⟨k, h⟩, m⟩
    rw [← Cv.x_eq, ← M'.y_base] at h1
    exact h1
  rw [e, e]
  refine IntermediateField.subset_adjoin _ _ ⟨_, _, ?_, rfl⟩
  show (Cv.v ⟨⟨k, h⟩, i⟩).1.1 = (Cv.v ⟨⟨k, h⟩, i₂⟩).1.1
  rw [Cv.block.2.2.1, Cv.block.2.2.1]

theorem transPt_ratio_step [CharZero Φ'] {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (hy : ∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (i i₂ : ι k) :
    transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y' := by
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' := by
    rcases e : M'.blk p with _ | k'
    · have h2 := (M.blk_none p).2 ((M'.blk_none p).1 e)
      rw [hp] at h2
      cases h2
    · exact ⟨k', rfl⟩
  obtain ⟨zb, hzb⟩ := GlobalTheory.T.multiprojective_points_nonempty _ _ _ M'.x M'.x_ne
  have hzv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  obtain ⟨F', hF', hG'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 zb hzb
  obtain ⟨F, hF, hG⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hzv
  obtain ⟨c, hc, hcs⟩ := GlobalTheory.T.flag_cover_frames_pullback K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF
    (fun k => x_chart_ne_of_pt M' hzb hG' k) (fun k => x_chart_ne_of_pt M hzv hG k) p k k' hp hk'
  obtain ⟨c', hc'⟩ := hy k'
  have hreg : ∀ (q : Σ k, ι k) (r : Σ k, ι' k),
      algebraMap M'.Ω Φ' (coE Cv F' F p q r) ∈ blockFnField y' := fun q r =>
    GlobalTheory.T.regular_function_in_block_field K' ι' Φ' y' Ψ N j M' zb _ hzb
      (GlobalTheory.T.flag_cover_frames_at_base_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb F' F hzb hF' hF hG' hG p q r).1
  let S : ι k → Φ' := fun m =>
    ∑ m' : ι' k', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
  have hS : ∀ m, S m ∈ blockFnField y' := fun m =>
    sum_mem fun m' _ => mul_mem (hreg _ _) (IntermediateField.subset_adjoin _ _ ⟨⟨k', m'⟩, ⟨k', c'⟩, rfl, rfl⟩)
  have e : ∀ m, transPt Cv ⟨k, m⟩ = (c * y' ⟨k', c'⟩) * S m := fun m => by
    rw [hcs m, mul_assoc]
    congr 1
    simp only [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  rw [e, e, mul_div_mul_left _ _ (mul_ne_zero hc hc')]
  exact div_mem (hS _) (hS _)

end

theorem blockFnField_pair_transPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) [CharZero Φ'], (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y' = blockFnField (pairV (transPt Cv) y') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv _ hy
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨p, q, h, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨inrV p, inrV q, by simp only [inrV, h], rfl⟩
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨⟨k | k, i⟩, ⟨k₂ | k₂, i₂⟩, h, rfl⟩
    · obtain rfl : k = k₂ := Sum.inl.inj h
      show transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y'
      by_cases hb : ∀ p, M.blk p ≠ some k
      · exact transPt_ratio_base Cv k hb i i₂
      · exact transPt_ratio_step Cv hy (stepOf M k hb) k (blk_stepOf M k hb) i i₂
    · cases h
    · cases h
    · obtain rfl : k = k₂ := Sum.inr.inj h
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, ⟨k, i₂⟩, rfl, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesLiftPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem coord_ne (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k} (hq : (X q : MRing ι) ∉ mCoordIdeal z) :
    x q ≠ 0 := fun h => hq (by
  have hm : (X q : MRing ι) ∈ mCoordIdeal x := by
    show mConeMap x (X q) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h0 : z q = 0 := by simpa using hz.2 _ hm
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

theorem isValueAt_sum {α : Type} (S : Finset α) (f : α → Ω) (v : α → ℂ)
    (h : ∀ i ∈ S, IsValueAt x (f i) z (v i)) : IsValueAt x (∑ i ∈ S, f i) z (∑ i ∈ S, v i) := by
  induction S using Finset.induction_on with
  | empty => simpa using ValRing.isValueAt_zero_self x z
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ValRing.isValueAt_add (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isValueAt_valAt (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    IsValueAt x s z (valAt x s z) := by
  obtain ⟨v, hv⟩ := ValRing.exists_isValueAt hz hs
  rw [valAt_eq hz hv]
  exact hv

theorem valAt_sum_mul (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (S : Finset α) (f g : α → Ω)
    (hf : ∀ i ∈ S, RegAt x (mCoordIdeal z) (f i)) (hg : ∀ i ∈ S, RegAt x (mCoordIdeal z) (g i)) :
    valAt x (∑ i ∈ S, f i * g i) z = ∑ i ∈ S, valAt x (f i) z * valAt x (g i) z :=
  valAt_eq hz (isValueAt_sum S _ _ fun i hi =>
    isValueAt_mul (isValueAt_valAt hz (hf i hi)) (isValueAt_valAt hz (hg i hi)))

end Values

theorem stepCols_ne {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · have hlt : N - j < N := by omega
    have hm : (⟨N - j, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
      omega
    rw [e] at hm
    simp at hm
  · have hm : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
      omega
    rw [e] at hm
    simp at hm

theorem read_minor {κ : Type} [Fintype κ] {N : ℕ} (P : Finset (Fin N) → Prop)
    (A : Finset (Fin N) → κ → ℂ) (B : κ → Finset (Fin N) → ℂ)
    (hAB : ∀ I I', P I → P I' → ∑ m, A I m * B m I' = if I = I' then 1 else 0)
    (μ : Finset (Fin N) → ℂ) (hμ : ∀ I, ¬ P I → μ I = 0) (w : κ → ℂ) (a : ℂ)
    (hw : ∀ m, w m = a * ∑ I, B m I * μ I) (I' : Finset (Fin N)) (hI' : P I') :
    ∑ m, A I' m * w m = a * μ I' := by
  have e : ∑ m, A I' m * w m = a * ∑ I, (∑ m, A I' m * B m I) * μ I := by
    simp only [hw, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e, Finset.sum_eq_single I']
  · rw [hAB I' I' hI' hI', if_pos rfl, one_mul]
  · intro I _ hne
    by_cases hI : P I
    · rw [hAB I' I hI' hI, if_neg hne.symm, zero_mul]
    · rw [hμ I hI, mul_zero]
  · simp

theorem move_minor {κ : Type} [Fintype κ] {N : ℕ} (P : Finset (Fin N) → Prop)
    (S : Finset (Finset (Fin N))) (hS : ∀ I, I ∈ S ↔ P I) (A : Finset (Fin N) → κ → ℂ)
    (D : Finset (Fin N) → ℂ) (Tm : Finset (Fin N) → Finset (Fin N) → ℂ)
    (μ : Finset (Fin N) → ℂ) (hμ : ∀ I, ¬ P I → μ I = 0) (w : κ → ℂ) (a : ℂ)
    (hA : ∀ I', P I' → ∑ m, A I' m * w m = a * μ I') :
    ∑ m, (∑ I, ∑ I' ∈ S, D I * Tm I I' * A I' m) * w m = a * ∑ I, D I * ∑ I', Tm I I' * μ I' := by
  have e : ∑ m, (∑ I, ∑ I' ∈ S, D I * Tm I I' * A I' m) * w m =
      ∑ I, ∑ I' ∈ S, D I * Tm I I' * ∑ m, A I' m * w m := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ S) fun I' _ h => by
    rw [hμ I' fun hp => h ((hS I').2 hp), mul_zero], Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun I' h => by rw [hA I' ((hS I').1 h)]; ring

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), z₁ ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) → M'.IsFlagOf F' z₁ h → M.IsFlagOf F z₀ (fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ) → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → M.blk p = some k → ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ m, transPt Cv ⟨k, m⟩ = e * s m ∧ IsValueAt y' (s m) z₁ (t * z₀ ⟨k, m⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG' hG hfl' hfl horb hp
  set zb := basePart M'.blk z₁ with hzbdef
  have hzb : zb ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z₁ hz₁
  have hzv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  have hstep : IsProperStep N j p.2 := by
    by_contra hn
    rw [(M.blk_none p).2 hn] at hp
    exact absurd hp (by simp)
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' :=
    Option.ne_none_iff_exists'.1 fun e => (M'.blk_none p).1 e hstep
  obtain ⟨c', hc'⟩ := hz₁.1 k'
  obtain ⟨hy0, hratio⟩ := GlobalTheory.T.coordinate_ratio_value_at_point K' ι' Φ' y' z₁ k' c' hz₁ hc'
  have ch' : ∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0 := fun k => coord_ne hzb (hG'.1 k)
  have ch : ∀ k, M.x ⟨k, F.c k⟩ ≠ 0 := fun k => coord_ne hzv (hG.1 k)
  obtain ⟨c, hc0, htr⟩ :=
    GlobalTheory.T.flag_cover_frames_pullback K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF ch' ch p k k' hp hk'
  obtain ⟨a', ha', hz1⟩ := hfl'.2.2 p k' hk'
  obtain ⟨a, ha, hz0⟩ := hfl.2.2 p k hp
  have hE := fun m m' =>
    GlobalTheory.T.flag_cover_frames_at_base_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb F' F hzb hF' hF hG' hG p ⟨k, m⟩ ⟨k', m'⟩
  have hmin := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hne : stepCols N j p.2 ≠ ∅ := stepCols_ne p.2 M.j_le
  obtain ⟨cc, hcc, horbE⟩ := horb
  have hval : ∀ s, valAt M.x s (basePart M.blk z₀) = valAt M.x s (zb ∘ Cv.v) := fun s => by
    rw [horbE]
    exact ((StepW.TorusAct.main _ _ _ M.x (zb ∘ Cv.v) cc hcc).2 hzv).2 s
  have hμ : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ (h p.1) I (stepCols N j p.2) = 0 := fun I hI =>
    (hmin.2.1 (h p.1) I (hfl'.2.1 p.1).1 hI).resolve_right hne
  have hAB : ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
      ∑ m, valAt M'.x (F'.u' I ⟨k', m⟩) zb * valAt M'.x (F'.u ⟨k', m⟩ I') zb =
        if I = I' then 1 else 0 := fun I I' hI hI' => by
    rw [← valAt_sum_mul hzb Finset.univ _ _ (fun m _ => (hG'.2.1 ⟨k', m⟩ I).2)
      (fun m _ => (hG'.2.1 ⟨k', m⟩ I').1), hF'.2.2.1 p k' hk' I I' hI hI']
    have h3 := ValRing.regAt_valAt_ring _ _ _ M'.x zb hzb
    split_ifs
    · exact h3.2.2.2.1
    · exact h3.2.2.1
  have hread := read_minor (IsStepRows N j p.2) _ _ hAB _ hμ (fun m => z₁ ⟨k', m⟩) a' hz1
  have key : ∀ m, ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ =
      a' * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (zb ∘ Cv.v) *
        minorIJ (Cv.trans F' F zb p.1 * h p.1) I (stepCols N j p.2) := fun m => by
    simp only [fun m' => (hE m m').2, hmin.1]
    exact move_minor (IsStepRows N j p.2) _ (fun I => by simp) _ _ _ _ hμ _ a' hread
  refine ⟨c * y' ⟨k', c'⟩, fun m => ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
    (y' ⟨k', m'⟩ / y' ⟨k', c'⟩), a' / (a * z₁ ⟨k', c'⟩), mul_ne_zero hc0 hy0,
    div_ne_zero ha' (mul_ne_zero ha hc'), fun m => ⟨?_, ?_⟩⟩
  · show transPt Cv ⟨k, m⟩ = c * y' ⟨k', c'⟩ * ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
      (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
    rw [htr m, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  · have hv := isValueAt_sum Finset.univ
      (fun m' => algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩))
      (fun m' => valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩))
      fun m' _ => isValueAt_mul (GlobalTheory.T.base_function_value_at_point K' ι' Φ' y' Ψ N j M' z₁ _ hz₁ hzb (hE m m').1) (hratio m')
    have e : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
        a' / (a * z₁ ⟨k', c'⟩) * z₀ ⟨k, m⟩ := by
      have e1 : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
          (z₁ ⟨k', c'⟩)⁻¹ * ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m' _ => by ring
      rw [e1, key m, hz0 m]
      simp only [hval]
      field_simp
    rw [← e]
    exact hv

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDomainCellCoordinatesStatement
section
open MeasureTheory Filter Topology Matrix NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_domain_cell_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j e : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (Ψ : Type) [Fintype Ψ] (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e), IsOrth X x0 → j ≤ r → X.p0 = r - j → (∀ z : Fin e → ℂ, z ∈ cellDom j q ↔ (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ OmF X x0) ∧ ∀ FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X)), MeasurableSet FF → FF ⊆ OmF X x0 → muF X x0 FF = cellVol j q {z | (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ FF} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.muF_orth_eq_cellVol | exact GlobalTheory.CompanionTheory.Ar.Cmp.muF_orth_eq_cellVol | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.muF_orth_eq_cellVol <;> assumption)
end

