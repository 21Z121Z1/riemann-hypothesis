import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.RootSurvey.GeometrySurvey.ExistsTopDegreeCoefficientFormAndEqOnTopForms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0017
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaTermLogDegreeBound
section
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem deltaTerm_one : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  intro Ψ _ _ N j p τ fr hj hp
  refine ⟨Bound₂.ep N j p fr, Bound₂.abs_ep_le hj hp fr, fun h => ?_, fun h => ?_,
    fun Q => Bound₂.delta_one hj p τ fr Q⟩
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1) := by
      funext n
      obtain ⟨σ, hσ⟩ := h n
      rw [hσ, inv_pow, div_eq_inv_mul]
      rfl
    unfold Bound₂.ep
    rw [e, (ep_split p j hp).tsum_eq, sub_self]
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1) := by
      funext n
      rw [inv_pow, div_eq_inv_mul]
      congr 1
      rcases hs : fr n with σ | σ
      · have : Odd n := (h n).1 ⟨σ, hs⟩
        rw [if_pos this.add_one]
        rfl
      · have : ¬ Odd n := fun ho => by
          obtain ⟨σ', h'⟩ := (h n).2 ho
          rw [hs] at h'
          cases h'
        rw [if_neg (by simpa [Nat.even_add_one] using this)]
        rfl
    unfold Bound₂.ep
    rw [e, (ep_inert p N j hp hj).1.tsum_eq]
    ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DotDualLatticeFamily
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem dotDual_latFamily : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) :=
  @PositivityTheory.Xgn.dual_lattice_family

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrLocalizationConstants
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chart_points_over_place : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) :=
  @PositivityTheory.Xgn.lattice_chart_points

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsometricHermLine
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem twist_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A : HermLine ι, A.a = T.x () → IsSmoothHerm A → IsConjInvariantH A → ∃ A' : HermLine ι, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ T.IsIsometric P (fun _ => A) (fun _ => A') := by
  intro K _ _ ι _ P D hP S T hT A hAx hAs hAc
  obtain ⟨_, ⟨hPp, hPh, _⟩, _, _⟩ := hP
  have hPh' := GlobalTheory.T.isMultiHomogIdeal_transfer K ι P hPh
  obtain ⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hW⟩ := hT ()
  generalize hfd : T.f () = f at *
  generalize hgd : T.g () = g at *
  let Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop :=
    fun a b u v => GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u * f - v * g ∈ P
  have hQmul : ∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m) := by
    rintro a b d u v m ⟨hu, hv, hab, hr⟩ hm
    refine ⟨hu.mul hm, hv.mul hm, ?_, ?_⟩
    · rw [add_right_comm, hab, add_right_comm]
    · have : u * m * f - v * m * g = m * (u * f - v * g) := by ring
      rw [this]
      exact P.mul_mem_left _ hr
  have hcompP : ∀ z ∈ mcPts P, ∀ (a : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℤ),
      eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0 → s ∉ P := fun z hz _ s hs hm =>
    hs (hz.2 s hm)
  have hin : ∀ z ∈ mcPts P, (∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) ∧
      (∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) := by
    intro z hz
    obtain ⟨W, hWp, hPW, hWr, hWc, hWs⟩ := GlobalTheory.T.relevant_prime_over_multihomog K ι P z hPh' hz
    obtain ⟨u₀, v₀, hu₀, hv₀, hr⟩ := hW W hWp hPW hWr (fun p _ => hWc p)
    constructor
    · obtain ⟨a, ha⟩ := hWs u₀ hu₀
      obtain ⟨b, v, hv, hab, hr'⟩ := GlobalTheory.T.multihomog_component_quotient K ι P hPp hPh' f g u₀ v₀ bf bg a hf hg hfP hr
        (hcompP z hz a _ ha)
      exact ⟨a, b, _, v, ⟨weightedHomogeneousComponent_isWeightedHomogeneous a u₀, hv, hab, hr'⟩, ha⟩
    · obtain ⟨b, hb⟩ := hWs v₀ hv₀
      have hr₂ : v₀ * g - u₀ * f ∈ P := by
        have := P.neg_mem hr
        rwa [neg_sub] at this
      obtain ⟨a, u, hu, hab, hr'⟩ := GlobalTheory.T.multihomog_component_quotient K ι P hPp hPh' g f v₀ u₀ bg bf b hg hf hgP hr₂
        (hcompP z hz b _ hb)
      refine ⟨a, b, u, _, ⟨hu, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hab.symm, ?_⟩, hb⟩
      have := P.neg_mem hr'
      rwa [neg_sub] at this
  have hout : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → z ∉ mcPts P →
      ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
    intro z hc hz
    have : ∃ q ∈ P, eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hz ⟨hc, hne⟩
    obtain ⟨q, hq, hqz⟩ := this
    obtain ⟨a, b, u, v, hu, hv, hab, huP, hvP, huz, hvz⟩ := GlobalTheory.T.multihomog_nonvanishing_ratio K ι P bf bg z q hPh' hc hq hqz
    refine ⟨a, b, u, v, ⟨hu, hv, hab, ?_⟩, huz, hvz⟩
    exact P.sub_mem (P.mul_mem_right _ huP) (P.mul_mem_right _ hvP)
  obtain ⟨Aₐ, B, n, u, v, hAB, hQ, hu, hv⟩ := GlobalTheory.T.multihomog_ratio_induction K ι Q bf bg hQmul (fun a b u v h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun z hc => by
      by_cases hz : z ∈ mcPts P
      · exact (hin z hz).1
      · obtain ⟨a, b, u, v, h, h1, _⟩ := hout z hc hz
        exact ⟨a, b, u, v, h, h1⟩)
    (fun z hc => by
      by_cases hz : z ∈ mcPts P
      · exact (hin z hz).2
      · obtain ⟨a, b, u, v, h, _, h1⟩ := hout z hc hz
        exact ⟨a, b, u, v, h, h1⟩)
  obtain ⟨A', ha', hs', hc', hh'⟩ := GlobalTheory.T.multihomog_covering_forms K ι A Aₐ B n u v (fun j => (hQ j).1) (fun j => (hQ j).2.1)
    hu hv hAs hAc
  refine ⟨A', hs', hc', fun _ => ⟨hAx, ?_, fun z hz => ?_⟩⟩
  · rw [ha', hAx]
    funext k
    have h1 := congrFun hdeg k
    have h2 : (Aₐ k : ℤ) + bf k = B k + bg k := by exact_mod_cast congrFun hAB k
    simp only [Pi.sub_apply] at h1
    linarith
  · show ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.f ()))‖ * A'.h z =
      ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.g ()))‖ * A.h z
    rw [hfd, hgd, hh']
    set fz := eval z (MvPolynomial.map (Int.castRingHom ℂ) f)
    set gz := eval z (MvPolynomial.map (Int.castRingHom ℂ) g)
    have hrel : ∀ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 * ‖fz‖ ^ 2 =
        ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2 * ‖gz‖ ^ 2 := by
      intro j
      have h0 := hz.2 _ (hQ j).2.2.2
      simp only [map_sub, map_mul] at h0
      have h1 := sub_eq_zero.mp h0
      have h2 := congrArg norm h1
      rw [norm_mul, norm_mul] at h2
      rw [← mul_pow, ← mul_pow, h2]
    have hD : 0 < ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2 := by
      obtain ⟨j, hj⟩ := hv z hz.1
      exact Finset.sum_pos' (fun _ _ => by positivity) ⟨j, Finset.mem_univ _, by positivity⟩
    have hsum : (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) * ‖fz‖ ^ 2 =
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2) * ‖gz‖ ^ 2 := by
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => hrel j
    have key : ‖fz‖ * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) = ‖gz‖ := by
      rw [← Real.sqrt_sq (norm_nonneg fz), ← Real.sqrt_mul (by positivity)]
      rw [show ‖fz‖ ^ 2 * ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) = ‖gz‖ ^ 2 by
        field_simp
        linarith]
      exact Real.sqrt_sq (norm_nonneg gz)
    calc ‖fz‖ * (A.h z * _) = (‖fz‖ * Real.sqrt _) * A.h z := by ring
      _ = ‖gz‖ * A.h z := by rw [key]

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsModelVectorBundlesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_vector_bundles : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → ∃ (X' : Scheme.{0}) (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (N : ℕ) (x' : Fin (N + 1) → Ω') (b : ∀ s, Fin (r s) → TensorProduct Ω Ω' E), CoordTie ℤ ξ' x' ∧ (∀ q : X', genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω Ω') ∧ Smooth f ∧ Function.Surjective f ∧ IsGenericFlag (Ω' := Ω') (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom V b 1 ∧ ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom).IsFlagVBOn Set.univ (b s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_flagBundle | exact GlobalTheory.CompanionTheory.Ar.exists_flagBundle | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_flagBundle <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPrimeDividingUniformizerStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_dividing_uniformizer : ∀ (F' : Type) [Field F'] [NumberField F'] (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | exact GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | (intros; apply GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalization
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SegreChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.HilbertSamuel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [CharZero Ω] in

theorem segre_update_ratio [DecidableEq K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (k : K) (i : ι k) :
    (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k', y ⟨k', c k'⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    rw [Function.update_of_ne hb, div_self (hc b)]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem adjoin_segre_eq (y : (Σ k, ι k) → Ω) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    IntermediateField.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) =
      blockFnField y := by
  classical
  rw [← CoordArithOfFnField.ratioField_eq y (E c₀) hc]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    simp only [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, rfl⟩
  · rw [GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨E.symm (Function.update (E c₀) k i), ?_⟩
    simpa using segre_update_ratio y (E c₀) hc k i

theorem trdeg_blockFnField {y : (Σ k, ι k) → Ω} {e : ℕ} (hA : IsArithVar (mCoordIdeal y) (e + 1))
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Algebra.trdeg ℚ (blockFnField y) = e := by
  obtain ⟨_, _, _, hdim⟩ := hA
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = e := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h1, ← trdeg_add_eq ℤ ℚ (A := blockFnField y), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem exists_away_of_trdeg (S : Set Ω) (hS : S.Finite) {e : ℕ}
    (h : Algebra.trdeg ℚ (IntermediateField.adjoin ℚ S) = e) :
    ∃ s : Algebra.adjoin ℚ S, s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  have hfin : Algebra.FiniteType ℚ (Algebra.adjoin ℚ S) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
  have h2 : Algebra.trdeg ℚ (Algebra.adjoin ℚ S) = e := by
    rw [← h]
    exact (GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := ℚ) (A := Algebra.adjoin ℚ S)
      (IntermediateField.adjoin ℚ S)).symm
  exact GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
    (GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℚ _ h2)

theorem exists_away_standardSmooth (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ)
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  refine exists_away_of_trdeg _ (Set.finite_range _) ?_
  rw [adjoin_segre_eq y E c₀ hc]
  exact trdeg_blockFnField hA (E c₀) hc

end GlobalTheory.CompanionTheory.Ar.SegreChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_coeff_base_change_compat : ∀ (X₀ X : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ X₀) (i : Ω₀ →+* Ω) (V₀ V : Type) [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] (j : V₀ →+ V) (A₀ B₀ : Lat ξ₀ V₀) (A B : Lat ξ V) (p q : ℕ) (a₀ : ⋀[Ω₀]^p V₀) (b₀ : ⋀[Ω₀]^q V₀) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (x₀ : Cpt ξ₀) (u₁ : Fin p → V₀) (u₂ : Fin q → V₀), IsCptGen ξ₀ → IsCptGen ξ → Dominates ξ ξ₀ f i → IsExtOver i j → x₀.1 = f x.1 → A₀.IsFrameAt u₁ x₀ → B₀.IsFrameAt u₂ x₀ → A x = A₀.pull ξ f j x → B x = B₀.pull ξ f j x → IsCoeffAt A₀ B₀ p q a₀ b₀ x₀ 1 → CptIn.IsPullWedge i j a₀ a → CptIn.IsPullWedge i j b₀ b → IsCoeffAt A B p q a b x 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull | exact GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModelStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_type_over_integers_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → ∃ s : X ⟶ Spec (CommRingCat.of ℤ), LocallyOfFiniteType s ∧ QuasiCompact s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFType.main | exact GlobalTheory.CompanionTheory.Ar.ChartFType.main | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFType.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelStatementHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem pull_map (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (φ : E →ₗ[Ω] E') :
    (L.map φ).pull ξ' f (AddMonoidHom.id E') = (L.pull ξ' f (AddMonoidHom.id E)).map φ := by
  funext p'
  simp only [Lat.pull, Lat.map, Submodule.map_span]
  congr 1
  ext e'
  constructor
  · rintro ⟨h, e, he, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 he
    exact ⟨u, ⟨h, u, hu, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨h, v, hv, huv⟩, rfl⟩
    exact ⟨h, φ v, Submodule.mem_map.2 ⟨v, hv, rfl⟩, congrArg φ huv⟩

theorem pull_vb {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {f : X' ⟶ X} (hd : Dominates ξ' ξ f (RingHom.id Ω)) : (L.pull ξ' f (AddMonoidHom.id E)).IsVB g W := by
  intro p' _
  obtain ⟨h, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ _ _ hd p'
  obtain ⟨U, hU, b, hW, hb⟩ := hL ⟨f p'.1, h⟩ (Set.mem_univ _)
  refine ⟨f ⁻¹ᵁ U, hU, b, hW, fun q' _ hq' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ _ _ hd q'
  obtain ⟨hli, hsp⟩ := hb ⟨f q'.1, hq⟩ (Set.mem_univ _) hq'
  refine ⟨hli, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨h', e, he, he'⟩
    have he2 : e ∈ Submodule.span (regAt ξ ⟨f q'.1, hq⟩) (Set.range b) := hsp ▸ he
    have hee : e' = e := he'
    rw [hee]
    clear he he' hee
    induction he2 using Submodule.span_induction with
    | mem u hu => exact Submodule.subset_span hu
    | zero => exact Submodule.zero_mem _
    | add u v _ _ hu hv => exact Submodule.add_mem _ hu hv
    | smul c u _ hu => exact Submodule.smul_mem _ (⟨c.1, hreg c.1 c.2⟩ : regAt ξ' q') hu
  · refine Submodule.span_mono ?_
    intro e he
    exact ⟨hq, e, hsp ▸ Submodule.subset_span he, rfl⟩

theorem coh_map {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) (φ : E →ₗ[Ω] E') :
    (L.map φ).IsCohOn Set.univ := by
  intro p hp
  obtain ⟨U, hU, b, -, hb⟩ := hL p hp
  refine ⟨U, hU, g, φ ∘ b, fun q hq hqU => ?_⟩
  simp only [Lat.map]
  rw [(hb q hq hqU).2, Submodule.map_span, Set.range_comp]
  rfl

theorem span_map {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) (φ : E →ₗ[Ω] E') (p : Cpt ξ) :
    Submodule.span Ω ((L.map φ) p : Set E') = W.map φ := by
  obtain ⟨U, hU, b, hW, hb⟩ := hL p (Set.mem_univ p)
  simp only [Lat.map]
  rw [(hb p (Set.mem_univ p) hU).2, Submodule.map_span, Submodule.span_span_of_tower, ← hW, Submodule.map_span]
  rfl

theorem flagStep_min {r : ℕ} (b₀ : Fin r → E) (n : ℕ) : flagStep Ω b₀ (min n r) = flagStep Ω b₀ n := by
  unfold flagStep
  congr 2
  ext k
  have := k.2
  simp only [Set.mem_setOf_eq]
  omega

theorem flagStep_le {r : ℕ} {b₀ : Fin r → E} {W : Submodule Ω E} (h : ∀ k, b₀ k ∈ W) (n : ℕ) :
    flagStep Ω b₀ n ≤ W := by
  unfold flagStep
  rw [Submodule.span_le]
  rintro _ ⟨k, -, rfl⟩
  exact h k

theorem flagModel : FlagModelStatement := by
  intro o _ _ Ω _ _ κ _ x M A _ κa _ w S _ E _ _ L g r W b₀ hw hL hb hbW
  obtain ⟨p₀⟩ : Nonempty (Cpt M.ξ) := ⟨⟨genPt M.ξ, specializes_rfl⟩⟩
  haveI hfin : ∀ σ, FiniteDimensional Ω (W σ) := fun σ => by
    obtain ⟨U, -, b, hW, -⟩ := hL σ p₀ (Set.mem_univ _)
    rw [← hW]
    exact FiniteDimensional.span_of_finite Ω (Set.finite_range b)
  obtain ⟨κ', hκ', y, M', f, hdom, hnorm, hchart, hvb, hat⟩ :=
    GlobalTheory.T.flag_model_common_refinement o Ω κ x M A κa w (Σ σ, Fin (r σ + 1))
      (fun q => E ⧸ flagStep Ω (b₀ q.1) q.2)
      (fun q => (L q.1).map (flagStep Ω (b₀ q.1) q.2).mkQ)
      (fun q => (W q.1).map (flagStep Ω (b₀ q.1) q.2).mkQ) hw
      (fun q => coh_map (hL q.1) _) (fun q p => span_map (hL q.1) _ p)
  have hpull : ∀ σ, ((L σ).pull M'.ξ f (AddMonoidHom.id E)).IsVBOn Set.univ (g σ) (W σ) :=
    fun σ => pull_vb (hL σ) hdom
  have hquot : ∀ σ (n : ℕ), ∃ s W', (((L σ).pull M'.ξ f (AddMonoidHom.id E)).map
      (flagStep Ω (b₀ σ) n).mkQ).IsVBOn Set.univ s W' := fun σ n => by
    rw [← flagStep_min]
    have h := hvb ⟨σ, ⟨min n (r σ), Nat.lt_succ_of_le (min_le_right _ _)⟩⟩
    rw [pull_map] at h
    exact ⟨_, _, h⟩
  refine ⟨κ', hκ', y, M', f, hdom, hnorm, hchart, fun σ => ?_, fun σ n p' => ?_, fun p hp hfr => ?_⟩
  · exact GlobalTheory.T.lattice_flag_vector_bundle _ _ _ _ _ _ _ _ _ _ (hb σ) (hbW σ) (hpull σ) (hquot σ)
  · obtain ⟨s, W', h⟩ := hquot σ n
    exact (GlobalTheory.T.lattice_sub_quotient_split _ _ _ _ _ _ _ _ _ _ _ (flagStep_le (hbW σ) n) (hpull σ) h).2 p' (Set.mem_univ _)
  · exact hat p hp fun q => hfr q.1 q.2

end GlobalTheory.CompanionTheory.Ar.FlagModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFormValuationEmbeddingStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_form_valuation_embedding : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω], Birational y → IsRelevant (mCoordIdeal y) → ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → aeval z h ≠ 0 → ∃ φ : F →+* 𝕜, ∀ θ : F, HasVal y 0 (algebraMap F Ω θ) z (φ θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.exists_form_embedding_hasVal | exact GlobalTheory.CompanionTheory.Ar.Small.exists_form_embedding_hasVal | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.exists_form_embedding_hasVal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianNormSectionValueStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_norm_section_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [Nonempty K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (A : HermLine J) (c₀ : Ω) (C : ℝ) (g h : MRing J) (dg dh : K → ℕ), IsCptGen ξ → CoordsAt ξ y z w → (∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w) → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → evC w h ≠ 0 → ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.EvalPt.norm_evC_of_forms | exact GlobalTheory.CompanionTheory.Ar.Flat.EvalPt.norm_evC_of_forms | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.EvalPt.norm_evC_of_forms <;> assumption)
end

