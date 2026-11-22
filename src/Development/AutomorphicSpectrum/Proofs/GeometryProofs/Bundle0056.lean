import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0026
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LLineiso
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLineStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_pullback_herm_line : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k), IsBlockMap κ v → (∀ A : HermLine ι, ∃! A' : HermLine ι', IsPullHerm κ v A A') ∧ (∀ (A : HermLine ι) (A' : HermLine ι'), IsPullHerm κ v A A' → IsSmoothHerm A → IsSmoothHerm A') ∧ (∀ (P' : Ideal (MRing ι')), ∀ z ∈ mcPts P', (fun p => z (v p)) ∈ mcPts (imageZ v P')) ∧ ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap | exact GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfHopfEmbedding
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem btOrder_eq_of_open_cover : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → Γ.TranslatesCover A j ⊤ → Γ.btOrder ⊤ = A :=
  @PositivityTheory.HtPt.Mh.char

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrder
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  intro R _ _ _ T _ _ Γ U hU
  obtain ⟨H, A, hH, hA, hAf⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ U hU
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [GlobalTheory.T.mem_btOrder_iff_btSet R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (GlobalTheory.T.regular_function_iff_section R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (GlobalTheory.T.regular_function_iff_section R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  rw [key]
  exact GlobalTheory.T.hopf_order_induction_injective R T H H.subtype H.subtype_injective A hA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CentreSetDominatingPointStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_set_dominating_point : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Centre.exists_centre | exact GlobalTheory.CompanionTheory.Ar.Centre.exists_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.Centre.exists_centre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingIntegralClosureFiniteStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ring_integral_closure_finite : ∀ {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFinite.finite_integralClosure_chRing | exact GlobalTheory.CompanionTheory.Ar.ChartFinite.finite_integralClosure_chRing | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFinite.finite_integralClosure_chRing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingIntegralFractionStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ring_integral_fraction : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧ v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FracExt.exists_integral_div | exact GlobalTheory.CompanionTheory.Ar.FracExt.exists_integral_div | (intros; apply GlobalTheory.CompanionTheory.Ar.FracExt.exists_integral_div <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_iff_centres : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ w : (Σ k, J k) → ℂ, w ∈ mcPts (mCoordIdeal y) ↔ ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt | exact GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt | (intros; apply GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeLatticeQuotientForms
section
open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.LineIso

theorem lineIso_of_two_degrees : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (a a' : K → ℤ) (e₀ : E) (ρ : Ω), CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) → Birational y → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → L.IsDegOn Set.univ y a e₀ → L.IsDegOn Set.univ y a' (ρ • e₀) → ∃ f g : MRing ι, IsLineIso (mCoordIdeal y) a a' f g ∧ aeval y f = ρ * aeval y g :=
  @PositivityTheory.UnitarySelfGeneration.l_lineiso

end GlobalTheory.CompanionTheory.Ar.LineIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentIdealLocalGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

open scoped nonZeroDivisors

theorem differentIdeal_principal_in_localSubring :
    ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [CharZero Ω] (R : Subring Ω)
      [IsLocalRing R] (σ : 𝓞 F →+* Ω), (∀ a, σ a ∈ R) →
      ∃ d₀ ∈ differentIdeal ℤ (𝓞 F), σ d₀ ≠ 0 ∧
        ∀ d ∈ differentIdeal ℤ (𝓞 F), σ d / σ d₀ ∈ R := by
  intro F _ _ Ω _ _ R _ σ hσ
  have hinj : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  set I : Ideal (𝓞 F) := differentIdeal ℤ (𝓞 F) with hIdef
  have hI0 : I ≠ ⊥ := differentIdeal_ne_bot
  let J : FractionalIdeal (𝓞 F)⁰ F := (I : FractionalIdeal (𝓞 F)⁰ F)
  have hJ0 : J ≠ 0 := by
    simpa [J] using hI0
  have hJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ0
  let σ' : 𝓞 F →+* R := σ.codRestrict R hσ
  let P : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal R).comap σ'
  have hP1 : (1 : 𝓞 F) ∉ P := by
    intro h
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by simpa [P] using h
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this

  have hex : ∃ x ∈ I, ∃ y ∈ J⁻¹, ∃ u : 𝓞 F, algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F x * y ∧
      u ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hle : J * J⁻¹ ≤ (P : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mul_le]
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
      have hab : algebraMap (𝓞 F) F x * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← hJ]
        exact FractionalIdeal.mul_mem_mul ha hb
      obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1 hab
      rw [← hu]
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨u, hcon x hx b hb u hu, rfl⟩
    have h1 : (1 : F) ∈ (P : FractionalIdeal (𝓞 F)⁰ F) :=
      hle (by rw [hJ]; exact FractionalIdeal.one_mem_one _)
    obtain ⟨w, hw, hw1⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
    have : w = 1 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hw1
    exact hP1 (this ▸ hw)
  obtain ⟨x, hx, y, hy, u, hu, huP⟩ := hex
  have hunit : IsUnit (σ' u) := by
    by_contra hnu
    exact huP ((IsLocalRing.mem_maximalIdeal _).2 hnu)
  have hσu : σ u ≠ 0 := by
    intro h0
    have : σ' u = 0 := Subtype.ext h0
    rw [this] at hunit
    exact not_isUnit_zero hunit
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : u = 0 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hu
    exact hσu (by simp [this])
  refine ⟨x, hx, fun h => hx0 (hinj (by simpa using h)), fun d hd => ?_⟩
  have hdJ : algebraMap (𝓞 F) F d ∈ J := (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  have hdy : algebraMap (𝓞 F) F d * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← hJ]
    exact FractionalIdeal.mul_mem_mul hdJ hy
  obtain ⟨v, hv⟩ := (FractionalIdeal.mem_one_iff _).1 hdy
  have hrel : d * u = x * v := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [map_mul, map_mul, hu, hv]
    ring
  have hrel' : σ d * σ u = σ x * σ v := by rw [← map_mul, ← map_mul, hrel]
  have hσx : σ x ≠ 0 := fun h => hx0 (hinj (by simpa using h))
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hw' : σ u * (w : Ω) = 1 := congrArg Subtype.val hw
  have key : σ d / σ x = σ v * (w : Ω) := by
    rw [div_eq_iff hσx]
    calc σ d = σ d * (σ u * (w : Ω)) := by rw [hw', _root_.mul_one]
      _ = (σ d * σ u) * (w : Ω) := by ring
      _ = σ v * (w : Ω) * σ x := by rw [hrel']; ring
  rw [key]
  exact R.mul_mem (hσ v) w.2

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentScaledLatticeExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem scale_pull_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (W : Submodule Ω V) (W' : Submodule Ω' V') (O : Type) [CommRing O] (σ : O →+* Ω) (𝔡 : Ideal O) (d₀ : O) (D : Submodule R V) (D' : Submodule R' V'), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → W' = Submodule.span Ω' (j '' (W : Set V)) → d₀ ∈ 𝔡 → σ d₀ ≠ 0 → (∀ d ∈ 𝔡, σ d / σ d₀ ∈ R) → (∀ e ∈ D, e ∈ W) → D' = Submodule.span R' (j '' (D : Set V)) → Submodule.span R' {e | e ∈ W' ∧ ∀ d ∈ 𝔡, (i.comp σ) d • e ∈ D'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j W W' O _ σ 𝔡 d₀ D D' hsemi hR hW' hd₀ hσd₀ hdiv hDW hD'
  have hj : ∀ (a : Ω) (v : V), j (a • v) = i a • j v := hsemi.1
  subst hW' hD'
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro e ⟨-, he⟩
    have hu : i (σ d₀) ≠ 0 := (map_ne_zero i).mpr hσd₀
    have key : ∀ y ∈ Submodule.span R' (j '' (D : Set V)),
        (i (σ d₀))⁻¹ • y ∈ Submodule.span R'
          (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨(σ d₀)⁻¹ • x, Submodule.subset_span ⟨W.smul_mem (σ d₀)⁻¹ (hDW x hx), fun d hd => ?_⟩, ?_⟩
        · rw [smul_smul, ← div_eq_mul_inv]
          exact D.smul_mem ⟨σ d / σ d₀, hdiv d hd⟩ hx
        · rw [hj, map_inv₀]
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul a y _ hy =>
        have e1 : (i (σ d₀))⁻¹ • (a • y) = a • ((i (σ d₀))⁻¹ • y) :=
          show (i (σ d₀))⁻¹ • ((a : Ω') • y) = (a : Ω') • ((i (σ d₀))⁻¹ • y) by
            rw [smul_smul, smul_smul, mul_comm]
        rw [e1]
        exact Submodule.smul_mem _ a hy
    have h1 := key _ (he d₀ hd₀)
    rwa [RingHom.comp_apply, inv_smul_smul₀ hu] at h1
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv =>
      apply Submodule.subset_span
      refine ⟨Submodule.subset_span ⟨v, hv.1, rfl⟩, fun d hd => ?_⟩
      rw [RingHom.comp_apply, ← hj]
      exact Submodule.subset_span ⟨_, hv.2 d hd, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      show j ((a : Ω) • x) ∈ _
      rw [hj]
      exact Submodule.smul_mem _ ⟨i a, hR a a.2⟩ hx

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantEigenProjector
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ScaledCasimir

section General

variable {J A : Type*} [Fintype J] [DecidableEq J] [CommRing A] (a : Module.Basis J ℤ A)

noncomputable def dualScaled (m : J) : A :=
  ∑ n, (Algebra.traceMatrix ℤ a).adjugate m n • a n

theorem trace_dualScaled_mul_basis (m p : J) :
    Algebra.trace ℤ A (dualScaled a m * a p) =
      if m = p then (Algebra.traceMatrix ℤ a).det else 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul (Algebra.traceMatrix ℤ a)) m) p
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one,
    mul_zero] at h
  rw [← h]
  simp only [dualScaled, Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply]

theorem trace_dualScaled_mul (m : J) (y : A) :
    Algebra.trace ℤ A (dualScaled a m * y) = a.repr y m * (Algebra.traceMatrix ℤ a).det := by
  conv_lhs => rw [← a.sum_repr y]
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_zsmul, trace_dualScaled_mul_basis,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem eq_of_trace_mul_basis (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) {x y : A}
    (H : ∀ p, Algebra.trace ℤ A (x * a p) = Algebra.trace ℤ A (y * a p)) : x = y := by
  have hz : (fun q => a.repr (x - y) q) = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hd
    funext p
    have h1 : Algebra.trace ℤ A ((x - y) * a p) = 0 := by
      rw [sub_mul, map_sub, H p, sub_self]
    conv at h1 => lhs; rw [← a.sum_repr (x - y)]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul] at h1
    simpa [Matrix.vecMul, dotProduct, Algebra.traceMatrix_apply, Algebra.traceForm_apply] using h1
  have : x - y = 0 := by
    apply a.repr.injective
    ext q
    simpa using congrFun hz q
  exact sub_eq_zero.mp this

theorem mul_dualScaled (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) (b : A) (n : J) :
    b * dualScaled a n = ∑ m, a.repr (b * a m) n • dualScaled a m := by
  apply eq_of_trace_mul_basis a hd
  intro p
  have h1 : b * dualScaled a n * a p = dualScaled a n * (b * a p) := by ring
  rw [h1, trace_dualScaled_mul]
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, trace_dualScaled_mul,
    Module.Basis.repr_self, smul_eq_mul]
  simp [Finsupp.single_apply]

theorem sum_dualScaled_mul (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) :
    ∑ m, dualScaled a m * a m = (((Algebra.traceMatrix ℤ a).det : ℤ) : A) := by
  apply eq_of_trace_mul_basis a hd
  intro k
  have h1 : ∀ m, dualScaled a m * a m * a k = dualScaled a m * (a k * a m) := fun m => by ring
  have h2 : (((Algebra.traceMatrix ℤ a).det : ℤ) : A) * a k =
      (Algebra.traceMatrix ℤ a).det • a k := by rw [zsmul_eq_mul]
  rw [Finset.sum_mul, map_sum, h2, map_zsmul, Algebra.trace_eq_matrix_trace a (a k)]
  simp only [h1, trace_dualScaled_mul, Matrix.trace, Matrix.diag_apply,
    Algebra.leftMulMatrix_eq_repr_mul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _

theorem equivariant (hd : (Algebra.traceMatrix ℤ a).det ≠ 0)
    {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (ρ : A →+* Module.End Ω V) (σ : A →+* Ω) (b : A) (v : V) :
    ρ b (∑ m, σ (dualScaled a m) • ρ (a m) v) =
      σ b • ∑ m, σ (dualScaled a m) • ρ (a m) v := by
  have hmul : ∀ m, ρ b (ρ (a m) v) = ∑ n, ((a.repr (b * a m) n : ℤ) : Ω) • ρ (a n) v := by
    intro m
    have h0 : ρ b (ρ (a m) v) = ρ (b * a m) v := by simp [map_mul]
    rw [h0]
    conv_lhs => rw [← a.sum_repr (b * a m)]
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  have hc : ∀ n, σ b * σ (dualScaled a n) =
      ∑ m, σ (dualScaled a m) * ((a.repr (b * a m) n : ℤ) : Ω) := by
    intro n
    rw [← map_mul, mul_dualScaled a hd, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  simp only [map_sum, map_smul, hmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc n, Finset.sum_smul]

end General

theorem exists_scaledCasimir :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (n : ℕ) (a c : Fin n → 𝓞 F), (∑ m, c m * a m = (((NumberField.discr F : ℤ) : 𝓞 F))) ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V] (ρ : 𝓞 F →+* Module.End Ω V) (σ : 𝓞 F →+* Ω) (b : 𝓞 F) (v : V), ρ b (∑ m, σ (c m) • ρ (a m) v) = σ b • ∑ m, σ (c m) • ρ (a m) v := by
  intro F _ _
  let a := Module.finBasis ℤ (𝓞 F)
  have hdet : (Algebra.traceMatrix ℤ a).det = NumberField.discr F := by
    rw [← Algebra.discr_def, NumberField.discr_eq_discr]
  have hd : (Algebra.traceMatrix ℤ a).det ≠ 0 := by
    rw [hdet]; exact NumberField.discr_ne_zero F
  refine ⟨_, a, dualScaled a, ?_, ?_⟩
  · rw [sum_dualScaled_mul a hd, hdet]
  · intro Ω _ V _ _ ρ σ b v
    exact equivariant a hd ρ σ b v

end GlobalTheory.CompanionTheory.Ar.ScaledCasimir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapOfFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DualExt

theorem dual_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V'), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → ∃ jd : Module.Dual Ω V →+ Module.Dual Ω' V', ∀ w e, jd w (j e) = i (w e) := by
  intro Ω Ω' _ _ i V V' _ _ _ _ j hext hspan
  let b := Module.Basis.ofVectorSpace Ω V
  have hj : ∀ e : V, j e = (b.repr e).sum fun k a => i a • j (b k) := by
    intro e
    conv_lhs => rw [← b.linearCombination_repr e]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => hext.1 _ _
  have hli : LinearIndependent Ω' fun k => j (b k) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    have h := hext.2 s.card (fun m => b (s.equivFin.symm m))
      (b.linearIndependent.comp (fun m => (s.equivFin.symm m : _))
        (Subtype.val_injective.comp s.equivFin.symm.injective))
    have h2 := h.comp s.equivFin s.equivFin.injective
    convert h2 using 1
    funext x
    simp
  have hsp : ⊤ ≤ Submodule.span Ω' (Set.range fun k => j (b k)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    rw [hj e, Finsupp.sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  refine ⟨AddMonoidHom.mk' (fun w => b'.constr Ω' fun k => i (w (b k))) fun w₁ w₂ => ?_, fun w e => ?_⟩
  · rw [← map_add]
    congr 1
    funext k
    simp
  · show b'.constr Ω' (fun k => i (w (b k))) (j e) = i (w e)
    rw [hj e, Finsupp.sum, map_sum]
    conv_rhs => rw [← b.linearCombination_repr e, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, show j (b k) = b' k from (Module.Basis.mk_apply hli hsp k).symm, Module.Basis.constr_basis,
      map_smul, smul_eq_mul, smul_eq_mul, map_mul]

end GlobalTheory.CompanionTheory.Ar.DualExt
end
end

