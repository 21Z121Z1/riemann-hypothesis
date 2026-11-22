import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverPrOfFnAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0280
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
import Development.WeilBound.CoreStatements.ProjectiveValuations.FlagEmbeddingAtlasProjective

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSection
section
open GlobalTheory.CompanionTheory.Ar AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open Classical

namespace GlobalTheory.CompanionTheory.Ar.Adapt

open ReciprocityTheory.AnForm.M.PLAux in

theorem exists_adaptedAtlas : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) → ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  intro e X _ _ _ A L s n m W hL hs hsnc _hle
  have hgood : ∀ x : X, ∃ φ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A φ ∧
      x ∈ φ.source ∧ φ x = 0 ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧
      ∃ (S : Finset (Fin e)) (μ : Fin e → ℕ) (M : ℝ), (∀ i ∈ S, 1 ≤ μ i) ∧
        (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
        ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s →
          |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
    intro x
    obtain ⟨φ, S, μ, v, hφc, hxφ, hball, hφx, hsrcU, hμ, hv, hv0, hsv⟩ :=
      GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form e X A L s n m W hsnc x
    refine ⟨φ, hφc, hxφ, hφx, hball, S, μ, ?_⟩

    have hnorm : ∀ y ∈ φ.source,
        ‖s y y‖ * Real.exp (-L.φ y y) = ‖s x y‖ * Real.exp (-L.φ x y) := fun y hy =>
      (hs.2 x y y ⟨hsrcU hy, L.mem_U y⟩).symm
    have hzero : ∀ y ∈ φ.source, (s y y = 0 ↔ s x y = 0) := by
      intro y hy
      have h := hnorm y hy
      constructor
      · intro h0
        rw [h0, norm_zero, zero_mul] at h
        have := (mul_eq_zero.1 h.symm).resolve_right (Real.exp_pos _).ne'
        exact norm_eq_zero.1 this
      · intro h0
        rw [h0, norm_zero, zero_mul] at h
        have := (mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne'
        exact norm_eq_zero.1 this
    have hmono : ∀ y ∈ φ.source, (s x y = 0 ↔ ∃ i ∈ S, φ y i = 0) := by
      intro y hy
      rw [hsv y hy, mul_eq_zero, Finset.prod_eq_zero_iff]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact absurd h (hv0 y hy)
        · exact ⟨i, hi, pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 (hμ i hi)) |>.1 h⟩
      · rintro ⟨i, hi, h⟩
        exact Or.inr ⟨i, hi, by rw [h, zero_pow (Nat.one_le_iff_ne_zero.1 (hμ i hi))]⟩
    have hbd : ∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0) := by
      intro y hy
      have hp := φ.map_target hy
      show s (φ.symm y) (φ.symm y) = 0 ↔ _
      rw [hzero _ hp, hmono _ hp, φ.right_inv hy]

    have hK : IsCompact (Metric.closedBall (0 : Fin e → ℂ) 2) := isCompact_closedBall _ _
    have hF : ContinuousOn (fun z => Real.log ‖v (φ.symm z)‖) (Metric.closedBall (0 : Fin e → ℂ) 2) := by
      intro z hz
      have hzt := hball hz
      have han := analyticAt_compat_fun hφc hv hzt (φ.map_target hzt)
      exact (han.continuousAt.norm.log (by simpa using hv0 _ (φ.map_target hzt))).continuousWithinAt
    have hG : ContinuousOn (fun z => L.φ x (φ.symm z)) (Metric.closedBall (0 : Fin e → ℂ) 2) := by
      have h := contDiffOn_compat hφc (L.isOpen_U x) (hL.1 x)
      refine h.continuousOn.mono ?_
      intro z hz
      exact ⟨hball hz, hsrcU (φ.map_target (hball hz))⟩
    obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hF
    obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hG
    refine ⟨2 * C₁ + 2 * C₂ + ∑ i ∈ S, (μ i : ℝ) * Real.log 4, hμ, hbd, ?_⟩
    intro y hy hyb
    have hyt := hball hy
    have hp := φ.map_target hyt
    set p := φ.symm y with hpdef
    have hφp : φ p = y := φ.right_inv hyt
    have hspp : s p p ≠ 0 := hyb
    have hsxp : s x p ≠ 0 := fun h => hspp ((hzero p hp).2 h)
    have hyi : ∀ i ∈ S, y i ≠ 0 := fun i hi h0 =>
      hsxp ((hmono p hp).2 ⟨i, hi, by rw [hφp]; exact h0⟩)
    have hvp : v p ≠ 0 := hv0 p hp

    have hlogN : logNormSec L s p = Real.log ‖v p‖ + ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ - L.φ x p := by
      unfold logNormSec
      rw [hnorm p hp, Real.log_mul (norm_ne_zero_iff.2 hsxp) (Real.exp_pos _).ne', Real.log_exp,
        hsv p hp, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hvp), norm_prod,
        Real.log_prod]
      · rw [hφp]
        congr 2
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [norm_pow, Real.log_pow]
      · intro i hi
        rw [hφp, norm_pow]
        exact pow_ne_zero _ (norm_ne_zero_iff.2 (hyi i hi))
      · rw [norm_ne_zero_iff, Finset.prod_ne_zero_iff]
        intro i hi
        rw [hφp]
        exact pow_ne_zero _ (hyi i hi)
    have hloc : rLoc S μ y = Real.exp 1 + ∑ i ∈ S, (μ i : ℝ) * (Real.log 4 - 2 * Real.log ‖y i‖) := by
      unfold rLoc
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Real.log_div (by norm_num) (pow_ne_zero _ (norm_ne_zero_iff.2 (hyi i hi))), Real.log_pow]
      push_cast
      ring
    have hdiff : rW L s p - rLoc S μ y =
        -2 * Real.log ‖v p‖ + 2 * L.φ x p - ∑ i ∈ S, (μ i : ℝ) * Real.log 4 := by
      unfold rW
      rw [hlogN, hloc]
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [show ∑ i ∈ S, (μ i : ℝ) * (2 * Real.log ‖y i‖) = 2 * ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring]
      ring
    rw [hdiff]
    have h1 : |Real.log ‖v p‖| ≤ C₁ := by simpa [Real.norm_eq_abs] using hC₁ y hy
    have h2 : |L.φ x p| ≤ C₂ := by simpa [Real.norm_eq_abs] using hC₂ y hy
    have h3 : 0 ≤ ∑ i ∈ S, (μ i : ℝ) * Real.log 4 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  choose φ hφc hφx hφ0 hφb hrest using hgood
  choose S μ M hμ hbd hbnd using hrest
  have hU : ∀ x, φ x ⁻¹' Metric.ball 0 1 ∩ (φ x).source ∈ nhds x := by
    intro x
    refine IsOpen.mem_nhds ?_ ⟨by simp [hφ0 x], hφx x⟩
    rw [Set.inter_comm]
    exact (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover _ hU
  have hcov : ∀ x, ∃ y ∈ t, x ∈ φ y ⁻¹' Metric.ball 0 1 ∩ (φ y).source := by
    intro x
    have : x ∈ (⊤ : Set X) := trivial
    rw [← ht] at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hx⟩ := this
    exact ⟨y, hy, hx⟩
  obtain ⟨B, hAB, h1, h2⟩ := ReciprocityTheory.AnForm.M.atlasOfCompat A (fun i => φ (t.equivFin.symm i))
    (fun i => hφc _) (fun x => by
      obtain ⟨y, hy, hx⟩ := hcov x
      exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hx.2⟩)
  refine ⟨B, hAB, fun j => ?_, fun x => ?_, ∑ y ∈ t, |M y|, fun j => ?_⟩
  · obtain ⟨i, hi⟩ := h2 j
    rw [hi]
    exact hφb _
  · obtain ⟨y, hy, hx⟩ := hcov x
    obtain ⟨j, hj⟩ := h1 (t.equivFin ⟨y, hy⟩)
    refine ⟨j, ?_, ?_⟩
    · rw [hj]; simpa using hx.2
    · rw [hj]; simpa using hx.1
  · obtain ⟨i, hi⟩ := h2 j
    set y : X := (t.equivFin.symm i : X) with hydef
    have hyt : y ∈ t := (t.equivFin.symm i).2
    refine ⟨S y, μ y, hμ y, ?_, ?_⟩
    · rw [hi]; exact hbd y
    · intro z hz hzb
      rw [hi] at hzb ⊢
      refine (hbnd y z hz hzb).trans ((le_abs_self _).trans ?_)
      exact Finset.single_le_sum (f := fun y => |M y|) (fun _ _ => abs_nonneg _) hyt

end GlobalTheory.CompanionTheory.Ar.Adapt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowLemmaQuasiProjective
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_lift_of_isDominant {D Y V A : Scheme.{0}} [IsReduced Y] (σ : D ⟶ Y) [IsDominant σ]
    (r : Y ⟶ V) (k : A ⟶ V) [IsClosedImmersion k] (a : D ⟶ A) (h : σ ≫ r = a ≫ k) :
    ∃ φ : Y ⟶ A, φ ≫ k = r := by
  have hl : pullback.lift σ a h ≫ pullback.fst r k = σ := pullback.lift_fst _ _ _
  have : IsDominant (pullback.lift σ a h ≫ pullback.fst r k) := by rw [hl]; infer_instance
  have : IsDominant (pullback.fst r k) := IsDominant.of_comp (pullback.lift σ a h) _
  have : Surjective (pullback.fst r k) :=
    surjective_of_isDominant_of_isClosed_range _ (pullback.fst r k).isClosedEmbedding.isClosed_range
  have : IsIso (pullback.fst r k) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst r k) ≫ pullback.snd r k, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem isClosedImmersion_morphismRestrict {S X B X' T D : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    (u : B ⟶ S) [IsReduced X'] (π : X' ⟶ X) (b : X' ⟶ B) (hπb : π ≫ f = b ≫ u)
    [IsClosedImmersion (pullback.lift π b hπb)] (A : X.Opens) (O : B.Opens) (τ : T ⟶ S)
    (ρ : O.toScheme ⟶ T) (hρ : ρ ≫ τ = O.ι ≫ u) (k : A.toScheme ⟶ T) [IsClosedImmersion k]
    (hk : k ≫ τ = A.ι ≫ f) (σ : D ⟶ (b ⁻¹ᵁ O).toScheme) [IsDominant σ] (a : D ⟶ A.toScheme)
    (h₁ : σ ≫ b ∣_ O ≫ ρ = a ≫ k) (h₂ : a ≫ A.ι = σ ≫ (b ⁻¹ᵁ O).ι ≫ π) :
    IsClosedImmersion (b ∣_ O) := by
  obtain ⟨φ, hφ⟩ := exists_lift_of_isDominant σ (b ∣_ O ≫ ρ) k a h₁
  have hσφ : σ ≫ φ = a := by
    rw [← cancel_mono k, Category.assoc, hφ, h₁]
  have hφι : φ ≫ A.ι = (b ⁻¹ᵁ O).ι ≫ π := by
    refine ext_of_isDominant_of_isSeparated f ?_ σ ?_
    · rw [Category.assoc, Category.assoc, ← hk, reassoc_of% hφ, hρ, morphismRestrict_ι_assoc,
        hπb]
    · rw [reassoc_of% hσφ, h₂]
  have hc : (pullback.snd ρ k ≫ A.ι) ≫ f = (pullback.fst ρ k ≫ O.ι) ≫ u := by
    rw [Category.assoc, Category.assoc, ← hk, ← hρ, pullback.condition_assoc]
  let c : pullback ρ k ⟶ pullback f u := pullback.lift _ _ hc
  have c₁ : c ≫ pullback.fst f u = pullback.snd ρ k ≫ A.ι := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd f u = pullback.fst ρ k ≫ O.ι := pullback.lift_snd _ _ _
  have : Mono c := by
    have : Mono (c ≫ pullback.snd f u) := by rw [c₂]; infer_instance
    exact mono_of_mono c (pullback.snd f u)
  let m : (b ⁻¹ᵁ O).toScheme ⟶ pullback ρ k := pullback.lift (b ∣_ O) φ hφ.symm
  have m₁ : m ≫ pullback.fst ρ k = b ∣_ O := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd ρ k = φ := pullback.lift_snd _ _ _
  have hw : (b ⁻¹ᵁ O).ι ≫ pullback.lift π b hπb = m ≫ c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, c₁, reassoc_of% m₂, hφι]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, c₂, reassoc_of% m₁,
        morphismRestrict_ι]
  have sq : IsPullback (b ⁻¹ᵁ O).ι m (pullback.lift π b hπb) c := by
    have hr : ∀ {Z : Scheme.{0}} (x : Z ⟶ X') (y : Z ⟶ pullback ρ k),
        x ≫ pullback.lift π b hπb = y ≫ c → Set.range x ⊆ Set.range (b ⁻¹ᵁ O).ι := by
      intro Z x y e
      have e' : x ≫ b = (y ≫ pullback.fst ρ k) ≫ O.ι := by
        have := congr($e ≫ pullback.snd f u)
        simpa only [Category.assoc, pullback.lift_snd, c₂] using this
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (x ≫ b) z ∈ O
      rw [e']
      exact ((y ≫ pullback.fst ρ k) z).2
    refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
      (fun s ↦ IsOpenImmersion.lift (b ⁻¹ᵁ O).ι s.fst (hr _ _ s.condition)) (fun s ↦ ?_)
      (fun s ↦ ?_) (fun s n h₃ _ ↦ ?_)⟩⟩
    · exact IsOpenImmersion.lift_fac _ _ _
    · rw [← cancel_mono c, Category.assoc, ← hw, IsOpenImmersion.lift_fac_assoc, s.condition]
    · rw [← cancel_mono (b ⁻¹ᵁ O).ι, IsOpenImmersion.lift_fac, h₃]
  have : IsClosedImmersion m := MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq ‹_›
  rw [← m₁]
  infer_instance

theorem exists_isProper_surjective_isQProjOver : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (X' : Scheme.{0}) (π : X' ⟶ X), IsProper π ∧ Surjective π ∧ IsQProjOver (π ≫ p) := by
  intro R _ _ X _ f _ _ _
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hA : ∀ y : X, ∃ A : X.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set X))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → X.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : X, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    (isAmpleLB_of_isAffine (LB.isLB_triv (A i).toScheme)).isQProjOver ((A i).ι ≫ f))
  choose N j hj _ hjt using hP
  let U : X.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint X ∈ U := by
    have : ∀ i, genericPoint X ∈ A i := fun i ↦
      ((genericPoint_spec X).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : X.Opens ↦ genericPoint X ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have hps : ∀ n, IsProjOver (PSpace.str R n) := fun n ↦ ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨P, s, p, hP, hp, hu⟩ := ProjFinProd.exists_isProjOver_finite_prod R T (Sp R) (𝟙 _)
    (fun i ↦ PSpace R (N i)) (fun i ↦ PSpace.str R (N i))
    ((isAmpleLB_of_isAffine (LB.isLB_triv (Sp R))).isProjOver (𝟙 _)) (fun i ↦ hps _)
  rw [Category.comp_id] at hP hp
  obtain ⟨h, ⟨hs, hh⟩, -⟩ := hu U.toScheme (U.ι ≫ f) (fun i ↦ X.homOfLE (hUA i) ≫ j i)
    (fun i ↦ by rw [Category.assoc, hjt, X.homOfLE_ι_assoc, Category.comp_id])
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hP).1
  let g : U.toScheme ⟶ pullback f s := pullback.lift U.ι h hs.symm
  have g₁ : g ≫ pullback.fst f s = U.ι := pullback.lift_fst _ _ _
  have g₂ : g ≫ pullback.snd f s = h := pullback.lift_snd _ _ _
  have : IsImmersion (g ≫ pullback.fst f s) := by rw [g₁]; infer_instance
  have : IsImmersion g := IsImmersion.of_comp g (pullback.fst f s)
  have : QuasiCompact (g ≫ pullback.fst f s) := by rw [g₁]; infer_instance
  have : QuasiCompact g := QuasiCompact.of_comp g (pullback.fst f s)
  have := isSchemeTheoreticallyDominant_toImage g
  have : IsReduced g.image := IsSchemeTheoreticallyDominant.isReduced g.toImage
  let π : g.image ⟶ X := g.imageι ≫ pullback.fst f s
  let q : g.image ⟶ P := g.imageι ≫ pullback.snd f s
  have hπ : g.toImage ≫ π = U.ι := by rw [g.toImage_imageι_assoc, g₁]
  have hq : g.toImage ≫ q = h := by rw [g.toImage_imageι_assoc, g₂]
  have hπq : π ≫ f = q ≫ s := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have key : ∀ i, (π ⁻¹ᵁ A i).ι ≫ q ≫ p i = π ∣_ A i ≫ j i := by
    intro i
    obtain ⟨σ, _, e₁, e₂⟩ := GlobalTheory.ChowLemma.exists_dominant_lift π (hUA i) g.toImage hπ
    have := isProper_str R (N i)
    refine ext_of_isDominant_of_isSeparated (PSpace.str R (N i)) ?_ σ ?_
    · rw [Category.assoc, Category.assoc, hp, ← hπq, Category.assoc (π ∣_ A i), hjt,
        morphismRestrict_ι_assoc]
    · rw [reassoc_of% e₁, reassoc_of% hq, hh, reassoc_of% e₂]
  have : ∀ i, IsImmersion (j i) := hj
  let V : ∀ i, (PSpace R (N i)).Opens := fun i ↦ (j i).coborderRange
  have hV : ∀ i (x : g.image), π x ∈ A i → (q ≫ p i) x ∈ V i := by
    intro i x hx
    have e : ((π ⁻¹ᵁ A i).ι ≫ q ≫ p i) ⟨x, hx⟩ = (π ∣_ A i ≫ j i) ⟨x, hx⟩ := by rw [key i]
    change ((π ⁻¹ᵁ A i).ι ≫ q ≫ p i) ⟨x, hx⟩ ∈ V i
    rw [e]
    exact subset_coborder ⟨_, rfl⟩
  let W : P.Opens := ⨆ i, p i ⁻¹ᵁ V i
  have hW : Set.range q ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨i, hi⟩ := hcov (π x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hV i x hi⟩
  let q' : g.image ⟶ W.toScheme := IsOpenImmersion.lift W.ι q hW
  have hq' : q' ≫ W.ι = q := IsOpenImmersion.lift_fac _ _ _
  have hπq' : π ≫ f = q' ≫ W.ι ≫ s := by rw [reassoc_of% hq', hπq]
  have hcl : IsClosedImmersion (pullback.lift π q' hπq') := by
    let e : pullback f (W.ι ≫ s) ⟶ pullback f s :=
      pullback.lift (pullback.fst f (W.ι ≫ s)) (pullback.snd f (W.ι ≫ s) ≫ W.ι)
        (by rw [pullback.condition, Category.assoc])
    have e₁ : e ≫ pullback.fst f s = pullback.fst f (W.ι ≫ s) := pullback.lift_fst _ _ _
    have e₂ : e ≫ pullback.snd f s = pullback.snd f (W.ι ≫ s) ≫ W.ι := pullback.lift_snd _ _ _
    have : Mono e := by
      refine ⟨fun a b hab ↦ pullback.hom_ext ?_ ?_⟩
      · simpa only [Category.assoc, e₁] using congr($hab ≫ pullback.fst f s)
      · rw [← cancel_mono W.ι]
        simpa only [Category.assoc, e₂] using congr($hab ≫ pullback.snd f s)
    have he : pullback.lift π q' hπq' ≫ e = g.imageι := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, e₁, pullback.lift_fst]
      · rw [Category.assoc, e₂, pullback.lift_snd_assoc, hq']
    have : IsClosedImmersion (pullback.lift π q' hπq' ≫ e) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp _ e
  let O : T → W.toScheme.Opens := fun i ↦ (W.ι ≫ p i) ⁻¹ᵁ V i
  have hO : iSup O = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 y.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hloc : ∀ i, IsClosedImmersion (q' ∣_ O i) := by
    intro i
    have hr : Set.range g.toImage ⊆ Set.range (q' ⁻¹ᵁ O i).ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hx : (g.toImage ≫ π) x ∈ A i := by
        rw [hπ]
        exact hUA i x.2
      change (q' ≫ W.ι ≫ p i) (g.toImage x) ∈ V i
      rw [reassoc_of% hq']
      exact hV i _ hx
    have hσ := IsOpenImmersion.lift_fac (q' ⁻¹ᵁ O i).ι g.toImage hr
    have : IsDominant (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr ≫ (q' ⁻¹ᵁ O i).ι) := by
      rw [hσ]; infer_instance
    have : IsDominant (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr) :=
      IsDominant.of_comp_of_isOpenImmersion _ (q' ⁻¹ᵁ O i).ι
    refine isClosedImmersion_morphismRestrict f (W.ι ≫ s) π q' hπq' (A i) (O i)
      ((V i).ι ≫ PSpace.str R (N i)) ((W.ι ≫ p i) ∣_ V i) ?_ (j i).liftCoborder ?_
      (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr) (X.homOfLE (hUA i)) ?_ ?_
    · rw [morphismRestrict_ι_assoc, Category.assoc, hp]
    · rw [Scheme.Hom.liftCoborder_ι_assoc, hjt]
    · rw [← cancel_mono (V i).ι, Category.assoc, Category.assoc, Category.assoc,
        morphismRestrict_ι, Scheme.Hom.liftCoborder_ι, morphismRestrict_ι_assoc, reassoc_of% hσ,
        reassoc_of% hq', reassoc_of% hq, hh]
    · rw [X.homOfLE_ι, reassoc_of% hσ, hπ]
  have : IsClosedImmersion q' :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) O hO hloc
  have : IsImmersion q := by rw [← hq']; infer_instance
  have : IsProper π := by infer_instance
  have : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U.isOpen.dense ⟨_, hU⟩⟩
  have : IsDominant (g.toImage ≫ π) := by rw [hπ]; infer_instance
  have : IsDominant π := IsDominant.of_comp g.toImage π
  have : QuasiCompact (q ≫ s) := by rw [← hπq]; infer_instance
  have : QuasiCompact q := QuasiCompact.of_comp q s
  obtain ⟨n, i₀, hi₀, e₀⟩ := hP
  exact ⟨g.image, π, inferInstance,
    surjective_of_isDominant_of_isClosed_range π π.isClosedMap.isClosed_range, n, q ≫ i₀,
    inferInstance, inferInstance, by rw [Category.assoc, e₀, hπq]⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspLatticeMulComponentSection
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.LatMul

theorem evI_of_isBC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {T T' : CDVR} {io : c.F →+* T.Fr} {φ : T.Fr →+* T'.Fr} (y : IntFr Xo c T io)
    (z : IntFr Xo c T' (φ.comp io)) (h : Ref.IsBC φ y z) : evI z f = φ (evI y f) := by
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  obtain ⟨p, ψ, y0, h0⟩ := y.2.1
  let φA : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  have h1 : evI y f = ψ (f p y0) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hWD f hf p ψ y0 y.1 h0
  have h2 : evI z f = (φA.comp ψ) (f p y0) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hWD f hf p (φA.comp ψ) y0 z.1
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ φA h0 h)
  rw [h2, h1]
  rfl

end GlobalTheory.CompanionTheory.Ar.Rec.LatMul

open GlobalTheory.CompanionTheory.Ar.Rec.LatMul in

theorem GlobalTheory.CompanionTheory.Ar.Rec.indicator_mul_mem_latOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (a : WZ E) (Z : Comp Xo c) (w : Rul Xo c), w ∈ (Ref.pjSys Xo c).lat (cuspZ Xo c U a) → e Z * w ∈ latOn U h a Z := by
  intro E _ _ _ H Dw l Xo c r U h e hL hU a Z w hw
  have hI := GlobalTheory.T.valuation_component_unique E H Dw l Xo c r U h e hL
  refine (mem_latIn _ _ _ _).2 ⟨(hI.2.2 a).1 Z w hw.1, ?_⟩
  rintro la _ ⟨⟨q, T, io, e', ho, y, hy, eta, heta, rfl⟩, rfl⟩
  have hv : ∃ Z₀, _ := hI.1 la _ ⟨⟨_, T, io, e', ho, y, hy, eta, heta, rfl⟩, rfl⟩
  obtain ⟨T', φV, φ, r', z, t, hfin, hbc, hz, hphi⟩ := hU la T io e' ho y hy
  have hw0 : (0 : EReal) ≤ nval T.V e' (evI y w) := by
    have h0 := hw.2 la (show (Ref.pjSys Xo c).Pt la from PtV.mk la (hfin.overLa ho) z hz t hphi)
    rw [Ref.pjSys_val_mk Xo c la (hfin.overLa ho) z hz t hphi w,
      evI_of_isBC hL.evalWD w hw.1.1.1 y z hbc, hfin.nval_eq] at h0
    exact h0
  obtain ⟨Z₀, h0, h1⟩ := hv
  let p : PtV Xo c (algCls Xo c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho y hy eta heta
  have hmul : vAtV p (e Z * w) =
      vAtV p (e Z) + nval T.V e' (evI y w) := vAtV_mul _ _ _
  show (0 : EReal) ≤ vAtV p (e Z * w)
  rw [hmul]
  by_cases hZ : Z = Z₀
  · subst hZ
    have h0' : vAtV p (e Z) = 0 := h0
    rw [h0', zero_add]
    exact hw0
  · have h1' : vAtV p (e Z) = ⊤ := (h1 Z hZ).1
    rw [h1', EReal.top_add_of_ne_bot (nval_ne_bot _ _)]
    exact le_top
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finConst_of_all_hosts : FinConst :=
  FinConstAll.finConst GlobalTheory.T.finite_constant_all_holds

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagAtlasProjectiveEmbedding
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.CompanionTheory.FlagMod

theorem cells_smooth_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, Z ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ Z)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∃ d : ℕ, SmoothOfRelativeDimension d (π ≫ Y.s) ∧ IsProjOver (π ≫ Y.s) :=
  @DifferentiableLines.flag_embedding_atlas_projective

end GlobalTheory.CompanionTheory.FlagMod
end

