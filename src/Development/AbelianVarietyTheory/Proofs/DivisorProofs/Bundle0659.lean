import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0005
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0003
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtWeak
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0636
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0635
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionOfCohomologyDerivativeRelation
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_obRel_of_dRel : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w → (∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = 0) → ∃ (m : ℕ) (u v : Fin m → Glob1 F), ObRel F x u v := by
  intro R _ C _ F hF h0 x n y w hD hy
  obtain ⟨N, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl2⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 N Φ
  obtain ⟨f, g, ω, hf, hg, hfD⟩ := hD
  have hcl : ∀ i, ∃ b : C0 F, d0 F b = (∑ k, l i (w k) • g k).1 := fun i ↦ by
    refine H1.mk_eq_zero.1 ?_
    simp only [map_sum, map_smul, hg]
    exact hy (l i)
  choose b hb using hcl
  have hb' : ∀ i ⦃T T' : C⦄ (φ : T ⟶ T'),
      b i T' - mp F φ (b i T) = ∑ k, l i (w k) • (g k).1 T T' φ := fun i T T' φ ↦ by
    have := congrFun (congrFun (congrFun (hb i) T) T') φ
    rw [amitsur_d0_apply] at this
    rw [this, Submodule.coe_sum]
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  have hw : ∀ k (T : C), (w k).1 T = ∑ i, l i (w k) • (Φ.w i).1 T := fun k T ↦ by
    have := congrArg (fun v : Glob1 F ↦ v.1 T) (hl2 (w k))
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hsum : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ∑ k, (g k).1 T T' φ • (w k).1 T' =
      ∑ i, (b i T' - mp F φ (b i T)) • (Φ.w i).1 T' := fun T T' φ ↦ by
    simp only [hb', hw, Finset.smul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_comm, smul_assoc]
  let ω' : A0 F := fun T ↦ ω T + ∑ i, b i T • (Φ.w i).1 T
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω' T' = p1 F φ (ω' T) + D R (F.obj T') (f.1 T T' φ) := by
    intro T T' φ
    rw [hfD φ, hsum φ]
    simp only [ω', map_add, map_sum, oneFormsMapOfFunctorMorphism_smul, ← (Φ.w _).2 φ, sub_smul, Finset.sum_sub_distrib]
    abel
  have hglob : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'),
      dOne R (F.obj T') (ω' T') = pOm F 2 φ (dOne R (F.obj T) (ω' T)) := by
    intro T T' φ
    rw [hconn φ, map_add, dOne_D, add_zero, pOm_dOne]
  obtain ⟨m, u, v, hζ⟩ := GlobalTheory.T.globalTwoForm_eq_sumWedgeGlobalOneForms R C F ⟨N, ⟨Φ⟩⟩ h0 (fun T ↦ dOne R (F.obj T) (ω' T)) hglob
  exact ⟨m, u, v, f, ω', hf, hconn, fun T ↦ congrFun hζ T⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDisjointMeetsComponents
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem exists_preconnected_infinite_nhds {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (hn : 1 ≤ n) (e : OpenPartialHomeomorph Y (V n)) (x : Y) (hx : x ∈ e.source) :
    ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ B.Infinite := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hx)
  refine ⟨e.symm '' ball (e x) r, ?_, ?_, ?_⟩
  · have h := e.symm.image_mem_nhds (x := e x) (e.map_source hx) (ball_mem_nhds (e x) hr)
    rwa [e.left_inv hx] at h
  · exact (convex_ball (e x) r).isPreconnected.image _ (e.continuousOn_symm.mono hsub)
  · refine Set.Infinite.image (e.symm.injOn.mono hsub) ?_
    haveI : NeBot (𝓝[≠] (e x)) := Module.punctured_nhds_neBot ℂ (V n) (e x)
    exact infinite_of_mem_nhds (e x) (ball_mem_nhds (e x) hr)

theorem exists_finite_disjoint_meets_components :
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ S : Set Y, S.Finite → ∃ T : Set Y, T.Finite ∧ Disjoint T S ∧ ∀ y, ∃ P ∈ T, P ∈ connectedComponent y := by
  intro n Y _ _ _ _ _ _ ι La _ A hn S hS
  have h1 : ∀ x : Y, ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ ∃ P ∈ B, P ∉ S := by
    intro x
    obtain ⟨B, hB, hc, hi⟩ :=
      exists_preconnected_infinite_nhds hn (A.chart (A.pick x)) x (A.mem_pick x)
    obtain ⟨P, hP, hPS⟩ := (hi.diff hS).nonempty
    exact ⟨B, hB, hc, P, hP, hPS⟩
  choose B hB hc P hP hPS using h1
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover B (fun x _ => hB x)
  refine ⟨P '' (t : Set Y), t.finite_toSet.image P, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩
    exact hPS x
  · intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨P x, ⟨x, hx, rfl⟩, (hc x).subset_connectedComponent hy (hP x)⟩

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalVectorFieldOfOneFormFunctional
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_vectorField_of_functional : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ l : Glob1 F →ₗ[R] R, ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T, (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧ ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  intro R _ C _ F hF h0 l
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨c, hc, hsum⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  refine ⟨fun T ↦ ∑ i, algebraMap R (F.obj T) (l (Φ.w i)) • Φ.δ i T, ?_, ?_⟩
  · intro T T' φ ω
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul,
      AlgHom.commutes, Φ.nat]
  · intro w T
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hc, ← map_mul, ← map_sum]
    have hw : l w = l (∑ i, c i w • Φ.w i) := congrArg l (hsum w)
    rw [hw, map_sum]
    simp [mul_comm]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHenselisation
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem exists_henselisation : ∀ (R : Type) [CommRing R] [IsLocalRing R], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Function.Bijective (ResidueField.map (algebraMap R S)) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _
  haveI : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  obtain ⟨hloc, hofloc⟩ := GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of R
  haveI : HenselianLocalRing (Hens R) := GlobalTheory.T.henselianLocalRing_hens' R
  let ofA : ∀ i : EtNbhd R, i.B →ₐ[R] Hens R := fun i =>
    { toRingHom := Hens.of i, commutes' := GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i }
  have hof_trans : ∀ {i j : EtNbhd R} (h : i ≤ j) (x : i.B),
      Hens.of j (EtNbhd.trans h x) = Hens.of i x := fun h x => Ring.DirectLimit.of_f h x
  have hexists : ∀ s : Hens R, ∃ i b, Hens.of i b = s := fun s => Ring.DirectLimit.exists_of s
  have hlocB : ∀ i : EtNbhd R, IsLocalHom (algebraMap R i.B) := fun i => ⟨fun r hr => by
    by_contra hn
    have hm : algebraMap R i.B r ∈ maximalIdeal i.B := by
      rw [GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map R i]; exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal r).2 hn)
    exact (mem_maximalIdeal _).1 hm hr⟩
  haveI : IsLocalHom (algebraMap R (Hens R)) := by
    have e : algebraMap R (Hens R) =
        (Hens.of EtNbhd.base).comp (algebraMap R (EtNbhd.base (R := R)).B) := rfl
    rw [e]
    haveI := hlocB EtNbhd.base
    haveI := hofloc EtNbhd.base
    infer_instance
  have hmax : (maximalIdeal R).map (algebraMap R (Hens R)) = maximalIdeal (Hens R) := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit (algebraMap R (Hens R)) r hr
    · intro s hs
      obtain ⟨i, b, rfl⟩ := hexists s
      have hb : b ∈ maximalIdeal i.B := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact (mem_maximalIdeal _).1 hs (hu.map (Hens.of i))
      rw [GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map R i] at hb
      have hm := Ideal.mem_map_of_mem (Hens.of i) hb
      rwa [Ideal.map_map, show (Hens.of i).comp (algebraMap R i.B) = algebraMap R (Hens R) from
        RingHom.ext (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i)] at hm
  have hres : Function.Bijective (ResidueField.map (algebraMap R (Hens R))) := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨s, rfl⟩ := residue_surjective y
    obtain ⟨i, b, rfl⟩ := hexists s
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood R i b
    refine ⟨residue R r, ?_⟩
    rw [ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      ← GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i r, ← map_sub]
    exact map_nonunit (Hens.of i) _ hr
  refine ⟨Hens R, inferInstance, inferInstance, inferInstance, inferInstance, GlobalTheory.T.flat_hens' R, hmax, hres,
    EtNbhd R, inferInstance, inferInstance, inferInstance, fun i => (ofA i).range, ?_, ?_, ?_⟩
  · intro i j h y hy
    obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).1 hy
    exact (AlgHom.mem_range _).2 ⟨EtNbhd.trans h x, hof_trans h x⟩
  · intro s
    obtain ⟨i, b, rfl⟩ := hexists s
    exact ⟨i, (AlgHom.mem_range _).2 ⟨b, rfl⟩⟩
  · intro i
    exact ⟨i.A, inferInstance, inferInstance, inferInstance, i.q, inferInstance,
      ⟨AlgEquiv.ofInjective (ofA i) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R i)⟩⟩

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloAeEq
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2LimitHolomorphic

open Set

variable {n : ℕ}

theorem exists_pos_le_on_compact {W K : Set (V n)} {ρ : V n → ℝ} (hρ : ContinuousOn ρ W)
    (hpos : ∀ v ∈ W, 0 < ρ v) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ K, c ≤ ρ v := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (hρ.mono hKW)
  exact ⟨ρ x, hpos x (hKW hx), fun v hv => hmin hv⟩

theorem lintegral_sq_le {W K : Set (V n)} {ρ : V n → ℝ} {c : ℝ} (hc : 0 < c)
    (hK : MeasurableSet K) (hKW : K ⊆ W) (hcK : ∀ v ∈ K, c ≤ ρ v) (g : V n → ℂ) :
    ∫⁻ v in K, ‖g v‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ v in W, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
  calc ∫⁻ v in K, ‖g v‖ₑ ^ 2
      ≤ ∫⁻ v in K, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
        apply setLIntegral_mono' hK
        intro v hv
        rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ c⁻¹ * ρ v := by
          rw [le_inv_mul_iff₀ hc]; simpa using hcK v hv
        have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖g v‖)
        nlinarith
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ v in K, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr

theorem integrableOn_of_limit {W K : Set (V n)} {ρ : V n → ℝ} {u : ℕ → V n → ℂ}
    {f : V n → ℂ} (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v)
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    (hK : IsCompact K) (hKW : K ⊆ W) : IntegrableOn f K := by
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_on_compact hρ hpos hK hKW
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
  have hum : IntegrableOn (u m) K := ((hu m).continuousOn.mono hKW).integrableOn_compact hK
  have hfK : AEStronglyMeasurable f (volume.restrict K) :=
    (hf.mono_measure (Measure.restrict_mono hKW le_rfl)).aestronglyMeasurable
  have hfin : ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 < ⊤ :=
    lt_of_le_of_lt (lintegral_sq_le hc hK.measurableSet hKW hcK (fun v => f v - u m v))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hm.trans ENNReal.one_lt_top))
  have hd : IntegrableOn (fun v => f v - u m v) K := by
    refine ⟨hfK.sub hum.aestronglyMeasurable, ?_⟩
    show ∫⁻ v in K, ‖f v - u m v‖ₑ < ⊤
    have hpt : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ 2 := by
      intro x
      rcases le_total x 1 with h | h
      · exact h.trans le_self_add
      · calc x = x * 1 := (mul_one x).symm
          _ ≤ x * x := by gcongr
          _ = x ^ 2 := (sq x).symm
          _ ≤ 1 + x ^ 2 := le_add_self
    calc ∫⁻ v in K, ‖f v - u m v‖ₑ ≤ ∫⁻ v in K, (1 + ‖f v - u m v‖ₑ ^ 2) :=
          lintegral_mono fun v => hpt _
      _ = volume K + ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const]; simp
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hfin⟩
  exact (hd.add hum).congr_fun (fun v _ => by simp) hK.measurableSet

theorem enorm_integral_mul_le {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {d h : V n → ℂ}
    (hd : AEMeasurable d (volume.restrict W)) (hh : Continuous h) :
    ‖∫ v in W, d v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
  have hρm : AEMeasurable ρ (volume.restrict W) := hρ.aemeasurable hW.measurableSet
  have hsq : AEMeasurable (fun v => Real.sqrt (ρ v)) (volume.restrict W) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hρm
  have ham : AEMeasurable (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)))
      (volume.restrict W) := (hd.norm.mul hsq).ennreal_ofReal
  have hbm : AEMeasurable (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)))
      (volume.restrict W) := (hh.measurable.norm.aemeasurable.div hsq).ennreal_ofReal
  have hab : EqOn (fun v => ‖d v * h v‖ₑ)
      ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
        fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) W := by
    intro v hv
    have hs : 0 < Real.sqrt (ρ v) := Real.sqrt_pos.2 (hpos v hv)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, norm_mul]
    congr 1
    field_simp
  have ha2 : EqOn (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, mul_pow,
      Real.sq_sqrt (hpos v hv).le]
  have hb2 : EqOn (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, div_pow,
      Real.sq_sqrt (hpos v hv).le]
  calc ‖∫ v in W, d v * h v‖ₑ ≤ ∫⁻ v in W, ‖d v * h v‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ v in W, ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
          fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) v :=
        setLIntegral_congr_fun hW.measurableSet hab
    _ ≤ (∫⁻ v in W, ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ v in W, ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two ham hbm
    _ = _ := by
        rw [setLIntegral_congr_fun hW.measurableSet ha2,
          setLIntegral_congr_fun hW.measurableSet hb2]

theorem integral_mul_eq_zero {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {u : ℕ → V n → ℂ} {f : V n → ℂ}
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    {h : V n → ℂ} (hhc : Continuous h) (hhs : HasCompactSupport h) (hsupp : tsupport h ⊆ W)
    (h0 : ∀ m, ∫ v in W, u m v * h v = 0) : ∫ v in W, f v * h v = 0 := by
  have hkc : Continuous fun v => ‖h v‖ ^ 2 / ρ v := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ W
    · exact (hhc.norm.pow 2).continuousAt.div (hρ.continuousAt (hW.mem_nhds hx))
        (hpos x hx).ne'
    · have hx' : x ∉ tsupport h := fun h' => hx (hsupp h')
      have hev : (fun v => ‖h v‖ ^ 2 / ρ v) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hx')] with v hv
        simp [hv]
      exact continuousAt_const.congr hev.symm
  have hks : HasCompactSupport fun v => ‖h v‖ ^ 2 / ρ v := by
    refine hhs.mono fun x hx => ?_
    intro h1
    apply hx
    simp [h1]
  have hH : ∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v) < ⊤ :=
    lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
      (hkc.integrable_of_hasCompactSupport hks).lintegral_lt_top
  by_cases hfi : Integrable (fun v => f v * h v) (volume.restrict W)
  swap
  · exact integral_undef hfi
  have key : ∀ m, ‖∫ v in W, f v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
    intro m
    have hUi : Integrable (fun v => u m v * h v) (volume.restrict W) := by
      have h1 : IntegrableOn (fun v => u m v * h v) (tsupport h) :=
        (((hu m).continuousOn.mono hsupp).mul hhc.continuousOn).integrableOn_compact hhs
      exact h1.of_forall_sdiff_eq_zero hW.measurableSet fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx.2]
    have heq : ∫ v in W, f v * h v = ∫ v in W, (f v - u m v) * h v := by
      simp_rw [sub_mul]
      rw [integral_sub hfi hUi, h0 m, sub_zero]
    rw [heq]
    exact enorm_integral_mul_le hW hρ hpos
      (hf.sub ((hu m).continuousOn.aemeasurable hW.measurableSet)) hhc
  have hT : Tendsto (fun m =>
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m =>
        (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
      simpa [Function.comp_def] using this
    have := ENNReal.Tendsto.mul_const h1
      (b := (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ))
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hH.ne))
    simpa using this
  have hle := ge_of_tendsto' hT key
  exact enorm_eq_zero.mp (le_antisymm hle bot_le)

theorem tsupport_dbarDir_subset (g : V n → ℂ) (w : V n) :
    tsupport (fun z => C.dbarDir g z w) ⊆ tsupport g := by
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  refine Function.mem_support.2 fun h0 => Function.mem_support.1 hz ?_
  simp [C.dbarDir, h0]

theorem exists_holo_ae_eq : ∀ (n : ℕ) (W : Set (V n)) (ρ : V n → ℝ) (u : ℕ → V n → ℂ) (f : V n → ℂ), IsOpen W → ContinuousOn ρ W → (∀ v ∈ W, 0 < ρ v) → (∀ m, DifferentiableOn ℂ (u m) W) → AEMeasurable f (volume.restrict W) → Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0) → ∃ g : V n → ℂ, DifferentiableOn ℂ g W ∧ g =ᵐ[volume.restrict W] f := by
  intro n W ρ u f hW hρ hpos hu hf hlim
  have hwh : C.WeakHolo W f := by
    refine ⟨(locallyIntegrableOn_iff hW.isLocallyClosed).2 fun K hKW hK =>
      integrableOn_of_limit hρ hpos hu hf hlim hK hKW, ?_⟩
    intro g hg w
    obtain ⟨hhc, hhs⟩ := C.dbarDir_continuous_hasCompactSupport hg.1 hg.2.1 w
    exact integral_mul_eq_zero hW hρ hpos hu hf hlim hhc hhs
      ((tsupport_dbarDir_subset g w).trans hg.2.2)
      (fun m => (C.holoWeak n W (u m) hW (hu m)).2 g hg w)
  obtain ⟨U, hU, hfU⟩ := C.reg n W f hW hwh
  exact ⟨U, hU, hfU.symm⟩

end GlobalTheory.L2LimitHolomorphic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHopfQuotientTorsionIdeal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_hopf_quotient_torsionIdeal :
    ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
      ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
        Function.Surjective π ∧ RingHom.ker π = torsionIdeal O B n := by
  intro O _ B _ _ _ n
  haveI : (torsionIdeal O B n).IsHopfIdeal O :=
    isHopfIdeal_kerIdeal_of_bialgHom O B B (mulBy O B n)
  let π : B →ₐc[O] B ⧸ torsionIdeal O B n := Bialgebra.Quotient.mkBialgHom _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have cocomm : IsCocomm O (B ⧸ torsionIdeal O B n) :=
    { comm_comp_comul := LinearMap.ext fun b => by
        obtain ⟨a, rfl⟩ := hπ b
        have h : ∀ t : B ⊗[O] B,
            TensorProduct.comm O (B ⧸ torsionIdeal O B n) (B ⧸ torsionIdeal O B n) (TensorProduct.map (π : B →ₗ[O] B ⧸ torsionIdeal O B n) (π : B →ₗ[O] B ⧸ torsionIdeal O B n) t) =
            TensorProduct.map (π : B →ₗ[O] B ⧸ torsionIdeal O B n) (π : B →ₗ[O] B ⧸ torsionIdeal O B n) (TensorProduct.comm O B B t) := by
          intro t
          induction t with
          | zero => simp
          | add x y hx hy => simp only [map_add, hx, hy]
          | tmul x y => simp
        change TensorProduct.comm O (B ⧸ torsionIdeal O B n) (B ⧸ torsionIdeal O B n) (comul (π a)) = comul (π a)
        rw [← CoalgHomClass.map_comp_comul_apply π a, h, comm_comul] }
  exact ⟨B ⧸ torsionIdeal O B n, inferInstance, inferInstance,
    cocomm, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem⟩

end GlobalTheory.PDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeLiftOfLevelSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_lift_of_level_section : ∀ (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (u : HolUnif P.A P.L h) (Ef : LinearMap.BilinForm ℤ u.Λ), 0 < k → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → (∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) → (∀ (x y : u.Λ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((k : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e)) → ∃ l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] u.Λ, (∀ a, lev a = u.ex ((k : ℂ)⁻¹ • (l a : Fin h → ℂ))) ∧ ∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b := by
  first | exact @GlobalTheory.LevelLift.exists_lattice_lift | exact GlobalTheory.LevelLift.exists_lattice_lift | (intros; apply GlobalTheory.LevelLift.exists_lattice_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftLocalPointAlongAffineFlatSurjectionStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π] [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'), IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  first | exact @GlobalTheory.LiftLocal.lift | exact GlobalTheory.LiftLocal.lift | (intros; apply GlobalTheory.LiftLocal.lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomainStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_lattice_frame_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ x ∈ X.dom, ∃ lam : Fin r → Fin r → E, (∀ j, lam j ∈ X.Λ) ∧ LinearIndependent E lam ∧ (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧ (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧ (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE X.p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE X.p0_le a))) := by
  first | exact @GlobalTheory.OrthoFrame.exists_orthoFrame | exact GlobalTheory.OrthoFrame.exists_orthoFrame | (intros; apply GlobalTheory.OrthoFrame.exists_orthoFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFiniteStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A], ∀ a : A, ∃ b : A, a = b ^ p := by
  first | exact @GlobalTheory.exists_pow_char_eq_of_isReduced_finite | exact GlobalTheory.exists_pow_char_eq_of_isReduced_finite | (intros; apply GlobalTheory.exists_pow_char_eq_of_isReduced_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutOfNilpotentThickenings
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem exists_pushout_of_nilpotent_thickenings : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₁.app U).hom)) → (∀ U : Y₂.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₂.app U).hom)) → ∃ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsPushout i₁ i₂ j₁ j₂ ∧ IsClosedImmersion j₁ ∧ IsClosedImmersion j₂ ∧ ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ h1 h2 s1 s2 n1 n2
  obtain ⟨Y, j₁, j₂, hw, c1, c2, t1, t2, 𝒱, hb, hp⟩ := GlobalTheory.T.exists_pushout_data_on_basis Y₀ Y₁ Y₂ i₁ i₂ h1 h2 s1 s2 n1 n2
  have hall := GlobalTheory.T.isPullback_app_of_isBasis_opens Y₀ Y₁ Y₂ Y i₁ i₂ j₁ j₂ hw 𝒱 hb hp
  exact ⟨Y, j₁, j₂, hw, GlobalTheory.T.isPushout_thickenings_of_isPullback_sections Y₀ Y₁ Y₂ i₁ i₂ h1 h2 s1 s2 Y j₁ j₂ hw c1 c2 t1 t2 hall,
    c1, c2, hall⟩

end GlobalTheory
end

