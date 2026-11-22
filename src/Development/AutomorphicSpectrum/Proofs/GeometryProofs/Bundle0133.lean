import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourth
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPositiveHermitianLineStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positive_hermitian_line : ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)), IsFullIntersectionSystem II → ∃ A : HermLine J, (∀ k, A.a k = 1) ∧ IsPositiveRel P A ∧ IsConjInvariantH A ∧ ∀ W : Ideal (MRing J), IsArithVar W 1 → 0 ≤ II K J W 1 ![A] := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line | exact GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSegreChartFrames
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ_eq {U : X.Opens} (g : Γ(X, U)) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) :
    genMap ξ p (X.presheaf.germ U p.1 hp g) = genMap ξ q (X.presheaf.germ U q.1 hq g) := by
  have key : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.2 hr) g) := by
    intro r hr
    show (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes r.2 (X.presheaf.germ U r.1 hr g)) = _
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hr r.2 g)
  rw [key p hp, key q hq]

theorem unitAt_of_isUnit {p : Cpt ξ} {s : X.presheaf.stalk p.1} (hs : IsUnit s) :
    unitAt ξ p (genMap ξ p s) := by
  have hu : IsUnit (genMap ξ p s) := hs.map (genMap ξ p)
  obtain ⟨u, rfl⟩ := hs
  refine ⟨hu.ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, Units.inv_mul, map_one]

theorem isUnit_of_unitAt (hξ : IsCptGen ξ) {p : Cpt ξ} {s : X.presheaf.stalk p.1}
    (h : unitAt ξ p (genMap ξ p s)) : IsUnit s := by
  obtain ⟨h0, _, t, ht⟩ := h
  refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
  rw [map_mul, ht, map_one, mul_inv_cancel₀ h0]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem inFrameDomain_of_unitAt (hT : CoordTie ℤ ξ (segreCoord y)) {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w : (Σ k, J k) → ℂ} (hz : CoordsAt ξ y z w) (h : genPt ξ ⤳ centre z) {c : (k : K) → J k} {f : Ω}
    (hc : InChart ξ (segreCoord y) c ⟨centre z, h⟩) (hf : unitAt ξ ⟨centre z, h⟩ f) :
    InFrameDomain y c f w := by
  let gv : X.presheaf.stalk (centre z) →+* Ω := genMap ξ ⟨centre z, h⟩
  let ev : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have hinj : Function.Injective gv := hT.gen.inj ⟨centre z, h⟩
  constructor
  · choose d hd using hz.1
    have key : ∀ k, ∃ (r : ℂ) (s : X.presheaf.stalk (centre z)),
        gv s = y ⟨k, c k⟩ / y ⟨k, d k⟩ ∧ ev s = r ∧ w ⟨k, c k⟩ = r * w ⟨k, d k⟩ := by
      intro k
      obtain ⟨r, ⟨_, s, hs, hv⟩, hw⟩ := (hz.2 k (d k) (hd k)).2 (c k)
      exact ⟨r, s, hs, hv, hw⟩
    choose r s hs hv hw using key
    obtain ⟨t, ht⟩ : ∃ t, gv t = segreCoord y d / segreCoord y c := hc.2 d
    have hxd : segreCoord y d ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => (hz.2 k (d k) (hd k)).1
    have hxc : segreCoord y c ≠ 0 := hc.1
    have hone : t * ∏ k, s k = 1 := by
      refine hinj ?_
      rw [map_mul, map_prod, ht, map_one]
      simp only [hs]
      rw [Finset.prod_div_distrib]
      change segreCoord y d / segreCoord y c * (segreCoord y c / segreCoord y d) = 1
      field_simp
    have hval := congrArg ev hone
    rw [map_mul, map_prod, map_one] at hval
    simp only [hv] at hval
    have hr : ∏ k, r k ≠ 0 := right_ne_zero_of_mul_eq_one hval
    intro k
    rw [hw k]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.1 hr k (Finset.mem_univ k)) (hd k).ne_zero
  · obtain ⟨s, hs⟩ : ∃ s, gv s = f := hf.2.1
    obtain ⟨t, ht⟩ : ∃ t, gv t = f⁻¹ := hf.2.2
    have hone : s * t = 1 := by
      refine hinj ?_
      rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hf.1]
    have hval := congrArg ev hone
    rw [map_mul, map_one] at hval
    exact ⟨ev s, (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w h hz f _).1 ⟨h, s, hs, rfl⟩,
      left_ne_zero_of_mul_eq_one hval⟩

variable {F : Type} [AddCommGroup F] [Module Ω F] {r : ℕ} {W : ChartBundle ℤ (segreCoord y) r F} {L : Lat ξ F}

theorem exists_frames_on_chart (hT : CoordTie ℤ ξ (segreCoord y)) (hV : L.IsVB r ⊤)
    (hC : L.IsChartOf (segreCoord y) W.lat) (c : (k : K) → J k) (hc : segreCoord y c ≠ 0) :
    ∃ S : Set (Ω × (Fin r → F)), S.Finite ∧ (∀ a ∈ S, IsFrameOver y W c a.1 a.2) ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → ∃ a ∈ S, unitAt ξ p a.1 := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have loc : ∀ q : U, ∃ (g : Γ(X, U)) (b : Fin r → F), q.1 ∈ X.basicOpen g ∧
      ∀ p : Cpt ξ, p.1 ∈ X.basicOpen g → L.IsFrameAt b p := by
    intro q
    obtain ⟨h, -⟩ := (hmem q.1).1 q.2
    obtain ⟨V, hqV, b, -, hb⟩ := hV ⟨q.1, h⟩ (Set.mem_univ _)
    obtain ⟨g, hgV, hqg⟩ := hU.exists_basicOpen_le (V := V) ⟨q.1, hqV⟩ q.2
    exact ⟨g, b, hqg, fun p hp => hb p (Set.mem_univ _) (hgV hp)⟩
  choose g b hq hfr using loc
  have hsp : ∀ q : U, genPt ξ ⤳ q.1 := fun q => ((hmem q.1).1 q.2).1
  have hpU : ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → p.1 ∈ U :=
    fun p hp => (hmem p.1).2 ⟨p.2, hp⟩
  let v : U → Ω := fun q => genMap ξ ⟨q.1, hsp q⟩ (X.presheaf.germ U q.1 q.2 (g q))
  have hv : ∀ (q : U) (p : Cpt ξ) (hp : p.1 ∈ U), v q = genMap ξ p (X.presheaf.germ U p.1 hp (g q)) :=
    fun q p hp => genMap_germ_eq (g q) ⟨q.1, hsp q⟩ p q.2 hp
  have hunit : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → p.1 ∈ X.basicOpen (g q) → unitAt ξ p (v q) := by
    intro q p hp hb
    rw [hv q p hp]
    exact unitAt_of_isUnit ((Scheme.mem_basicOpen _ _ _ hp).1 hb)
  have hbasic : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → unitAt ξ p (v q) → p.1 ∈ X.basicOpen (g q) := by
    intro q p hp hu
    rw [hv q p hp] at hu
    exact (Scheme.mem_basicOpen _ _ _ hp).2 (isUnit_of_unitAt hT.gen hu)
  have hcov : (U : Set X) ⊆ ⋃ q : U, (X.basicOpen (g q) : Set X) :=
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hq _⟩
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover _ (fun q => (X.basicOpen (g q)).isOpen) hcov
  refine ⟨(fun q => (v q, b q)) '' (↑t : Set _), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    have hne : v q ≠ 0 := (hunit q ⟨q.1, hsp q⟩ q.2 (hq q)).1
    have hring : v q ∈ chartRing ℤ (segreCoord y) c :=
      (hT.ring c hc (v q)).2 fun p hp => ⟨_, (hv q p (hpU p hp)).symm⟩
    exact (GlobalTheory.T.segre_chart_bundle X Ω ξ K J y F r W L hT hV hC c (v q) (b q) hc hring hne).2
      fun p hp hu => hfr q p (hbasic q p (hpU p hp) hu)
  · intro p hp
    obtain ⟨q, hqt, hqp⟩ := Set.mem_iUnion₂.1 (ht (hpU p hp))
    exact ⟨_, ⟨q, hqt, rfl⟩, hunit q p (hpU p hp) hqp⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrames

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem exists_frames_cover_mcPts : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F : Type) [AddCommGroup F] [Module Ω F] (r : ℕ) (W : ChartBundle ℤ (segreCoord y) r F) (L : Lat ξ F), CoordTie ℤ ξ (segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (segreCoord y) W.lat → ∃ (m : ℕ) (ch : Fin m → (k : K) → J k) (fr : Fin m → Ω) (b : Fin m → Fin r → F), (∀ i, IsFrameOver y W (ch i) (fr i) (b i)) ∧ ∀ w ∈ mcPts (mCoordIdeal y), ∃ i, InFrameDomain y (ch i) (fr i) w := by
  classical
  intro X Ω _ ξ K _ J _ y F _ _ r W L hT hV hC
  have hloc := fun c : {c : (k : K) → J k // segreCoord y c ≠ 0} =>
    ChartFrames.exists_frames_on_chart (W := W) (L := L) hT hV hC c.1 c.2
  choose S hfin hframe hcov using hloc
  let T : Set (((k : K) → J k) × Ω × (Fin r → F)) :=
    ⋃ c, (fun a : Ω × (Fin r → F) => (c.1, a.1, a.2)) '' S c
  have hTfin : T.Finite := Set.finite_iUnion fun c => (hfin c).image _
  haveI := hTfin.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨m, fun i => (e.symm i).1.1, fun i => (e.symm i).1.2.1, fun i => (e.symm i).1.2.2, ?_, ?_⟩
  · have hall : ∀ t ∈ T, IsFrameOver y W t.1 t.2.1 t.2.2 := by
      intro t ht
      obtain ⟨c, a, ha, rfl⟩ := Set.mem_iUnion.1 ht
      exact hframe c a ha
    exact fun i => hall _ (e.symm i).2
  · intro w hw
    obtain ⟨z, h, hz⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hw
    obtain ⟨c, hc⟩ := hT.cover ⟨centre z, h⟩
    obtain ⟨a, ha, hu⟩ := hcov ⟨c, hc.1⟩ ⟨centre z, h⟩ hc
    have hmem : (c, a.1, a.2) ∈ T := Set.mem_iUnion.2 ⟨⟨c, hc.1⟩, a, ha, rfl⟩
    refine ⟨e ⟨_, hmem⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ChartFrames.inFrameDomain_of_unitAt hT hz h hc hu

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExpHomBijectiveOfLocalInj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LbMarking

theorem linearLift_bijective_of_discrete_kernels : ∀ (M : Type) [Group M] (g g' : ℕ) (ex : (Fin g' → ℂ) → M) (r : (Fin g → ℂ) → M) (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z w, ex (z + w) = ex z * ex w) → (∀ x, ex (h x) = r x) → Function.Surjective r → (∃ δ : ℝ, 0 < δ ∧ ∀ x, ‖x‖ < δ → r x = 1 → x = 0) → (∃ δ : ℝ, 0 < δ ∧ ∀ y, ‖y‖ < δ → ex y = 1 → y = 0) → Function.Bijective h := by
  intro M _ g g' ex r h hadd hr hsurj ⟨δ, hδ, hsep⟩ ⟨ε, hε, hsep'⟩
  have hex0 : ex 0 = 1 := by
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact left_eq_mul.mp h0
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hne
    have hs : 0 < δ / (2 * ‖x‖) := by positivity
    have ht : ((δ / (2 * ‖x‖) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hs.ne'
    have h1 : r (((δ / (2 * ‖x‖) : ℝ) : ℂ) • x) = 1 := by
      rw [← hr, map_smul, hx, smul_zero, hex0]
    have h2 : ‖((δ / (2 * ‖x‖) : ℝ) : ℂ) • x‖ < δ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      have : δ / (2 * ‖x‖) * ‖x‖ = δ / 2 := by
        field_simp
      rw [this]
      linarith
    have h3 := hsep _ h2 h1
    exact hne ((smul_eq_zero.mp h3).resolve_left ht)
  · intro v
    by_contra hv
    have hsub : ∀ a b, ex a = 1 → ex b = 1 → a ≠ b → ε ≤ ‖a - b‖ := by
      intro a b ha hb hab
      by_contra hlt
      have h1 : ex (a - b) = 1 := by
        have h2 := hadd (a - b) b
        rw [sub_add_cancel, ha, hb, _root_.mul_one] at h2
        exact h2.symm
      exact hab (sub_eq_zero.mp (hsep' _ (not_le.mp hlt) h1))
    have hK : {y | ex y = 1}.Countable := by
      have hdisj : ({y | ex y = 1} : Set (Fin g' → ℂ)).PairwiseDisjoint
          (fun y => ball y (ε / 2)) := by
        intro a ha b hb hab
        refine Set.disjoint_left.mpr ?_
        intro z hza hzb
        have h1 := hsub a b ha hb hab
        have h2 : dist z a < ε / 2 := hza
        have h3 : dist z b < ε / 2 := hzb
        have h4 : dist a b ≤ dist z a + dist z b := dist_triangle_left a b z
        rw [dist_eq_norm a b] at h4
        linarith
      exact hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
        (fun y _ => ⟨y, mem_ball_self (half_pos hε)⟩)
    choose x hx using fun t : ℂ => hsurj (ex (t • v))
    have hkK : ∀ t, ex (t • v - h (x t)) = 1 := by
      intro t
      have h2 := hadd (t • v - h (x t)) (h (x t))
      rw [sub_add_cancel, hr, hx t] at h2
      exact right_eq_mul.mp h2
    have hinj : Function.Injective (fun t : ℂ =>
        (⟨t • v - h (x t), hkK t⟩ : {y | ex y = 1})) := by
      intro s t hst
      by_contra hne
      have h1 : s • v - h (x s) = t • v - h (x t) := congrArg Subtype.val hst
      have hc : s - t ≠ 0 := sub_ne_zero.mpr hne
      apply hv
      refine ⟨(s - t)⁻¹ • (x s - x t), ?_⟩
      have h2 : (s - t) • v = h (x s - x t) := by
        rw [map_sub, sub_smul]
        rw [sub_eq_sub_iff_add_eq_add] at h1 ⊢
        rw [h1, add_comm]
      rw [map_smul, ← h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    haveI : Countable {y | ex y = 1} := hK.to_subtype
    have hC : Countable ℂ := hinj.countable
    have hle := Cardinal.mk_le_aleph0_iff.mpr hC
    rw [Cardinal.mk_complex] at hle
    exact absurd Cardinal.aleph0_lt_continuum (not_lt.mpr hle)

end GlobalTheory.CompanionTheory.Ar.LbMarking
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_index_of_isPreconnected : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B → IsPreconnected B → B.Nonempty → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ∃ i : Fin FU.n, ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b := by
  intro E _ _ _ H D l Xo σ g ty FU m B y hB hpre hne hs hy
  let S : Fin FU.n → Set (Fin m → ℂ) := fun i => {b₀ | ∃ (B' : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b}
  have hopen : ∀ i, IsOpen (S i) := by
    intro i
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro b₀ ⟨B', P, hB', hb₀, hsub, hP, hu⟩
    exact ⟨B', fun b hb => ⟨B', P, hB', hb, hsub, hP, hu⟩, hB', hb₀⟩
  have hcover : ∀ b ∈ B, ∃ i, b ∈ S i := by
    intro b hb
    obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := FU.lift m B y hB hs hy b hb
    exact ⟨i, B', P, hB', hb', hsub, hP, hu⟩
  have hdisj : ∀ i j b, b ∈ S i → b ∈ S j → i = j := by
    rintro i j b ⟨B₁, P₁, -, hb₁, -, hP₁, hu₁⟩ ⟨B₂, P₂, -, hb₂, -, hP₂, hu₂⟩
    exact FU.disj i j (P₁ b) (P₂ b) (hP₁.1 b hb₁) (hP₂.1 b hb₂) ((hu₁ b hb₁).trans (hu₂ b hb₂).symm)
  obtain ⟨b₁, hb₁⟩ := hne
  obtain ⟨i, hi⟩ := hcover b₁ hb₁
  have hsub : B ⊆ S i := by
    refine IsPreconnected.subset_left_of_subset_union (v := ⋃ j ∈ {j | j ≠ i}, S j) (hopen i)
      (isOpen_biUnion fun j _ => hopen j) ?_ ?_ ⟨b₁, hb₁, hi⟩ hpre
    · refine Set.disjoint_left.2 fun b hbi hbT => ?_
      obtain ⟨j, hj, hbj⟩ := Set.mem_iUnion₂.1 hbT
      exact hj (hdisj i j b hbi hbj).symm
    · intro b hb
      obtain ⟨j, hj⟩ := hcover b hb
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, hj⟩)
  exact ⟨i, fun b₀ hb₀ => hsub hb₀⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOnLogResolutionCorrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_on_log_resolution_corr : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P Jd : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P Jd D) (Ψ : Type) (N : ℕ) (T : Ψ × Fin N → HermLine J), (∀ r, IsFlatOn R (T r)) → ∀ a, IsFlatOn R (corr T a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr | exact GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem inChart_unitAt_of_inFrameDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segreCoord y) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f : Ω) (h : genPt ξ ⤳ centre z), CoordsAt ξ y z w → InFrameDomain y cc f w → InChart ξ (segreCoord y) cc ⟨centre z, h⟩ ∧ unitAt ξ ⟨centre z, h⟩ f := by
  intro X Ω _ ξ K _ J _ y hT z w cc f h hw hd
  have hu : ∀ k, IsUnit (w ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (hd.1 k)
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hw.2 k (cc k) (hu k)).1
  have reg : ∀ {a : Ω} {r : ℂ}, ValAt ξ z a r → a ∈ regAt ξ ⟨centre z, h⟩ := by
    rintro a r ⟨_, s, hs, -⟩
    exact ⟨s, hs⟩
  refine ⟨⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩, ?_⟩
  · choose r hr _ using fun k => (hw.2 k (cc k) (hu k)).2 (c' k)
    have hp : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, y ⟨k, c' k⟩ / y ⟨k, cc k⟩) (∏ k ∈ s, r k) := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using CxVal.one h
      | insert k s hk ih =>
        rw [Finset.prod_insert hk, Finset.prod_insert hk]
        exact CxVal.mul (hr k) ih
    have e : segreCoord y c' / segreCoord y cc = ∏ k, y ⟨k, c' k⟩ / y ⟨k, cc k⟩ := by
      simp only [segreCoord, Finset.prod_div_distrib]
    rw [e]
    exact reg (hp Finset.univ)
  · obtain ⟨v, hv, hv0⟩ := hd.2
    have hf : ValAt ξ z f v := (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w h hw f v).2 hv
    refine ⟨?_, reg hf, reg (CxVal.inv hf hv0)⟩
    obtain ⟨_, s, hs, hsv⟩ := hf
    have hs0 : (Scheme.stalkClosedPointTo z).hom s ≠ 0 := by rw [hsv]; exact hv0
    have := (CxVal.isUnit s hs0).map (genMap ξ ⟨centre z, h⟩)
    rw [hs] at this
    exact this.ne_zero

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectorsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_point_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S)) → ∃ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) ∧ (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) ∧ ∀ U : Set (Xo.XF c), Set.range y ⊆ U → IsFramed U τ (ψ.comp (algebraMap c.F S)) y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt | exact GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionWeilPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.full_torsion_weil_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ n : ℕ, FullTorsion G ξ n → FullTorsion G' ξ' n ∧ ∀ e, GenWeil G L ξ n e → ∃ e', GenWeil G' L' ξ' n e' ∧ ∀ (x g : Over.mk ξ ⟶ G) (x' g' : Over.mk ξ' ⟶ G'), x ^ n = 1 → g ^ n = 1 → x'.left ≫ φ = spMap i ≫ x.left → g'.left ≫ φ = spMap i ≫ g.left → (e' x' g' : Ω') = i (e x g) := by
  first | exact @PositivityTheory.HtPt.Mk.ht_weil_pull | exact PositivityTheory.HtPt.Mk.ht_weil_pull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsGoodStatement
section
namespace GlobalTheory.CompanionTheory.Ggeo

theorem blockProjection_genericPoints_good : GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement :=
  GlobalTheory.CompanionTheory.Ar.PB.BaseCount.generic_points_good_for_intersection

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixConjugation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem dualMap_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : R) :
    dualMap φ (algebraMap R (DualNumber R) a) = algebraMap R' (DualNumber R') (φ a) := by
  change dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)
  exact TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem centre_conj (z : Spec (CommRingCat.of ℂ) ⟶ X) : centre (spMap (starRingEnd ℂ) ≫ z) = centre z := by
  have h : (spMap (starRingEnd ℂ)) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact congrArg (fun p => z p) h

theorem extends_conj (M : LieModel G ξ E) {x x' : X} (hx : x = x') (h : genPt ξ ⤳ x) (h' : genPt ξ ⤳ x') (e : E)
    (v : epsAt (X.fromSpecStalk x) ⟶ G) (hv : M.Extends ⟨x, h⟩ e v)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of ℂ) (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of ℂ)
    (H : Spec.map φ' ≫ X.fromSpecStalk x' = spMap (starRingEnd ℂ) ≫ Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ v' : epsAt (X.fromSpecStalk x') ⟶ G, M.Extends ⟨x', h'⟩ e v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ'.hom)) ≫ v'.left =
        spMap (dualMap (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v.left := by
  subst hx
  refine ⟨v, hv, ?_⟩
  have h1 : Spec.map φ' = Spec.map (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)) := by
    rw [← cancel_mono (X.fromSpecStalk x), H, Spec.map_comp, Category.assoc]
  have h2 : φ' = φ ≫ CommRingCat.ofHom (starRingEnd ℂ) := Spec.map_injective h1
  subst h2
  have h3 : dualMap (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom =
      (dualMap (starRingEnd ℂ)).comp (dualMap φ.hom) := dualMap_comp _ _
  rw [h3, CommRingCat.ofHom_comp, Spec.map_comp]
  exact Category.assoc _ _ _

def conjVec (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : epsAt z ⟶ G) : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (by
    have h1 : w.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z := Over.w w
    have h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) =
        CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) :=
      CommRingCat.hom_ext (RingHom.ext fun a => dualMap_algebraMap (starRingEnd ℂ) a)
    have h3 := congrArg Spec.map h2
    simp only [Spec.map_comp] at h3
    simp only [Over.mk_hom, Category.assoc, h1]
    rw [← Category.assoc, h3, Category.assoc])

theorem valAt_conj (M : LieModel G ξ E) (z : Spec (CommRingCat.of ℂ) ⟶ X) (e : E) (w : epsAt z ⟶ G)
    (hw : M.ValAt z e w) : M.ValAt (spMap (starRingEnd ℂ) ≫ z) e (conjVec z w) := by
  obtain ⟨h, v, hv, hl⟩ := hw
  have hc := centre_conj z
  have h' : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z) := hc ▸ h
  obtain ⟨v', hv', hl'⟩ := extends_conj M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z)
    (Scheme.stalkClosedPointTo (spMap (starRingEnd ℂ) ≫ z)) (by
      refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap (starRingEnd ℂ) ≫ z)).trans ?_
      exact congrArg (spMap (starRingEnd ℂ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)
  refine ⟨h', v', hv', ?_⟩
  have : (conjVec z w).left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left := rfl
  rw [this, hl]
  exact hl'.symm

theorem gramAt_conj_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L (spMap (starRingEnd ℂ) ≫ z) b (Γ.map (starRingEnd ℂ)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z r b Γ ⟨v, hv, hG⟩
  refine ⟨fun i => conjVec z (v i), fun i => valAt_conj 𝔐.M z (b i) (v i) (hv i), fun p q => ?_⟩
  exact GlobalTheory.T.hodge_inner_product_conjugate E H 𝔐.X 𝔐.t z (v p) (v q) (conjVec z (v p)) (conjVec z (v q)) (Γ p q) rfl rfl (hG p q)

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_fourth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (r : CMType H × Fin (D.p + D.q)), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → (Fl₀.rootLat r).IsDegOn Set.univ y₀ a₀ e₀ → (Fl.rootLat r).IsDegOn Set.univ y a e → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt 𝔐₀.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit | exact GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit <;> assumption)
end

