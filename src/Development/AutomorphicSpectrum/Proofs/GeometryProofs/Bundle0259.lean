import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdeg
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0257
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullTorsionNumberField
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagWeightedDegreeSection
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0200
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0255
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0258
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0203
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0204
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.BdSym

theorem boundary_closed_torus_conj : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (T : Set X) (bd : Ideal (MRing J)), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ centre z ∉ T)) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) ∧ (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) ∧ ∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, conjVec z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd := by
  intro X Ω _ ξ K _ J _ y T bd hT hbd
  have key := GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT
  refine ⟨?_, ?_, ?_⟩
  · have e : ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) =
        ⋂ f ∈ bd, {w : mcPts (mCoordIdeal y) |
          MvPolynomial.eval w.1 (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} := by
      ext w
      have hw : w.1 ∈ mcPts (mCoordIdeal y) := w.2
      rw [Set.mem_iInter₂]
      simp only [mcPts, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq] at hw ⊢
      exact ⟨fun h => h.2.2, fun h => ⟨hw, hw.1, h⟩⟩
    rw [e]
    refine isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (MvPolynomial.continuous_eval _).comp continuous_subtype_val
  · rintro w ⟨hw1, hw2⟩ c hc
    obtain ⟨z, hz, hzw⟩ := (key w).1 hw1
    have hzc : CoordsAt ξ y z (torusSmul c w) := by
      have h' := hzw
      unfold CoordsAt at h' ⊢
      refine ⟨fun k => ?_, fun k i hu => ?_⟩
      · obtain ⟨i, hi⟩ := h'.1 k
        refine ⟨i, isUnit_iff_ne_zero.2 ?_⟩
        show c k * w ⟨k, i⟩ ≠ 0
        exact mul_ne_zero (hc k) (isUnit_iff_ne_zero.1 hi)
      · have hu' : IsUnit (w ⟨k, i⟩) := by
          refine isUnit_iff_ne_zero.2 fun h0 => isUnit_iff_ne_zero.1 hu ?_
          show c k * w ⟨k, i⟩ = 0
          rw [h0, mul_zero]
        obtain ⟨hy, hr⟩ := h'.2 k i hu'
        refine ⟨hy, fun j => ?_⟩
        obtain ⟨r, hr1, hr2⟩ := hr j
        refine ⟨r, hr1, ?_⟩
        show c k * w ⟨k, j⟩ = r * (c k * w ⟨k, i⟩)
        rw [hr2]
        ring
    exact Set.mem_inter ((key _).2 ⟨z, hz, hzc⟩) ((hbd z _ hzc).2 ((hbd z w hzw).1 hw2))
  · rintro w ⟨hw1, hw2⟩
    obtain ⟨z, hz, hzw⟩ := (key w).1 hw1
    have hzc := GlobalTheory.CompanionTheory.Ar.HodgeLine.coordsAt_conj hzw
    have hcz : centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) = centre z := GlobalTheory.CompanionTheory.Ar.HodgeLine.centre_cj z
    have hz' : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) := by
      rw [hcz]
      exact hz
    have hT' : centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) ∉ T := by
      rw [hcz]
      exact (hbd z w hzw).1 hw2
    exact Set.mem_inter ((key (conjVec w)).2 ⟨GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z, hz', hzc⟩) ((hbd _ _ hzc).2 hT')

end GlobalTheory.CompanionTheory.Ar.BdSym
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFourthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_hodge_fourth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (e e' : Or.𝔐.Li) (v v' : epsAt z ⟶ Or.𝔐.t.G) (a : ℂ), Or.𝔐.Interior z → e ∈ Or.𝔐.Vgen (Or.bg τ) → e' ∈ Or.𝔐.Vgen (Or.sm τ) → Or.𝔐.M.ValAt z e v → Or.𝔐.M.ValAt z e' v' → HodgeIP Or.𝔐.t.G Or.𝔐.t.PP.L z v v' a → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.hodgeInnerProduct_blocks_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.hodgeInnerProduct_blocks_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.hodgeInnerProduct_blocks_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeThirdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_hodge_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → ∃ G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G ∧ G.PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks | exact GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks | (intros; apply GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConjugatePointSameCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.CoordConj

theorem centre_and_coords_conj : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), centre (spMap (starRingEnd ℂ) ≫ z) = centre z ∧ (CoordsAt ξ y z w → CoordsAt ξ y (spMap (starRingEnd ℂ) ≫ z) (conjVec w)) := by
  intro X Ω _ ξ K _ J _ y z w
  exact ⟨GlobalTheory.CompanionTheory.Ar.HodgeLine.centre_cj z, fun h => GlobalTheory.CompanionTheory.Ar.HodgeLine.coordsAt_conj h⟩

end GlobalTheory.CompanionTheory.Ar.CoordConj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullTorsionNumberFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_full_torsion_number_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (m : ℕ), 1 ≤ m → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K) (x : Fin (m ^ (2 * D.g)) → (Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G)), (∀ i, x i ^ m = 1) ∧ ∀ (F : Type) [Field F] (f : K →+* F) (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G), b = spMap f ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) → y ^ m = 1 → ∃! i, y.left = spMap f ≫ (x i).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational | exact GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagWeightedDegreeSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_weighted_degree_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (A : HermLine J) (τ : CMType H) (t₀ : ℝ) (c₁ : Ω) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), Fl.RootLines xdeg e → (∀ r, Fl.IsHodgeLine r (e r) (hx r)) → A.a = ∑ i, xdeg (τ, i) → (∀ w' : (Σ k, J k) → ℂ, CoordsAt 𝔐.ξ y z w' → A.h w' = ∏ i, (hx (τ, i)).h w') → CoordsAt 𝔐.ξ y z w → 𝔐.Interior z → c₁ ≠ 0 → (∀ (hc : genPt 𝔐.ξ ⤳ centre z) (bp : Fin D.p → 𝔐.Li) (bq : Fin D.q → 𝔐.Li) (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ) (α κ : Ω) (u : ℂ), (𝔐.V (.inl τ)).IsFrameAt bp ⟨centre z, hc⟩ → (𝔐.V (.inr τ)).IsFrameAt bq ⟨centre z, hc⟩ → 𝔐.M.GramAt 𝔐.t.PP.L z bp Γ → 𝔐.M.GramAt 𝔐.t.PP.L z bq Δ → Γ.PosDef → Δ.PosDef → (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) = α • exteriorPower.ιMulti Ω _ bp → (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) = κ • exteriorPower.ιMulti Ω _ bq → ValAt 𝔐.ξ z (c₁ * α / κ) u → Real.log ‖u‖ + (Real.log ‖Γ.det‖ - Real.log ‖Δ.det‖) / 2 = t₀) → ∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt 𝔐.ξ z (c₁ / ((∏ k, y ⟨k, cc k⟩ ^ A.a k) * ∏ i, e (τ, i))) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = Real.exp t₀ * A.h w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootGram.norm_against_root_metrics | exact GlobalTheory.CompanionTheory.Ar.RootGram.norm_against_root_metrics | (intros; apply GlobalTheory.CompanionTheory.Ar.RootGram.norm_against_root_metrics <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermSystemHeightFreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_system_height_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M), PowFns t → IsCptGen ξ → HChar S.g₀.B r → (∀ (q : Cpt ξ) (p : ℕ), p.Prime → (p : X.residueField q.1) = 0 → FibPF t q.1) → ∀ q : Cpt ξ, HFree (S.g q).B r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hfree_at_component_stalks | exact GlobalTheory.CompanionTheory.Ar.Flat.hfree_at_component_stalks | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hfree_at_component_stalks <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFifthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_fifth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (hv : IsBlockMap bk (blkV bk bx)) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (A₀ : HermLine J₀) (T : HermLine J), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → NormPull Fl₀ Fl i h → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → (∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → 𝔐₀.Interior (z ≫ h)) → e ≠ 0 → A₀.a = a₀ → T.a = a - pullDeg bk a₀ → IsRatio 𝔐.ξ y y₀ bk bx i a a₀ e e₀ T.h → Fl₀.IsHodgeLine r e₀ A₀ → Fl.IsHodgeLine r e ((pullHerm hv A₀).tensor T) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor | exact GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdegStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_flag_xdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective β → Fl.RootLines xdeg e → ∀ r, ∃ A : HermLine J, A.a = xdeg r ∧ Fl.IsHodgeLine r (e r) A ∧ IsConjInvariantH A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeLine.exists_hodgeLine | exact GlobalTheory.CompanionTheory.Ar.HodgeLine.exists_hodgeLine | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeLine.exists_hodgeLine <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_hodge_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → gramAt (Dc.h τ) b w = G := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge | exact GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_hodge_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (d d' : MuFrameAt Hd w) (s s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (Γ Γ' : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → Or.IsSmallPart d s → Or.IsSmallPart d' s' → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s' τ) (Γ' τ)) → (∀ τ, (Γ τ).PosDef) → ‖valAt Dc.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ τ).det.re = ‖valAt Dc.y d'.u w‖ * (∏ k, ‖w ⟨k, d'.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ' τ).det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep | exact GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep <;> assumption)
end

