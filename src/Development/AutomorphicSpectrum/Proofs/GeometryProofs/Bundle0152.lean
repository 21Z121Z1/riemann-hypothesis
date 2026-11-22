import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0050
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0144
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0139
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0146
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0101
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReferenceGeometryMultihomogForm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_finite_projective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E :=
  PositivityTheory.HtPt.Htat.lie_fin

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_pullback_action_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X)
    (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
    (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω' V')
    (j : V →+ V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) →
    ∀ a e, j (ρ a e) = ρ' a (j e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull | exact GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelWithCmActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_with_cm_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsPeriod (FU.Di i) ty P → ∃ (M : LieModel Xo.univ.t.G (FU.u i P) (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ a w, ρ a w = fun k => ty k (a : E) * w k) ∧ (∀ w, IsDerivAt0 (fun z => (FU.ex i P z).left) w (M.pt w).left) ∧ ∀ τ w, HT.eigProj ρ τ w = tyPart ty τ w := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action | exact GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LiftGenericPointOverIsoOpenStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_generic_point_over_iso_open : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coords.dense_point_lift | exact GlobalTheory.CompanionTheory.Ar.Coords.dense_point_lift | (intros; apply GlobalTheory.CompanionTheory.Ar.Coords.dense_point_lift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleFromUnitRatiosStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_from_unit_ratios : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X] (I : Type) (V : Option I → X.Opens) (T : I → Ω), IsCptGen ξ → (∀ i, ∀ q ∈ V (some i), genPt ξ ⤳ q) → (∀ q ∈ V none, ¬ genPt ξ ⤳ q) → (∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q), q ∈ V (some i) → q ∈ V (some j) → unitAt ξ ⟨q, hq⟩ (T j / T i)) → (⨆ i, V i = ⊤) → ∃ g : ∀ i j, Γ(X, V i ⊓ V j)ˣ, (LB.mk (Option I) V g).IsLB ∧ ∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ V (some i) ⊓ V (some j)), genMap ξ ⟨q, hq⟩ (X.presheaf.germ _ q h (g (some i) (some j)).val) = T j / T i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition.exists_transition | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition.exists_transition | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition.exists_transition <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_periods_conjugate_exists : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L' : Flat.LogPeriods n a g Λ), ∃ L : Flat.LogPeriods n a g Λ, (∀ w x, L.P w x = star (L'.P (star w) x)) ∧ ∀ z, L.H z = (L'.H (star z)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods | exact GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OverlappingAnalyticChartsRatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.overlapping_analytic_charts_ratio : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U U' : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T T' : Ω) (d d' : ℕ) (B : Set (Fin d → ℂ)) (B' : Set (Fin d' → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (Y' : (Fin d' → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) (H' : (Fin d' → ℂ) → ℂ) (b₁ : Fin d → ℂ) (b₂ : Fin d' → ℂ) (r : ℂ), IsCptGen ξ → HChart s ξ W U F T B Y H → HChart s ξ W U' F T' B' Y' H' → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U → q ∈ W → unitAt ξ ⟨q, hq⟩ T) → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U' → q ∈ W → unitAt ξ ⟨q, hq⟩ T') → b₁ ∈ B → b₂ ∈ B' → Y b₁ = Y' b₂ → ValAt ξ (Y b₁) (T' / T) r → H b₁ = r * H' b₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare.eq_val_mul | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare.eq_val_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare.eq_val_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointCoordsExistStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_point_coords_exist : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (r : ℕ) (p : Sp Ω ⟶ PSpace ℚ r), ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point | exact GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point | (intros; apply GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointImageReducedStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_point_image_reduced : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (hx : x ≠ 0), IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant | exact GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RationalRelationInChartIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartDehom

theorem den_mul_algebraMap {F : Type} [Field F] [CharZero F] (q : ℚ) :
    (q.den : F) * algebraMap ℚ F q = (q.num : F) := by
  have hd : (q.den : F) ≠ 0 := by exact_mod_cast q.den_nz
  rw [eq_ratCast, Rat.cast_def]
  field_simp

theorem exists_homog {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {Q : Type} [CommRing Q] (ρ : MvPolynomial (Σ k, J k) ℤ →+* Q)
    (τ : MvPolynomial (Σ k, J k) ℚ →+* Q)
    (hρ : ∀ k, ρ (X ⟨k, c k⟩) = 1) (hX : ∀ p, ρ (X p) = τ (X p))
    (hQ : ∀ q : ℚ, (q.den : Q) * τ (MvPolynomial.C q) = (q.num : Q))
    (G : MvPolynomial (Σ k, J k) ℚ) :
    ∃ (N : ℤ) (D : K → ℕ) (H : MvPolynomial (Σ k, J k) ℤ), N ≠ 0 ∧
      mConeMap y H = MvPolynomial.C (N : Ω) *
        (∏ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ^ D k) *
        MvPolynomial.C (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G) ∧
      ρ H = (N : Q) * τ G := by
  classical
  set u : (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hu
  set w : K → MvPolynomial K Ω := fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k with hw
  let M : (K → ℕ) → MvPolynomial (Σ k, J k) ℤ := fun D => ∏ k, X ⟨k, c k⟩ ^ D k
  have hXc : ∀ p, mConeMap y (X p) = MvPolynomial.C (y p) * X p.1 := by
    intro p; simp [mConeMap]
  have hMc : ∀ D, mConeMap y (M D) = ∏ k, w k ^ D k := by
    intro D
    simp only [M, map_prod, map_pow, hXc, hw]
  have hMρ : ∀ D, ρ (M D) = 1 := by
    intro D
    simp only [M, map_prod, map_pow, hρ, one_pow, Finset.prod_const_one]
  have hW : ∀ D E : K → ℕ, (∏ k, w k ^ D k) * ∏ k, w k ^ E k = ∏ k, w k ^ (D + E) k := by
    intro D E
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hS : ∀ a, ∏ k, w k ^ (Pi.single a 1 : K → ℕ) k = w a := by
    intro a
    rw [Finset.prod_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
    simp
  have hCc : ∀ n : ℤ, mConeMap y (MvPolynomial.C n) = MvPolynomial.C (n : Ω) := by
    intro n
    have h := (mConeMap y).commutes n
    simpa [MvPolynomial.algebraMap_eq] using h
  have hCρ : ∀ n : ℤ, ρ (MvPolynomial.C n) = (n : Q) := fun n =>
    eq_intCast (ρ.comp MvPolynomial.C) n
  induction G using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, 0, MvPolynomial.C q.num, by exact_mod_cast q.den_nz, ?_, ?_⟩
    · rw [hCc, aeval_C]
      simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one]
      rw [_root_.mul_one, ← map_mul]
      congr 1
      have := den_mul_algebraMap (F := Ω) q
      push_cast
      exact this.symm
    · rw [hCρ]
      have := hQ q
      push_cast
      exact this.symm
  | add f g hf hg =>
    obtain ⟨N₁, D₁, H₁, h₁, c₁, r₁⟩ := hf
    obtain ⟨N₂, D₂, H₂, h₂, c₂, r₂⟩ := hg
    refine ⟨N₁ * N₂, D₁ + D₂,
      MvPolynomial.C N₂ * H₁ * M D₂ + MvPolynomial.C N₁ * H₂ * M D₁, mul_ne_zero h₁ h₂, ?_, ?_⟩
    · rw [map_add, map_mul, map_mul, map_mul, map_mul, c₁, c₂, hMc, hMc, hCc, hCc, ← hW, map_add,
        map_add]
      push_cast
      rw [MvPolynomial.C_mul]
      ring
    · rw [map_add, map_mul, map_mul, map_mul, map_mul, r₁, r₂, hMρ, hMρ, hCρ, hCρ, map_add]
      push_cast
      ring
  | mul_X f p hf =>
    obtain ⟨N, D, H, h, c₁, r₁⟩ := hf
    refine ⟨N, D + Pi.single p.1 1, H * X p, h, ?_, ?_⟩
    · have hp : MvPolynomial.C (y p) * X p.1 = MvPolynomial.C (u p) * w p.1 := by
        rw [hw]
        simp only
        rw [← _root_.mul_assoc, ← MvPolynomial.C_mul, hu]
        simp only
        rw [div_mul_cancel₀ _ (hy p.1)]
      rw [map_mul, c₁, hXc, hp, ← hW, hS, map_mul, aeval_X, MvPolynomial.C_mul]
      ring
    · rw [map_mul, map_mul, r₁, hX]
      ring

theorem map_mem_chartIdeal : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ G : MvPolynomial (Σ k, J k) ℚ,
    aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G = (0 : Ω) →
    map (algebraMap ℚ ℂ) G ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
  intro K _ J _ Ω _ _ y c hy G hG
  classical
  set A : Ideal (MvPolynomial (Σ k, J k) ℂ) :=
    Ideal.span (Set.range fun k => (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, J k) ℂ)) with hA
  let π := Ideal.Quotient.mk A
  let ρ : MvPolynomial (Σ k, J k) ℤ →+* (MvPolynomial (Σ k, J k) ℂ ⧸ A) :=
    π.comp (MvPolynomial.map (Int.castRingHom ℂ))
  let τ : MvPolynomial (Σ k, J k) ℚ →+* (MvPolynomial (Σ k, J k) ℂ ⧸ A) :=
    π.comp (MvPolynomial.map (algebraMap ℚ ℂ))
  have hρ : ∀ k, ρ (X ⟨k, c k⟩) = 1 := by
    intro k
    have h : π (X ⟨k, c k⟩) = π 1 :=
      Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨k, rfl⟩)
    simpa [ρ] using h
  have hX : ∀ p, ρ (X p) = τ (X p) := by
    intro p
    simp [ρ, τ]
  have hQ : ∀ q : ℚ, (q.den : MvPolynomial (Σ k, J k) ℂ ⧸ A) * τ (MvPolynomial.C q) =
      (q.num : MvPolynomial (Σ k, J k) ℂ ⧸ A) := by
    intro q
    have h := congrArg (fun a : ℂ => π (MvPolynomial.C a)) (den_mul_algebraMap (F := ℂ) q)
    simpa [τ] using h
  obtain ⟨N, D, H, hN, hc, hr⟩ := exists_homog y c hy ρ τ hρ hX hQ G
  have hHP : H ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, hc, hG]
    simp
  have h1 : MvPolynomial.map (Int.castRingHom ℂ) H ∈ pC (mCoordIdeal y) :=
    Ideal.subset_span ⟨H, hHP, rfl⟩
  have h2 : MvPolynomial.map (Int.castRingHom ℂ) H -
      MvPolynomial.C (N : ℂ) * MvPolynomial.map (algebraMap ℚ ℂ) G ∈ A := by
    refine Ideal.Quotient.eq.mp ?_
    have : π (MvPolynomial.C (N : ℂ)) = (N : MvPolynomial (Σ k, J k) ℂ ⧸ A) := by simp
    rw [map_mul, this]
    exact hr
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have h3 : MvPolynomial.C (N : ℂ) * MvPolynomial.map (algebraMap ℚ ℂ) G ∈
      ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
    have ha : MvPolynomial.map (Int.castRingHom ℂ) H ∈
        ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := Ideal.mem_sup_left h1
    have hb : MvPolynomial.map (Int.castRingHom ℂ) H -
        MvPolynomial.C (N : ℂ) * MvPolynomial.map (algebraMap ℚ ℂ) G ∈
        ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := Ideal.mem_sup_right h2
    simpa using Ideal.sub_mem _ ha hb
  have h4 := Ideal.mul_mem_left _ (MvPolynomial.C (N : ℂ)⁻¹) h3
  rwa [← _root_.mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hN', MvPolynomial.C_1, _root_.one_mul] at h4

end GlobalTheory.CompanionTheory.Ar.ChartDehom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReferenceGeometryMultihomogFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reference_geometry_multihomog_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β₀ : O →+* c.F) (Y : Model Xo c β₀) (G : RefGeo Y), ∃ (β : MRing G.J) (dβ : G.K → ℕ), IsMultiHomog β dβ ∧ β ∉ mCoordIdeal G.y ∧ MvPolynomial.aeval G.y β ≠ 0 ∧ MvPolynomial.aeval G.y β ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1 ∧ ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G → ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p → ¬ unitAt G.𝔐.ξ p (MvPolynomial.aeval G.y β * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form | exact GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form | (intros; apply GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedFieldStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_values_in_adjoined_field : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A) (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')), valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification | exact GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification <;> assumption)
end

