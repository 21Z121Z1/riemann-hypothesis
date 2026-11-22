import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationCompact
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSum
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordRelationsHomogeneous
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeReindexedCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapTangentCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PeriodCoord

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {A R : Type} [CommRing A] [CommRing R]

theorem dualMap_comp_base (i : Sp A ⟶ X) (θ : A →+* R) :
    spMap (dualMap θ) ≫ (epsAt i).hom = (epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i)).hom := by
  have e : (CommRingCat.ofHom (algebraMap A (DualNumber A))) ≫ CommRingCat.ofHom (dualMap θ) =
      CommRingCat.ofHom θ ≫ CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show dualMap θ (algebraMap A (DualNumber A) a) = algebraMap R (DualNumber R) (θ a)
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl]
    ext <;> simp [dualMap]
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp] at e'
  show spMap (dualMap θ) ≫ Spec.map _ ≫ i = Spec.map _ ≫ 𝟙 (Sp R) ≫ spMap θ ≫ i
  rw [Category.id_comp, ← Category.assoc, e', Category.assoc]

def pushEps (i : Sp A ⟶ X) (θ : A →+* R) (v : epsAt i ⟶ G) : epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i) ⟶ G :=
  Over.homMk (spMap (dualMap θ) ≫ v.left) (by
    have e : (spMap (dualMap θ) ≫ v.left) ≫ G.hom = (epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i)).hom := by
      rw [Category.assoc, Over.w v, dualMap_comp_base]
    exact e)

theorem isTanAt_pushEps (i : Sp A ⟶ X) (θ : A →+* R) {v : epsAt i ⟶ G} (h : IsTanAt G i v) :
    IsTanAt G (𝟙 (Sp R) ≫ spMap θ ≫ i) (pushEps i θ v) := by
  unfold IsTanAt at h ⊢
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap θ)) =
      Spec.map (CommRingCat.ofHom θ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp [dualMap]
  let s : Over.mk (𝟙 (Sp R) ≫ spMap θ ≫ i) ⟶ Over.mk i :=
    Over.homMk (spMap θ) (by simp)
  have h1 : s ≫ (1 : Over.mk i ⟶ G) = 1 := MonObj.comp_one s
  have h2 := congrArg CommaMorphism.left h1
  refine Eq.trans ?_ h2
  change _ = spMap θ ≫ (1 : Over.mk i ⟶ G).left
  rw [← h]
  change Spec.map _ ≫ spMap (dualMap θ) ≫ v.left = _
  rw [← Category.assoc, key, Category.assoc]

theorem exists_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (i : Sp A ⟶ X) (N : ℕ) (v : Fin N → (epsAt i ⟶ t.G)) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (θ : A →+* R) (m : SABMap t' t (spMap θ ≫ i)) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)), (∀ k, IsTanAt t.G i (v k)) → ∃ x : Fin N → Fin g → R, ∀ k, (M.pt (x k)).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := by
  intro E _ _ _ H X t A _ i N v R _ t' θ m g M hv
  have hx : ∀ k, ∃ e : Fin g → R, (M.pt e).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := fun k => by
    have ht : IsTanAt t'.G (𝟙 (Sp R)) ((LiePull.tanPts m.cart (𝟙 (Sp R))).symm (pushEps i θ (v k))) :=
      (LiePull.isTan_iff m.cart (𝟙 (Sp R)) _).1 (by
        rw [MulEquiv.apply_symm_apply]
        exact isTanAt_pushEps i θ (hv k))
    obtain ⟨e, he⟩ := M.onto _ ht
    refine ⟨e, ?_⟩
    rw [he, ← LiePull.pts_left m.cart (LiePull.eps_assoc (𝟙 (Sp R))), MulEquiv.apply_symm_apply]
    rfl
  choose x hx using hx
  exact ⟨x, hx⟩

end GlobalTheory.CompanionTheory.Ar.PeriodCoord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange | exact GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineDomainGenericSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames

theorem mem_prime_germ_eq_zero {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) (x : A)
    (hF : IsField (X.presheaf.stalk x.1)) (f : Γ(X, A)) (hf : f ∈ (hA.primeIdealOf x).asIdeal) :
    X.presheaf.germ A x.1 x.2 f = 0 := by
  have hl := hA.isLocalization_stalk x
  have h1 : algebraMap Γ(X, A) (X.presheaf.stalk x.1) f ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x.1)
      (hA.primeIdealOf x).asIdeal f).2 hf
  have h2 : ¬ IsUnit (algebraMap Γ(X, A) (X.presheaf.stalk x.1) f) := h1
  by_contra h0
  exact h2 (by
    let _ := hF.toField
    exact IsUnit.mk0 _ h0)

theorem germ_injective {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) [IsDomain Γ(X, A)] (x : A) :
    Function.Injective (X.presheaf.germ A x.1 x.2) := by
  have hl := hA.isLocalization_stalk x
  exact IsLocalization.injective (X.presheaf.stalk x.1)
    (M := (hA.primeIdealOf x).asIdeal.primeCompl)
    ((hA.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors)

theorem genPt_specializes_of_isDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  intro X Ω _ ξ A hA p hgen hdom hp z hz
  have hx : genPt ξ ∈ A := p.2.mem_open A.2 hp
  let x : A := ⟨genPt ξ, hx⟩
  let q : A := ⟨p.1, hp⟩
  have hF : IsField (X.presheaf.stalk x.1) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hgen.bij).toMulEquiv
  have hbot : (hA.primeIdealOf x).asIdeal = ⊥ := by
    refine le_antisymm (fun f hf => ?_) bot_le
    have h0 := mem_prime_germ_eq_zero hA x hF f hf
    have h1 : X.presheaf.germ A p.1 hp f = 0 := by
      apply hgen.inj p
      have h2 : X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f) =
          X.presheaf.germ A (genPt ξ) hx f := by
        exact congr($(X.presheaf.germ_stalkSpecializes hp p.2).hom f)
      rw [map_zero]
      change (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f)) = 0
      rw [h2]
      have h3 : X.presheaf.germ A (genPt ξ) hx f = 0 := h0
      rw [h3]
      exact map_zero (Scheme.stalkClosedPointTo ξ).hom
    exact germ_injective hA q (h1.trans (map_zero _).symm)
  obtain ⟨t, rfl⟩ : z ∈ Set.range hA.fromSpec := by rwa [hA.range_fromSpec]
  have hs : hA.primeIdealOf x ⤳ t := by
    refine (PrimeSpectrum.le_iff_specializes (hA.primeIdealOf x) t).1 ?_
    change (hA.primeIdealOf x).asIdeal ≤ _
    rw [hbot]
    exact bot_le
  have := hs.map hA.fromSpec.continuous
  rwa [hA.fromSpec_primeIdealOf] at this

end GlobalTheory.CompanionTheory.Ar.LocFrames
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticPointsFiniteCompact
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem compact_of_finite_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (Z' : Scheme.{0}) (f : Z' ⟶ XQ X), IsFinite f →
    @CompactSpace (Sp ℂ ⟶ Z') (anTop Z') :=
  @PositivityTheory.Xgn.torus_uniformization_compact

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieMetricBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_lie_metric_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_intersection_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (S₀ : Finset ℕ) (𝔐 : HodgeCpt Y S₀ Dc.y) (bg sm : CMType H → CMType H ⊕ CMType H) (i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li) (s : CMType H → Fin (Dc.N - Dc.j) → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), (∀ τ, Function.Injective (i τ)) → (∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)) → (∀ τ, bg τ ≠ sm τ) → (∀ τ, labelRk D (bg τ) = Dc.j) → (∀ τ, labelRk D (sm τ) = Dc.N - Dc.j) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsVB Dc.N ⊤) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat) → (∀ τ, LinearIndependent Ω (s τ)) → (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y aMu e₀ → ∃ Hd : HodgeData Dc, ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BigBlock.main | exact GlobalTheory.CompanionTheory.Ar.BigBlock.main | (intros; apply GlobalTheory.CompanionTheory.Ar.BigBlock.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentOpenStalksDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem stalkMap_bijective_of_flat_preimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [IsPreimmersion f] [Flat f] (x : X) :
    Function.Bijective (f.stalkMap x).hom := by
  refine ⟨?_, f.stalkMap_surjective x⟩
  have h := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem spMap_flat_preimmersion {O F : Type} [CommRing O] [Field F] (β : O →+* F) (hi : Function.Injective β)
    (hq : ∀ x : F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) : IsPreimmersion (spMap β) ∧ Flat (spMap β) := by
  haveI : IsDomain O := hi.isDomain β
  letI : Algebra O F := β.toAlgebra
  have hal : ∀ a : O, algebraMap O F a = β a := fun _ => rfl
  have hfr : IsLocalization (nonZeroDivisors O) F :=
    { map_units := fun y => by
        refine IsUnit.mk0 _ ?_
        rw [hal]
        exact fun h => nonZeroDivisors.ne_zero y.2 (hi (h.trans (map_zero β).symm))
      surj := fun z => by
        obtain ⟨a, b, hb, e⟩ := hq z
        have hb0 : b ≠ 0 := fun h => hb (by rw [h, map_zero])
        exact ⟨(a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩), e⟩
      exists_of_eq := fun {x y} e => ⟨1, by rw [hi e]⟩ }
  refine ⟨IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F), ?_⟩
  have hfl : Module.Flat O F := IsLocalization.flat F (nonZeroDivisors O)
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 hfl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem j_flat_preimmersion {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (hi : Function.Injective β) (hq : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) :
    IsPreimmersion Y.j ∧ Flat Y.j := by
  obtain ⟨h1, h2⟩ := spMap_flat_preimmersion β hi hq
  have h3 : IsPreimmersion (pullback.fst Y.s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h1
  have h4 : Flat (pullback.fst Y.s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip h2
  have := Y.jQ_open
  exact ⟨inferInstanceAs (IsPreimmersion (Y.jQ ≫ pullback.fst _ _)), inferInstanceAs (Flat (Y.jQ ≫ pullback.fst _ _))⟩

theorem cptOver_isOpen_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ U' : (Xo.XF c).Opens, (U' : Set (Xo.XF c)) = U ∧ ∀ p : Xo.XF c, p ∈ U → IsDomain ((Xo.XF c).presheaf.stalk p) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z ⟨hi, hN, hq⟩
  obtain ⟨h1, h2⟩ := j_flat_preimmersion Y hi hq
  have hP : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hLN : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have ho := isOpen_closure_genPt (Z.ξ₀ ≫ Y.j) Z.gen
  have hU : U = Y.j ⁻¹' closure {genPt (Z.ξ₀ ≫ Y.j)} := by
    ext u
    rw [Z.closure u, Set.mem_preimage, ← specializes_iff_mem_closure]
    exact (Y.j.isEmbedding.isInducing.specializes_iff).symm
  refine ⟨⟨U, hU ▸ ho.preimage Y.j.continuous⟩, rfl, fun p _ => ?_⟩
  haveI := (Y.normal (Y.j p)).1
  have hb := stalkMap_bijective_of_flat_preimmersion Y.j p
  exact ((RingEquiv.ofBijective _ hb).symm.injective.isDomain (RingEquiv.ofBijective _ hb).symm.toRingHom)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsAtFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstVal

def constGerm {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) (x : X) (o : O) :
    X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))

theorem genMap_constGerm {X : Scheme.{0}} {Ω O : Type} [Field Ω] [CommRing O] (f : O →+* Ω)
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom f)) (p : Cpt ξ) (o : O) :
    genMap ξ p (constGerm s p.1 o) = f o := by
  letI : Algebra O Ω := f.toAlgebra
  exact ConstReg.genMap_germ_const ξ s hs p o

theorem genMap_self {X : Scheme.{0}} {F : Type} [Field F] (z : Spec (CommRingCat.of F) ⟶ X)
    (x : X.presheaf.stalk (genPt z)) :
    genMap z ⟨genPt z, specializes_rfl⟩ x = (Scheme.stalkClosedPointTo z).hom x := by
  have e₀ : X.presheaf.stalkSpecializes (specializes_rfl (x := genPt z)) ≫ Scheme.stalkClosedPointTo z =
      Scheme.stalkClosedPointTo z := by
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact Category.id_comp _
  exact congrArg (fun q => q.hom x) e₀

def closedMap {X : Scheme.{0}} {F : Type} [Field F] (z : Spec (CommRingCat.of F) ⟶ X) :
    X.presheaf.stalk (centre z) →+* F :=
  (Scheme.stalkClosedPointTo z).hom

theorem closedPoint_constGerm {X : Scheme.{0}} {F O : Type} [Field F] [CommRing O] (f : O →+* F)
    (z : Spec (CommRingCat.of F) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : z ≫ s = Spec.map (CommRingCat.ofHom f)) (o : O) :
    closedMap z (constGerm s (centre z) o) = f o :=
  (genMap_self z _).symm.trans (genMap_constGerm f z s hs ⟨genPt z, specializes_rfl⟩ o)

theorem isUnit_constGerm {X : Scheme.{0}} {F O : Type} [Field F] [CommRing O] (f : O →+* F)
    (z : Spec (CommRingCat.of F) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : z ≫ s = Spec.map (CommRingCat.ofHom f)) (o : O) (ho : f o ≠ 0) :
    IsUnit (constGerm s (centre z) o) := by
  have h1 : IsUnit (closedMap z (constGerm s (centre z) o)) := by
    rw [closedPoint_constGerm f z s hs o]
    exact ho.isUnit
  haveI : IsLocalHom (closedMap z) := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  exact isUnit_of_map_unit (closedMap z) _ h1

theorem map_frac {A L K O : Type} [CommRing A] [CommRing L] [Field K] [CommRing O] (β : O →+* K) (g : O → A)
    (φ : A →+* L) (e : K →+* L) (h : ∀ o, φ (g o) = e (β o)) {a b : O} {k : K} (hk : k * β b = β a)
    (u : Aˣ) (hu : (u : A) = g b) : φ (g a * ↑u⁻¹) = e k := by
  have hw : e (β b) * φ ↑u⁻¹ = 1 := by
    rw [← h b, ← hu, ← map_mul, u.mul_inv, map_one]
  rw [map_mul, h a, ← hk, map_mul, _root_.mul_assoc, hw, _root_.mul_one]

theorem valAt_of_frac {X : Scheme.{0}} {K Ω F O : Type} [Field K] [Field Ω] [Field F] [CommRing O]
    (β : O →+* K) (inc : K →+* Ω) (βF : K →+* F)
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of F) ⟶ X)
    (s : X ⟶ Spec (CommRingCat.of O))
    (hξ : ξ ≫ s = Spec.map (CommRingCat.ofHom (inc.comp β)))
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom (βF.comp β)))
    (hfr : ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (h : genPt ξ ⤳ centre z) (k : K) : ValAt ξ z (inc k) (βF k) := by
  obtain ⟨a, b, hb, hk⟩ := hfr k
  obtain ⟨u, hu⟩ := isUnit_constGerm (βF.comp β) z s hz b ((map_ne_zero βF).2 hb)
  have e₁ : genMap ξ ⟨centre z, h⟩ (constGerm s (centre z) a * ↑u⁻¹) = inc k :=
    map_frac β (constGerm s (centre z)) (genMap ξ ⟨centre z, h⟩) inc
      (fun o => genMap_constGerm (inc.comp β) ξ s hξ ⟨centre z, h⟩ o) hk u hu
  have e₂ : closedMap z (constGerm s (centre z) a * ↑u⁻¹) = βF k :=
    map_frac β (constGerm s (centre z)) (closedMap z) βF
      (fun o => closedPoint_constGerm (βF.comp β) z s hz o) hk u hu
  exact ⟨h, _, e₁, e₂⟩

theorem constants_compose_structure {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {R : Type} [CommRing R] (w : Sp R ⟶ Xo.XF c) (f : c.F →+* R) (hw : w ≫ pullback.snd _ _ = spMap f) :
    (w ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom (f.comp β)) := by
  have h1 : (w ≫ Y.j) ≫ Y.s = (w ≫ pullback.snd _ _) ≫ spMap β := by
    simp only [Model.j, Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  rw [h1, hw, CommRingCat.ofHom_comp, Spec.map_comp]

theorem valAt_inc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap βF → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → ∀ k : c.F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (Z.inc k) (βF k) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F _ βF y hfr hy hsp k
  exact valAt_of_frac β Z.inc βF (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) Y.s (constants_compose_structure Y _ _ Z.over_inc)
    (constants_compose_structure Y _ _ hy) hfr hsp k

end GlobalTheory.CompanionTheory.Ar.Flat.ConstVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsInCoordRatioFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constants_in_coord_ratio_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (cc : (k : K) → J k), (∀ k, y ⟨k, cc k⟩ ≠ 0) → ∀ r : c.F, 𝔐.cst r ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart | exact GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordRelationsHomogeneousStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_relations_homogeneous : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ k : K, ∃ (l : ℕ) (n : Fin l → ℕ) (F : Fin l → J k → MvPolynomial (J k₀) ℤ), (∀ t j, (F t j).IsHomogeneous (n t)) ∧ (∀ t j j', MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j) * y ⟨k, j'⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j') * y ⟨k, j⟩) ∧ ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ t j, MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F t j) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families | exact GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families | (intros; apply GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeReindexedCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_reindexed_coords : ∀ (X : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u) → ∃ φ : ((Σ k, J k) → ℂ) → ℝ, (∀ z ∈ mcPts (mCoordIdeal y), 0 < φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), φ (fun p => starRingEnd ℂ (z p)) = φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ (a - pullDeg bk a₀) k) * φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y), F z' ≠ 0 ∧ φ z' = ‖F z'‖) ∧ IsRatio ξ y y₀ bk bx i a a₀ e e₀ φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.Ratio.exists_isRatio | exact GlobalTheory.CompanionTheory.Ar.Chg.Ratio.exists_isRatio | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.Ratio.exists_isRatio <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingCoordsReindexedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominating_coords_reindexed : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)), GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i → CoordTie ℤ ξ₀ (fun c' : (k : K₀) → J₀ k => ∏ k, y₀ ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ₀ y₀ (z ≫ h) (fun p => w (blkV bk bx p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV | exact GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV <;> assumption)
end

