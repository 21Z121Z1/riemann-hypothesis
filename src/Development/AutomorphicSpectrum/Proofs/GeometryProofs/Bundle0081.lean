import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0073
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0074
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import Development.WeilBound.CoreStatements.RationalSupMetrics.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffRatioRegularStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_coeff_ratio_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (b₁ : Fin p → V) (b₂ : Fin q → V), IsCoeffAt A B p q a b x 1 → A.IsFrameAt b₁ x → B.IsFrameAt b₂ x → ∃ α κ : Ω, a = α • exteriorPower.ιMulti Ω p b₁ ∧ b = κ • exteriorPower.ιMulti Ω q b₂ ∧ α / κ ∈ regAt ξ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModel
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFType

theorem finiteType_of_equiv {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra ℤ C]
    [Algebra.FiniteType ℤ C] (E : B ≃+* C) (g : ℤ →+* A) (f : A →+* B) : f.FiniteType := by
  have hC : (algebraMap ℤ C).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have hE : (E.symm.toRingHom).FiniteType := RingHom.FiniteType.of_surjective _ E.symm.surjective
  have h1 : ((E.symm.toRingHom).comp (algebraMap ℤ C)).FiniteType := hE.comp hC
  have h2 : f.comp (Int.castRingHom A) = (E.symm.toRingHom).comp (algebraMap ℤ C) := RingHom.ext_int _ _
  rw [← h2] at h1
  exact RingHom.FiniteType.of_comp_finiteType h1

theorem main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → ∃ s : X ⟶ Spec (CommRingCat.of ℤ), LocallyOfFiniteType s ∧ QuasiCompact s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := by
  intro X Ω _ ξ κ _ x hall T
  refine ⟨specZIsTerminal.from X, ?_, ?_, specZIsTerminal.hom_ext _ _⟩
  · have hQ := (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).1
    rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) hQ]
    intro q
    obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
    obtain ⟨U, hUa, hU⟩ := T.affine c hcq.1
    have hqU : q ∈ U := (hU q).2 ⟨hall q, hcq⟩
    have hg : genPt ξ ∈ U := (hall q).mem_open U.isOpen hqU
    obtain ⟨E, -⟩ := GlobalTheory.CompanionTheory.Ar.ChartSmooth.exists_secEquiv hall T hcq.1 hU hg
    haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    exact ⟨⟨⊤, isAffineOpen_top _⟩, ⟨U, hUa⟩, hqU, by simp, finiteType_of_equiv E (Int.castRingHom _) _⟩
  · rw [quasiCompact_iff_compactSpace]
    choose U hUa hU using T.affine
    refine ⟨?_⟩
    have hcov : (Set.univ : Set X) = ⋃ (c : κ) (hc : x c ≠ 0), (U c hc : Set X) := by
      ext q
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
      exact ⟨c, hcq.1, (hU c hcq.1 q).2 ⟨hall q, hcq⟩⟩
    rw [hcov]
    exact isCompact_iUnion fun c => isCompact_iUnion fun hc => (hUa c hc).isCompact

end GlobalTheory.CompanionTheory.Ar.ChartFType
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelCommonRefinementStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_common_refinement : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement | exact GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagPairChartBundleCompatStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_chart_bundle_compat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ϖ : O) (r : ℕ) (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (w w' : Module.Basis (Fin r) Ω (Fin r → Ω))
    (x x' : Fin r → K → ℤ) (f g : Fin r → MvPolynomial (Σ k, J k) O), IsFlagPair ϖ y B B' w w' x x' f g →
    ∃ (C C' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
      (∀ c, segreVec y c ≠ 0 → C.lat c = dotDual (chartRing O (segreVec y) c) (B.lat c) ∧
        C'.lat c = dotDual (chartRing O (segreVec y) c) (B'.lat c)) ∧
      IsFlagPair ϖ y C C' v v' (fun i => -x (Fin.rev i)) (fun i => -x' (Fin.rev i)) (fun i => g (Fin.rev i))
        (fun i => f (Fin.rev i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLocalExtensionExistsStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_local_extension_exists : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists | exact GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists | (intros; apply GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

open GlobalTheory.CompanionTheory.Ar.BT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F]

abbrev NAdd (E : Type) [Field E] [NumberField E] (n p : ℕ) : Type := Fin n → (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})

def toNAdd {n p : ℕ} (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) : (Fin n → F) →+ NAdd E n p where
  toFun a i := sc (a i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def fromNAdd {n p : ℕ} (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) : NAdd E n p →+ (Fin n → F) where
  toFun t i := pq (t i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def bcLin (C : Type) [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω)) :
    (Fin m → C) →ₗ[C] (Fin n → C) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (algebraMap Ω C))

variable {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}

def testOrd (P : ChartPack G O c') {C : Type} [Field C] [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) :
    Submodule RC (NAdd E (D.p + D.q) p → C) :=
  Submodule.span RC {f | ∃ g ∈ P.Γ₁.btOrder ⊤, f = fun x =>
    algebraMap Ω C ((g (Multiplicative.ofAdd x) : CR O y c') : Ω)}

def testOrdW (P : ChartPack G O c') (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) {C : Type} [Field C] [Algebra O C]
    [Algebra Ω C] (RC : Subalgebra O C) : Submodule RC ((Fin (D.p + D.q) → F) → C) :=
  (testOrd P RC).map (LinearMap.funLeft RC C (toNAdd sc : (Fin (D.p + D.q) → F) → NAdd E (D.p + D.q) p))

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructurePropertiesStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_level_structure_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props | exact GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFormValuationEmbedding
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem exists_form_embedding_hasVal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω], Birational y → IsRelevant (mCoordIdeal y) → ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → aeval z h ≠ 0 → ∃ φ : F →+* 𝕜, ∀ θ : F, HasVal y 0 (algebraMap F Ω θ) z (φ θ) :=
  @MultiProjectiveCoordinates.exists_field_hom_on_open

end GlobalTheory.CompanionTheory.Ar.Small
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_generic_fibre : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P), IsCptGen ξ₀ → ∃ (b : F →+* Ω) (ξF : Sp Ω ⟶ pullback s (spMap (algebraMap (𝓞 F) F))), ξF ≫ pullback.fst _ _ = ξ₀ ∧ ξF ≫ pullback.snd _ _ = spMap b ∧ IsCptGen ξF := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point | exact GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point | (intros; apply GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointLiftAlongIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_lift_along_iso : ∀ (W X' : Scheme.{0}) (f : X' ⟶ W) (U : W.Opens) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W), IsIso (f ∣_ U) → genPt ξ ∈ U → IsCptGen ξ → (∀ x : X', IsDomain (X'.presheaf.stalk x)) → ∃ ξ' : Sp Ω ⟶ X', ξ' ≫ f = ξ ∧ IsCptGen ξ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointMemDenseOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_mem_dense_open : ∀ (W : Scheme.{0}) [IsLocallyNoetherian W] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W) (U : W.Opens), IsCptGen ξ → Dense (U : Set W) → genPt ξ ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.genPt_mem_of_dense_open | exact GlobalTheory.CompanionTheory.Ar.SncBase.genPt_mem_of_dense_open | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.genPt_mem_of_dense_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianNormSectionValue
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.EvalPt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem aeval_div_mul_prod {F : Type} [Field F] (v : (Σ k, J k) → F) (t : K → F) (ht : ∀ k, t k ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval (fun p => v p / t p.1) g * ∏ k, t k ^ d k = aeval v g := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  have key : ∏ k, t k ^ d k = ∏ p : (Σ k, J k), t p.1 ^ m p := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [key, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (ht p.1))]

theorem map_aeval_int {σ S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (s : σ → S) (f : MvPolynomial σ ℤ) :
    φ (aeval s f) = aeval (fun i => φ (s i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem norm_evC_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ} {A : HermLine J} {c₀ : Ω} {C : ℝ}
    {g h : MRing J} {dg dh : K → ℕ} (hz : genPt ξ ⤳ centre z) (hco : CoordsAt ξ y z w)
    (hyp : ∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) →
      ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w)
    (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) (hd : ∀ k, (dg k : ℤ) - dh k = A.a k)
    (he : aeval y g = c₀ * aeval y h) (hw : evC w h ≠ 0) :
    ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  classical
  obtain ⟨hcov, hco2⟩ := hco
  choose cc hcc using hcov
  have hw0 : ∀ k, w ⟨k, cc k⟩ ≠ 0 := fun k => (hcc k).ne_zero
  have hy0 : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hco2 k (cc k) (hcc k)).1
  have hr : ∀ p : (Σ k, J k), ∃ s : X.presheaf.stalk (centre z),
      genMap ξ ⟨centre z, hz⟩ s = y p / y ⟨p.1, cc p.1⟩ ∧
      w p = (Scheme.stalkClosedPointTo z).hom s * w ⟨p.1, cc p.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r, ⟨h', s, hs1, hs2⟩, hwr⟩ := (hco2 k (cc k) (hcc k)).2 i
    exact ⟨s, hs1, by rw [hwr, ← hs2]⟩
  choose s hs1 hs2 using hr
  have hφ1 : ∀ f : MRing J, genMap ξ ⟨centre z, hz⟩ (aeval s f) =
      aeval (fun p => y p / y ⟨p.1, cc p.1⟩) f := by
    intro f
    rw [map_aeval_int]
    simp only [hs1]
  have hwr : ∀ p : (Σ k, J k), w p / w ⟨p.1, cc p.1⟩ = (Scheme.stalkClosedPointTo z).hom (s p) := fun p => by
    rw [hs2 p, mul_div_cancel_right₀ _ (hw0 p.1)]
  have hφ2 : ∀ f : MRing J, (Scheme.stalkClosedPointTo z).hom (aeval s f) =
      aeval (fun p => w p / w ⟨p.1, cc p.1⟩) f := by
    intro f
    refine (map_aeval_int (Scheme.stalkClosedPointTo z).hom s f).trans ?_
    simp only [← hwr]
    try rfl
  have hev : ∀ f : MRing J, evC w f = aeval w f := fun f => by
    simp only [evC, MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]
  have hg1 : aeval (fun p => w p / w ⟨p.1, cc p.1⟩) g * ∏ k, w ⟨k, cc k⟩ ^ dg k = aeval w g :=
    aeval_div_mul_prod w (fun k => w ⟨k, cc k⟩) hw0 hg
  have hh1 : aeval (fun p => w p / w ⟨p.1, cc p.1⟩) h * ∏ k, w ⟨k, cc k⟩ ^ dh k = aeval w h :=
    aeval_div_mul_prod w (fun k => w ⟨k, cc k⟩) hw0 hh
  have hg2 : aeval (fun p => y p / y ⟨p.1, cc p.1⟩) g * ∏ k, y ⟨k, cc k⟩ ^ dg k = aeval y g :=
    aeval_div_mul_prod y (fun k => y ⟨k, cc k⟩) hy0 hg
  have hh2 : aeval (fun p => y p / y ⟨p.1, cc p.1⟩) h * ∏ k, y ⟨k, cc k⟩ ^ dh k = aeval y h :=
    aeval_div_mul_prod y (fun k => y ⟨k, cc k⟩) hy0 hh
  rw [hev, hev] at *
  set Pg := aeval (fun p => w p / w ⟨p.1, cc p.1⟩) g with hPg
  set Ph := aeval (fun p => w p / w ⟨p.1, cc p.1⟩) h with hPh
  set Qg := aeval (fun p => y p / y ⟨p.1, cc p.1⟩) g with hQg
  set Qh := aeval (fun p => y p / y ⟨p.1, cc p.1⟩) h with hQh
  have hTg : ∏ k, w ⟨k, cc k⟩ ^ dg k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hw0 k)
  have hTh : ∏ k, w ⟨k, cc k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hw0 k)
  have hYg : ∏ k, y ⟨k, cc k⟩ ^ dg k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy0 k)
  have hYh : ∏ k, y ⟨k, cc k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy0 k)
  have hPh0 : Ph ≠ 0 := by
    intro h0
    apply hw
    rw [← hh1, h0, zero_mul]
  have hunit : IsUnit (aeval s h : X.presheaf.stalk (centre z)) :=
    isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (by rw [hφ2]; exact hPh0.isUnit)
  have hQh0 : Qh ≠ 0 := by
    have := (hunit.map (genMap ξ ⟨centre z, hz⟩)).ne_zero
    rwa [hφ1] at this
  have hyh0 : aeval y h ≠ 0 := by
    rw [← hh2]
    exact mul_ne_zero hQh0 hYh
  have hval : ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) (Pg / Ph) := by
    refine ⟨hz, aeval s g * ↑hunit.unit⁻¹, ?_, ?_⟩
    · rw [map_mul, map_units_inv, IsUnit.unit_spec, hφ1, hφ1]
      have hpow : ∏ k, y ⟨k, cc k⟩ ^ A.a k = (∏ k, y ⟨k, cc k⟩ ^ dg k) / ∏ k, y ⟨k, cc k⟩ ^ dh k := by
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← hd k, zpow_sub₀ (hy0 k), zpow_natCast, zpow_natCast]
      have hc0 : c₀ = (Qg * ∏ k, y ⟨k, cc k⟩ ^ dg k) / (Qh * ∏ k, y ⟨k, cc k⟩ ^ dh k) := by
        rw [hg2, hh2, he, mul_div_assoc, div_self hyh0, mul_one]
      rw [hpow, hc0, ← hQg, ← hQh]
      field_simp
      try ring
    · have hq : (aeval s g * ↑hunit.unit⁻¹ : X.presheaf.stalk (centre z)) * aeval s h = aeval s g := by
        rw [mul_assoc, Units.inv_mul_of_eq hunit.unit_spec, mul_one]
      have key2 := (RingHom.map_mul (Scheme.stalkClosedPointTo z).hom _ _).symm.trans
        (congrArg (Scheme.stalkClosedPointTo z).hom hq)
      rw [hφ2, hφ2] at key2
      exact (eq_div_iff hPh0).2 key2
  have key := hyp cc (Pg / Ph) hw0 hval
  have hnpow : ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k =
      (∏ k, ‖w ⟨k, cc k⟩‖ ^ dg k) / ∏ k, ‖w ⟨k, cc k⟩‖ ^ dh k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hd k, zpow_sub₀ (norm_ne_zero_iff.2 (hw0 k)), zpow_natCast, zpow_natCast]
  have hnh : ∏ k, ‖w ⟨k, cc k⟩‖ ^ dh k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hw0 k))
  have hPhn : ‖Ph‖ ≠ 0 := norm_ne_zero_iff.2 hPh0
  rw [← key, ← hg1, ← hh1, hnpow, norm_mul, norm_mul, norm_div, norm_prod, norm_prod]
  simp only [norm_pow]
  field_simp
  try ring

theorem norm_evC_of_forms : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [Nonempty K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (A : HermLine J) (c₀ : Ω) (C : ℝ) (g h : MRing J) (dg dh : K → ℕ), IsCptGen ξ → CoordsAt ξ y z w → (∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w) → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → evC w h ≠ 0 → ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  intro X Ω _ ξ K _ _ J _ y z w A c₀ C g h dg dh _ hco hyp hg hh hd he hw
  obtain ⟨k⟩ := ‹Nonempty K›
  obtain ⟨c, hc⟩ := hco.1 k
  obtain ⟨r, ⟨hz, _⟩, _⟩ := (hco.2 k c hc).2 c
  exact norm_evC_of_specializes hz hco hyp hg hh hd he hw

end GlobalTheory.CompanionTheory.Ar.Flat.EvalPt
end
end

