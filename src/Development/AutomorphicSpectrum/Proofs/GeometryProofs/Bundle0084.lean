import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0018
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0017
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZarhinBundleKernelFirstCoordEquations
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicPointOverNumberField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend

theorem exists_numberField_point (C : Type) [Field C] [CharZero C] [Algebra.IsAlgebraic ℚ C]
    (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : Sp C ⟶ X) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (e : K →+* C) (x' : Sp K ⟶ X),
      spMap e ≫ x' = x :=
  _root_.UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.main C X π x

end GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeCount
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem mem_coordLat_iff_forall_om_mem_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ (s : CMType H ⊕ CMType H), (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = 𝔐.emb s a) → (∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * 𝔐.emb s x = 1) → (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → ∀ a : Fin (labelRk D s) → Ω, a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ CR O y c' :=
  PositivityTheory.Xgn.sequence_coordinates_exist

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeDegree
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff

theorem embedding_integers_and_different_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧ ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 :=
  @PositivityTheory.Xgn.sequence_differentials_exist

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeRelay
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) ∧ ∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω) := by
  first | exact @PositivityTheory.Xgn.sequence_ring_exists | exact PositivityTheory.Xgn.sequence_ring_exists
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryGeneratorUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_generator_unit : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (B : Set (Cpt ξ)) (p : Cpt ξ) (a : Ω), (∀ q ∈ B, Char0 ξ q) → Char0 ξ p → InChart ξ x c p → a ∈ Mdl.chartQ x c → unitAt ξ p a → (∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a) → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep.exists_bdGens_unitAt | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep.exists_bdGens_unitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep.exists_bdGens_unitAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_points_coords : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (B : Set (Cpt ξ)), IsCptGen ξ → (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → p ∉ B → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G)) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w → (w ∈ mcPts (Ideal.span (Mdl.bdGens ξ x B)) ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.mem_mcPts_span_bdGens_iff | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.mem_mcPts_span_bdGens_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.mem_mcPts_span_bdGens_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPointInChartDominated
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chartPoint_inChart_dominated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (z : Spec (CommRingCat.of (CR O y c'))), InChart 𝔐.ξ (mseg y) c' ⟨P.x z, 𝔐.all _⟩ ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) ∧ ∀ a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩, ∃ r s : CR O y c', s ∉ z.asIdeal ∧ (s : Ω) * a = r :=
  @PositivityTheory.Xgn.exists_function_at_point

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeGivesComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_prime_gives_component : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmEmbeddingConjugateCompatStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_embedding_conjugate_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab.exists_labelEmbedding | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab.exists_labelEmbedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab.exists_labelEmbedding <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishingStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_dense_nonvanishing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | exact GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGivesChartPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_gives_chart_prime : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → ∀ p : Cpt ξ, Char0 ξ p → InChart ξ x c p → ∃ I : Ideal (Mdl.chartQ x c), I.IsPrime ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_prime_chartQ | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_prime_chartQ | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_prime_chartQ <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocks
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AddBlockMulti

open GlobalTheory.CompanionTheory.Ar.ProjCoord

section Reindex

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem inChart_comp_equiv (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ κ' : Type} (e : κ' ≃ κ) (x : κ → Ω) (c : κ')
    (p : Cpt ξ) : InChart ξ (x ∘ e) c p ↔ InChart ξ x (e c) p := by
  unfold InChart
  refine and_congr Iff.rfl ⟨fun h c' => ?_, fun h c' => h _⟩
  simpa using h (e.symm c')

theorem coordTie_comp_equiv {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type}
    (e : κ' ≃ κ) {x : κ → Ω} (h : CoordTie o ξ x) : CoordTie o ξ (x ∘ e) := by
  have hr : ∀ c : κ', (Set.range fun j => (x ∘ e) j / (x ∘ e) c) = Set.range fun j => x j / x (e c) := fun c =>
    e.surjective.range_comp (fun j => x j / x (e c))
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (inChart_comp_equiv ξ e x _ p).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    refine ⟨U, hU, fun q => ?_⟩
    rw [hq q]
    exact exists_congr fun hh => (inChart_comp_equiv ξ e x c ⟨q, hh⟩).symm
  · rw [hr c, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (inChart_comp_equiv ξ e x c p).symm Iff.rfl

end Reindex

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
variable (ζ : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]

theorem specializes_of_openImm {y : Y} (h : genPt (ζ ≫ f) ⤳ f y) : genPt ζ ⤳ y := by
  have e2 : genPt (ζ ≫ f) = f (genPt ζ) := Scheme.Hom.comp_apply _ _ _
  rw [e2] at h
  exact f.isOpenEmbedding.isInducing.specializes_iff.1 h

theorem inChart_push {κ : Type} (x : κ → Ω) (c : κ) (p : Cpt ζ) :
    InChart (ζ ≫ f) x c (push ζ f p) ↔ InChart ζ x c p := by
  unfold InChart
  rw [regAt_push]

variable {ζ f}

theorem exists_push (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (q : Cpt (ζ ≫ f)) :
    ∃ p : Cpt ζ, push ζ f p = q := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ := hR q hq
  exact ⟨⟨y, specializes_of_openImm ζ f hq⟩, rfl⟩

theorem coordTie_push {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (h : CoordTie o ζ x) : CoordTie o (ζ ≫ f) x := by
  refine ⟨⟨?_, fun q => ?_⟩, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · rw [Scheme.stalkClosedPointTo_comp ζ f]
    have hb : Function.Bijective (f.stalkMap (ζ (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact h.gen.bij.comp hb
  · obtain ⟨p, rfl⟩ := exists_push hR q
    exact genMap_push_injective ζ f p (h.gen.inj p)
  · obtain ⟨p, rfl⟩ := exists_push hR q
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨c, (inChart_push ζ f x c p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    refine ⟨f ''ᵁ U, hU.image_of_isOpenImmersion f, fun q => ⟨?_, ?_⟩⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, h2⟩ := (hq y).1 hy
      exact ⟨(push ζ f ⟨y, h1⟩).2, (inChart_push ζ f x c ⟨y, h1⟩).2 h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := hR q h1
      have h1' := specializes_of_openImm ζ f h1
      exact ⟨y, (hq y).2 ⟨h1', (inChart_push ζ f x c ⟨y, h1'⟩).1 h2⟩, rfl⟩
  · rw [h.ring c hc a]
    constructor
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push hR q
      rw [regAt_push]
      exact H p ((inChart_push ζ f x c p).1 hq)
    · intro H p hp
      have := H (push ζ f p) ((inChart_push ζ f x c p).2 hp)
      rwa [regAt_push] at this

theorem coordTie_of_push {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (h : CoordTie o (ζ ≫ f) x) : CoordTie o ζ x := by
  refine ⟨⟨?_, fun p => ?_⟩, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · have hb : Function.Bijective (f.stalkMap (ζ (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    have h1 := h.gen.bij
    rw [Scheme.stalkClosedPointTo_comp ζ f] at h1
    exact (Function.Bijective.of_comp_iff _ hb).1 h1
  · have h1 := h.gen.inj (push ζ f p)
    rw [genMap_push] at h1
    have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
    exact (Function.Injective.of_comp_iff' _ hb).1 h1
  · obtain ⟨c, hc⟩ := h.cover (push ζ f p)
    exact ⟨c, (inChart_push ζ f x c p).1 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    have hle : U ≤ f.opensRange := fun q hqU => hR q ((hq q).1 hqU).1
    refine ⟨f ⁻¹ᵁ U, ?_, fun y => ⟨fun hy => ?_, ?_⟩⟩
    · have e : f ''ᵁ (f ⁻¹ᵁ U) = U := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
        exact inf_eq_right.2 hle
      rw [← f.isAffineOpen_iff_of_isOpenImmersion, e]
      exact hU
    · obtain ⟨h1, h2⟩ := (hq (f y)).1 hy
      have h1' := specializes_of_openImm ζ f h1
      exact ⟨h1', (inChart_push ζ f x c ⟨y, h1'⟩).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact (hq (f y)).2 ⟨(push ζ f ⟨y, h1⟩).2, (inChart_push ζ f x c ⟨y, h1⟩).2 h2⟩
  · rw [h.ring c hc a]
    constructor
    · intro H p hp
      have := H (push ζ f p) ((inChart_push ζ f x c p).2 hp)
      rwa [regAt_push] at this
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push hR q
      rw [regAt_push]
      exact H p ((inChart_push ζ f x c p).1 hq)

end OpenImm

section Model

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem spec_int_hom_ext (g g' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℤ)) : g = g' := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage g']
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_int _ _)

theorem exists_openModel {κ : Type} {x : κ → Ω} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : CoordTie ℤ ξ x) :
    ∃ (Y : Scheme.{0}) (ζ : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (_ : IsOpenImmersion f), ζ ≫ f = ξ ∧
      (∀ q : X, genPt ξ ⤳ q → q ∈ Set.range f) ∧ ∀ q : Y, genPt ζ ⤳ q := by
  let W : X.Opens := sSup {U : X.Opens | ∀ q ∈ U, genPt ξ ⤳ q}
  have hW : ∀ q ∈ W, genPt ξ ⤳ q := by
    intro q hq
    obtain ⟨U, hU, hqU⟩ := TopologicalSpace.Opens.mem_sSup.1 hq
    exact hU q hqU
  have hC : ∀ q : X, genPt ξ ⤳ q → q ∈ W := by
    intro q hq
    obtain ⟨c, hc⟩ := h.cover ⟨q, hq⟩
    obtain ⟨U, -, hU⟩ := h.affine c hc.1
    refine TopologicalSpace.Opens.mem_sSup.2 ⟨U, fun r hr => ((hU r).1 hr).1, (hU q).2 ⟨hq, hc⟩⟩
  have hr : Set.range ξ ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst hz
    rw [Scheme.Opens.range_ι]
    exact hC _ specializes_rfl
  have e : IsOpenImmersion.lift W.ι ξ hr ≫ W.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  have hR : ∀ q : X, genPt ξ ⤳ q → q ∈ Set.range W.ι := fun q hq => by
    rw [Scheme.Opens.range_ι]
    exact hC q hq
  refine ⟨W, IsOpenImmersion.lift W.ι ξ hr, W.ι, inferInstance, e, hR, fun q => ?_⟩
  refine specializes_of_openImm _ W.ι ?_
  rw [e]
  exact hW _ q.2

theorem coordTie_join {κ κ' : Type} [Finite κ] [Finite κ'] {x : κ → Ω} {w : κ' → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : CoordTie ℤ ξ x) (hw : ∀ p : Cpt ξ, ∃ l, InChart ξ w l p) :
    CoordTie ℤ ξ (joinCo (RingHom.id Ω) x w) := by
  obtain ⟨Y, ζ, f, _, rfl, hR, hall⟩ := exists_openModel h
  let M : PModel ℤ x :=
    { X := Y
      ξ := ζ
      s := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom _))
      hover := spec_int_hom_ext _ _
      all := hall
      tie := coordTie_of_push hR h }
  refine coordTie_push hR (GlobalTheory.T.join_coords_coordTie ℤ Ω κ x M κ' w fun p => ?_)
  obtain ⟨l, hl⟩ := hw (push ζ f p)
  exact ⟨l, (inChart_push ζ f w l p).1 hl⟩

end Model

theorem add_block_multi : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type)
    [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (K' : Type) [Fintype K']
    (J' : K' → Type) [∀ k, Fintype (J' k)] (s : (Σ k, J' k) → Ω),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    (∀ (k : K') (p : Cpt ξ), ∃ i, InChart ξ (fun i' : J' k => s ⟨k, i'⟩) i p) →
    CoordTie ℤ ξ fun c' : (k : K ⊕ K') → Sum.elim J J' k =>
      (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ := by
  intro X Ω _ ξ K _ J _ y K' _ J' _ s h hs
  have hw : ∀ p : Cpt ξ, ∃ i, InChart ξ (fun c : (k : K') → J' k => ∏ k, s ⟨k, c k⟩) i p := by
    intro p
    choose i hi using fun k => hs k p
    refine ⟨i, Finset.prod_ne_zero_iff.2 fun k _ => (hi k).1, fun c' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => (hi k).2 (c' k)
  have h2 := coordTie_join (κ := (k : K) → J k) (κ' := (k : K') → J' k) h hw
  exact coordTie_comp_equiv (Equiv.sumPiEquivProdPi (Sum.elim J J')) h2

end GlobalTheory.CompanionTheory.Ar.AddBlockMulti
end
end

