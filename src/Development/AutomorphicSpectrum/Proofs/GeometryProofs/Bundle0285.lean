import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0282
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0280
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0151
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
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
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArch
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0283
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSectionStatement
section
open GlobalTheory.CompanionTheory.Ar AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_atlas_snc_section : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) → ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | exact GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | (intros; apply GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeTorsion
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts

theorem chartRing_over_place_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ ∃ x : Spec (CommRingCat.of (CR O y c')) ⟶ 𝔐.X, spMap (algebraMap (CR O y c') Ω) ≫ x = 𝔐.ξ :=
  @PositivityTheory.Xgn.torsion_packing_facts

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowLemmaQuasiProjectiveStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chow_lemma_quasi_projective : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (X' : Scheme.{0}) (π : X' ⟶ X), IsProper π ∧ Surjective π ∧ IsQProjOver (π ≫ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentNormConstantModels
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.component_norm_constant_models : (Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (σ : c.F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal RM.y), (∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) → MvPolynomial.aeval z u ≠ 0 → ∃ k, Over (U (goodOf c σ)) (e Z) k ∧ ∃ y ∈ ((U (goodOf c σ)).X k).dom, ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∃ θ : ℂ, ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw x a * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y ∧ ∀ f ∈ secZ Xo c a, (GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * rdU (U (goodOf c σ)) f k y)) ∧ (¬ GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * starRingEnd ℂ (rdU (U (goodOf c σ)) f k y)))) := by
  first | exact @PositivityTheory.UnitarySelfGeneration.y_read_arch | exact PositivityTheory.UnitarySelfGeneration.y_read_arch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspLatticeMulComponentSectionStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_lattice_mul_component_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (a : WZ E) (Z : Comp Xo c) (w : Rul Xo c), w ∈ (Ref.pjSys Xo c).lat (cuspZ Xo c U a) → e Z * w ∈ latOn U h a Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.indicator_mul_mem_latOn | exact GlobalTheory.CompanionTheory.Ar.Rec.indicator_mul_mem_latOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.indicator_mul_mem_latOn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticeBaseChange
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem dual_baseChange_fractionField : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) :=
  @PositivityTheory.Xgn.exists_dual_base_change

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_quasi_finite_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp R ⟶ X) (n : ℕ), IsSemiAbelian G → 0 < n → FullTorsion G (spMap (algebraMap R (FractionRing R)) ≫ x) n → ∃ (T : Type) (_ : CommGroup T) (_ : Finite T) (Q : BT.QFGroup R T) (i : Q.G.left ⟶ G.left), Q.IsTorsionAlong G x n i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorsQF.torsion_qfGroup | exact GlobalTheory.CompanionTheory.Ar.TorsQF.torsion_qfGroup | (intros; apply GlobalTheory.CompanionTheory.Ar.TorsQF.torsion_qfGroup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_constant_holds : GlobalTheory.CompanionTheory.Ar.Flat.FinConst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | exact GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagAtlasProjectiveEmbeddingStatement
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_atlas_projective_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, Z ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ Z)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∃ d : ℕ, SmoothOfRelativeDimension d (π ≫ Y.s) ∧ IsProjOver (π ≫ Y.s) := by
  first | exact @GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj | exact GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj | (intros; apply GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionInjectiveSubalgebra
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem torsionAlong_of_fullTorsion : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsNoetherianRing R] [CharZero R] [IsFractionRing R Ω] (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∀ (T : Type) [CommGroup T] (pt : T →* (Over.mk ξ ⟶ G)) (N n : ℕ), 1 ≤ N → N ∣ n → FullTorsion G ξ n → Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (pt t).left = spMap (fracToField R) ≫ (Γ.pt t).left ≫ i :=
  @PositivityTheory.Xgn.full_torsion_packing

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_weil_unique : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (y : Over.mk ξ ⟶ G) (q : Cpt ξ) (w w' : Module.Dual Ω E), y ^ n = 1 → M.IsHTAt L n y q w → (M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HtUniq.isHTAt_iff | exact GlobalTheory.CompanionTheory.Ar.HtUniq.isHTAt_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.HtUniq.isHTAt_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsHTAtIff
section
noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie

theorem isHTAt_iff (h455 : type_of% @GlobalTheory.T.lie_model_finite_base_change) (h876 : type_of% @GlobalTheory.T.section_eq_zero_of_values)
    {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (L : LB G.left) {n : ℕ} (hn : n ≠ 0)
    (hfull : FullTorsion G ξ n) {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E)
    {R : Type} [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω)
    (hx : Spec.map (CommRingCat.ofHom (κ.toRingHom.comp (algebraMap R (FractionRing R)))) ≫ x = ξ)
    {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (htor : Γ.IsTorsionAlong G x n i)
    {L₀ : Type} [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀) (j : L₀ → E)
    (hj : ∀ v, (M.pt (j v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (κ.toRingHom.comp (algebraMap R (FractionRing R))))) ≫ (M₀.pt v).left)
    (y : Over.mk ξ ⟶ G) (χ : T →* Rˣ) (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E)
    (hW : ∀ (t : T) (k : Type) [Field k] [IsAlgClosed k] (a : Ω →+* k) (xk gk : Over.mk (spMap a ≫ ξ) ⟶ G) (c : kˣ),
      xk.left = spMap a ≫ y.left → gk.left = spMap a ≫ ptG κ.toRingHom i t →
        (Out.WeilIs G L n xk gk (unitOn c) ↔ (c : k) = a (κ (algebraMap R _ (χ t : R)))))
    (hHT : Γ.IsHT i M₀ n χ w₀) (hwj : ∀ v, w (j v) = κ (algebraMap R _ (w₀ v)))
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a : R, κ (algebraMap R _ a) ∈ regAt ξ q)
    (w' : Module.Dual Ω E) : M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum R, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ (κ.toRingHom.comp (algebraMap R (FractionRing R)))
    (κ.injective.comp (IsFractionRing.injective R _)) x hx p q hp hsub
  obtain ⟨s, hs, hv⟩ := hHT
  have hcore := fun W f hval (e' : E) (v : epsAt (X.fromSpecStalk q.1) ⟶ G) (hv' : M.Extends q e' v) =>
    core_tan h455 M p.asIdeal.primeCompl Γ i x hzs (genMap ξ q) _ hg M₀ j hj n w₀ w hwj s hv W f hval e' v hv'.1 hv'.2
  obtain ⟨W₀, f₀, hW₀, hf₀⟩ := lift_sec G Γ x n i htor q.1 _ hzs s
  have hval₀ : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (b : X.presheaf.stalk q.1 →+* B),
      y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R (X.presheaf.stalk q.1)))) →
        ∀ h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W₀, valAt (y ≫ i) W₀ h f₀ = valAt y ⊤ le_top s :=
    fun y b hb h => hf₀ y (Spec.map (CommRingCat.ofHom b)) (hb.trans (spec_comp _ _)) h
  have hlat := (lieLat_carrier X G Ω ξ E M q).1
  have hw : w ∈ M.omLat q := fun e' he' => by
    obtain ⟨v, hv'⟩ := (hlat e').1 he'
    obtain ⟨c, hc, -⟩ := hcore W₀ f₀ hval₀ e' v hv'
    exact ⟨c, hc.symm⟩
  have hn' : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
  constructor
  · rintro ⟨-, W, f, hWm, hf, hd⟩
    have hsec : (i.app W).hom f - Γ.G.left.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op s = 0 := by
      refine h876 R T Γ (i ⁻¹ᵁ W) _ fun t h => ?_
      rw [valAt_sub, sub_eq_zero]
      refine Eq.trans ?_ (valAt_res _ _ ⊤ le_top h le_top s).symm
      rw [hs t]
      refine (valAt_comp (Γ.pt t).left i W h f).symm.trans ?_
      let k := AlgebraicClosure Ω
      let a : Ω →+* k := algebraMap Ω k
      let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a) rfl
      obtain ⟨g, hg1, hg2⟩ := tors_ex κ.toRingHom htor hx t
      let c : kˣ := Units.map ((a.comp κ.toRingHom).comp (algebraMap R (FractionRing R))).toMonoidHom (χ t)
      have e0 : (ψ ≫ g).left = spMap a ≫ ptG κ.toRingHom i t := by rw [← hg2]; rfl
      have e1 : (ψ ≫ g).left = Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left ≫ i := by
        rw [e0, spec_comp, Category.assoc]
      have h1 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left ≫ i) ⁻¹ᵁ W :=
        fun z _ => h (by trivial)
      have h2 := hf k a (ψ ≫ y) (ψ ≫ g) c (by rw [e1]; exact h1) rfl (by rw [← comp_pow', hg1, MonObj.comp_one])
        ((hW t k a (ψ ≫ y) (ψ ≫ g) c rfl e0).2 rfl)
      apply (a.comp κ.toRingHom).injective
      exact (valAt_spec (a.comp κ.toRingHom) _ W h h1 f).symm.trans ((valAt_congr e1 W _ h1 f).symm.trans h2)
    have hval : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (b : X.presheaf.stalk q.1 →+* B),
        y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R (X.presheaf.stalk q.1)))) →
          ∀ h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W, valAt (y ≫ i) W h f = valAt y ⊤ le_top s := by
      intro B _ y _ _ h
      refine (valAt_comp y i W h f).trans ?_
      rw [sub_eq_zero.1 hsec]
      exact valAt_res y (i ⁻¹ᵁ W) ⊤ le_top h le_top s
    refine ⟨(n : Ω)⁻¹ • (w' - w), fun e' he' => ?_, ?_⟩
    · obtain ⟨v, hv'⟩ := (hlat e').1 he'
      have hm : ⊤ ≤ v.left ⁻¹ᵁ W := HtUniq.tan_le v hv'.1 hWm
      obtain ⟨c, hc, hr⟩ := hcore W f hval e' v hv'
      obtain ⟨r, hr⟩ := hr hm
      obtain ⟨r', hr', he⟩ := hd e' v hv' hm
      have : ((n : Ω)⁻¹ • (w' - w)) e' = r' - genMap ξ q r := by
        have he' : w' e' = genMap ξ q (BT.valAt v.left W hm f).snd + n * r' := he
        have hc' : w e' = genMap ξ q (BT.valAt v.left W hm f).snd + n * genMap ξ q r := by
          rw [hc, hr, map_add, map_mul, map_natCast]
          rfl
        rw [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hn', mul_sub, he', hc',
          add_sub_add_left_eq_sub]
      rw [this]
      exact sub_mem hr' ⟨r, rfl⟩
    · rw [← Nat.cast_smul_eq_nsmul Ω, smul_smul, mul_inv_cancel₀ hn', one_smul, add_sub_cancel]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨add_mem hw (nsmul_mem hu n), W₀, f₀, hW₀, ?_, ?_⟩
    · intro K _ _ a xk g' c h hxk hg' hweil
      obtain ⟨g₀, hg₀⟩ := hfull K a g' hg'
      have hg0 : g₀ ^ n = 1 := pow_descend a hg₀ hg'
      obtain ⟨t, ht⟩ := tors_pt κ.toRingHom htor hx g₀ hg0
      have hc₁ := (hW t K a xk g' c hxk (by rw [hg₀, ht])).1 hweil
      have e1 : g'.left = (Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left) ≫ i := by
        rw [hg₀, ht, spec_comp]; simp only [ptG, Category.assoc]
      refine (valAt_congr e1 W₀ h (by rw [← e1]; exact h) f₀).trans ?_
      rw [hval₀ _ (a.comp (genMap ξ q)) (by
        rw [Category.assoc, Over.w, RingHom.comp_assoc, hg, ← RingHom.comp_assoc, spec_comp (algebraMap R _)]; rfl)]
      refine (valAt_spec (a.comp κ.toRingHom) (Γ.pt t).left ⊤ le_top le_top s).trans ?_
      rw [hs t, hc₁]
      rfl
    · intro e' v hv' h
      obtain ⟨c, hc', hr⟩ := hcore W₀ f₀ hval₀ e' v hv'
      obtain ⟨r, hr⟩ := hr h
      refine ⟨genMap ξ q r + u e', add_mem ⟨r, rfl⟩ (hu e' ((hlat e').2 ⟨v, hv'⟩)), ?_⟩
      rw [LinearMap.add_apply, LinearMap.smul_apply, hc', hr, map_add, map_mul, map_natCast, nsmul_eq_mul, mul_add,
        ← add_assoc]
      rfl

end GlobalTheory.CompanionTheory.HtLink
end
end

