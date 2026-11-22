import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeRelation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0200
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.WeilBound.CoreStatements.VolumeEquality.SheetPiecesComponent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsOrthogonalLieMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0202
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0193

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeRelationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_gauge_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ lam : PS k 2 d, (∀ m, ∃ U : (Jet k (Fin 2 × Fin d) m)ˣ, (U : Jet k (Fin 2 × Fin d) m) = psJet m lam ∧ Tr w (cubeF t x ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (fun I => (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)] I) (cε 2) (g.e m) (LB.pullGen Q.tB.PP.L (cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)]) (cε 2) (gB.e m) (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) (unitΓ U⁻¹)) → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → AdRel Q.tB (𝟙 (Sp k)) d' gB.x gB.B.A.act gB.B.ad gB.e a wB → Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) 1 → subQ Qs (gB.B.ad a) * ev (n := 2) ![pt k d 0, comp1 (g.B.A.act (H.bar a)) (pt k d 1)] lam = ev (n := 2) ![comp1 (g.B.A.act a) (pt k d 0), pt k d 1] lam * g.B.ad a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackTorsionPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_torsion_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ y : Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ X.B.t.G, ∃ x : ∀ k, Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ (X.C (b k)).P.A, y = (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod) ∧ ∀ x : ∀ k, Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ (X.C (b k)).P.A, (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod = 1 → ∀ k, x k ^ N = 1 := by
  first | exact @PositivityTheory.Xgf.cm_pack_torsion_points | exact PositivityTheory.Xgf.cm_pack_torsion_points
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CodimOneGramTwistAgreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.codim_one_gram_twist_agree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (t t' : SAB H X) (tp : SAB H (Spec (X.presheaf.stalk p.1))) (m : SABMap tp t (X.fromSpecStalk p.1)) (m' : SABMap (twistSAB tp g) t' (X.fromSpecStalk p.1)) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V), (∀ e, ∃ v : Sp (DualNumber Ω) ⟶ tp.G.left, v ≫ m.φ = (M.pt e).left ∧ v ≫ m'.φ = (M'.pt e).left) → ∀ (z : Sp ℂ ⟶ X), centre z = p.1 → ∀ (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ), M.GramAt t.PP.L z b Γ ↔ M'.GramAt t'.PP.L z b Γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.codim_one_gram_twist_eq | exact GlobalTheory.CompanionTheory.Ar.codim_one_gram_twist_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.codim_one_gram_twist_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexSectionFiniteCombinationStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_section_finite_combination : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ), LocallyOfFiniteType p → ∀ (B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y), B.IsLB → ∀ (O : Y.Opens) (x : GlobalTheory.SecC p σ B), (∀ i y, y ∉ GlobalTheory.CxPts.ptsIn p σ O → GlobalTheory.SecC.val x i y = 0) → ∃ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → B.Sec), (∀ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (ss j) ≤ O) ∧ GlobalTheory.SecC.val x = ∑ j, as j • GlobalTheory.CxPts.secVal p σ (ss j) := by
  first | exact @GlobalTheory.CompanionTheory.VanDescent.vanish_descent | exact GlobalTheory.CompanionTheory.VanDescent.vanish_descent | (intros; apply GlobalTheory.CompanionTheory.VanDescent.vanish_descent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsReindexDegreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_reindex_degree : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  first | exact @GlobalTheory.CompanionTheory.Relay.coords_reindex_degree | exact GlobalTheory.CompanionTheory.Relay.coords_reindex_degree | (intros; apply GlobalTheory.CompanionTheory.Relay.coords_reindex_degree <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_z_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (Z : Curve0 H ρ), Z.z ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeRight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem ptsIntegral_eq_sum_fundamental : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t :=
  SheetDecomposition.sheet_pieces_component

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsOrthogonalLieMetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_lie_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ h : LieMetric 𝔐.M y, h.Orth 𝔐.t.act := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MetricOrth.main | exact GlobalTheory.CompanionTheory.Ar.MetricOrth.main | (intros; apply GlobalTheory.CompanionTheory.Ar.MetricOrth.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteGroupSchemeSumExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_group_scheme_sum_extension : ∀ {X : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K : Type} [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (xl : Sp K ⟶ X) (A : FG M (Sp K)), (∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), A.sum U h = (h xl ^ n)⁻¹) → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (e : FG M (Sp K')), (∀ (U : Type) [CommGroup U] (h : (Sp K' ⟶ X) → U), e.sum U h = h (spMap (algebraMap K K') ≫ xl)) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K') (z : Z) (J), Good M z J → e.v r z J ^ n * A.v (r ≫ spMap (algebraMap K K')) z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelGenericCover
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem unitAt_of_pow_eq_one {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hN : Flat.NormalCpt ξ)
    {N : ℕ} (hN0 : N ≠ 0) {a : Ω} (ha : a ^ N = 1) (q : Cpt ξ) : unitAt ξ q a :=
  Flat.ZUnit.of_pow_of_normal hN hN0 (by rw [ha]; exact Flat.ZUnit.one)

theorem exists_full_level_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (K Ω : Type) [Field K] [Field Ω] [CharZero Ω] (i : K →+* Ω) (y : Sp K ⟶ Xo.XF c) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk (spMap i ≫ y ≫ Y.j) ⟶ Y.t.G)), 1 ≤ N → IsFullLevelAt D Y.t (spMap i ≫ y ≫ Y.j) N z ev → ∀ (X : Scheme.{0}) (ξ : Sp Ω ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ f : X ⟶ Y.X, ξ ≫ f = spMap i ≫ y ≫ Y.j → ∃ (t : SAB H X) (_ : SABMap t Y.t f) (ev' : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev' ∧ FullTorsion t.G ξ N ∧ ∀ q : Cpt ξ, unitAt ξ q (z : Ω) := by
  intro E _ _ _ H D l Xo c Y K Ω _ _ _ i y N z ev hN hlev X ξ _ hnorm f hf
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull f Y.t
  have hid : ξ ≫ f = spMap (RingHom.id Ω) ≫ spMap i ≫ y ≫ Y.j := by
    rw [hf]
    have : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [this, Category.id_comp]
  obtain ⟨ev', hev', -⟩ := GlobalTheory.T.full_level_structure_pullback E H D Y.X X Y.t t f m Ω Ω (RingHom.id Ω) (spMap i ≫ y ≫ Y.j) ξ hid N z ev hlev
  have hz : Units.map (RingHom.id Ω).toMonoidHom z = z := by ext; rfl
  rw [hz] at hev'
  obtain ⟨hprim, -, -, -, -, hfull, -⟩ := GlobalTheory.T.full_level_structure_properties E H D X t Ω ξ N hN z ev' hev'
  refine ⟨t, m, ev', hev', hfull, fun q => ?_⟩
  have hpow : (z : Ω) ^ N = 1 := by
    have := congrArg Units.val hprim.pow_eq_one
    simpa using this
  exact unitAt_of_pow_eq_one hnorm (by omega) hpow q

end GlobalTheory.CompanionTheory.Ar.XR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricConnectednessGeneralizes
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_isPullback_left {P Q X S T U : Scheme.{0}} {t : P ⟶ X} {v : P ⟶ U} {p : X ⟶ S}
    {g : U ⟶ T} {f : T ⟶ S} {t' : Q ⟶ X} {v' : Q ⟶ T}
    (h : IsPullback t v p (g ≫ f)) (h' : IsPullback t' v' p f) :
    ∃ u : P ⟶ Q, IsPullback u v v' g := by
  refine ⟨h'.lift t (v ≫ g) (by simpa using h.w), ?_⟩
  refine IsPullback.of_right (h₁₂ := t') (h₂₂ := f) (v₁₃ := p) ?_ (by simp) h'
  simpa using h

theorem spMap_comp_spMap {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem geometricallyConnected_of_local {k A E L K : Type} [CommRing k] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Field E] [Field L] [Field K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (φ : k →+* A) (a : k →+* E)
    (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp φ)
    (hE : GeometricallyConnected (pullback.snd p (spMap a)))
    (j : A →+* L) (hj : j.Flat) (c : k →+* K) (d : K →+* L) (hd : d.comp c = j.comp φ) :
    GeometricallyConnected (pullback.snd p (spMap c)) := by
  have hPA : IsPullback (pullback.fst p (spMap φ)) (pullback.snd p (spMap φ)) p (spMap φ) :=
    .of_hasPullback _ _
  haveI : Smooth (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : IsProper (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : Flat (pullback.snd p (spMap φ)) := inferInstance
  let eA : Sp A ⟶ pullback p (spMap φ) :=
    pullback.lift (spMap φ ≫ e) (𝟙 _) (by rw [Category.assoc, hs]; simp)
  have heA : eA ≫ pullback.snd p (spMap φ) = 𝟙 _ := pullback.lift_snd _ _ _

  have hW : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)) := .of_hasPullback _ _
  have hbot : spMap (IsLocalRing.residue A) ≫ spMap φ = spMap b ≫ spMap a := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hb]
  have hW' := hW.paste_horiz hPA
  rw [hbot] at hW'
  obtain ⟨u, hu⟩ := exists_isPullback_left hW' (.of_hasPullback p (spMap a))
  haveI : Smooth (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hW ‹_›
  haveI : GeometricallyConnected
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hu hE
  have hGI : GeometricallyIntegral
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    GlobalTheory.geometricallyIntegral_of_smooth _
  haveI hA : IsIso (pullback.snd p (spMap φ)).appTop :=
    isIso_appTop_of_closedFibre A _ _ eA heA inferInstance inferInstance hGI

  have hL : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd p (spMap φ)) (spMap j) := .of_hasPullback _ _
  haveI : Flat (spMap j) := Flat.SpecMap_iff.2 hj
  haveI hL1 : IsIso (pullback.snd (pullback.snd p (spMap φ)) (spMap j)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback hL
  have hbot' : spMap j ≫ spMap φ = spMap d ≫ spMap c := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hd]
  have hL' := hL.paste_horiz hPA
  rw [hbot'] at hL'
  obtain ⟨w, hw⟩ := exists_isPullback_left hL' (.of_hasPullback p (spMap c))
  haveI : Flat (spMap d) := Flat.SpecMap_iff.2 (by
    algebraize [d]
    exact RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : Surjective (spMap d) := by
    refine ⟨fun x => ?_⟩
    have y : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  haveI hK : IsIso (pullback.snd p (spMap c)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback_of_surjective hw
  exact geometricallyConnected_of_isIso_appTop K _ _ inferInstance inferInstance hK

theorem geometricallyConnected_of_localDomain {k B A E K : Type} [CommRing k] [CommRing B]
    [IsDomain B] [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field E] [Field K]
    [Algebra B K] [IsFractionRing B K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (q : k →+* B) (ψ : B →+* A)
    (hψ : Function.Injective ψ) (a : k →+* E) (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp (ψ.comp q))
    (hE : GeometricallyConnected (pullback.snd p (spMap a))) :
    GeometricallyConnected (pullback.snd p (spMap ((algebraMap B K).comp q))) := by
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp ψ) :=
    (IsFractionRing.injective A (FractionRing A)).comp hψ
  refine geometricallyConnected_of_local (A := A) (E := E) (L := FractionRing A) X p e hs (ψ.comp q)
    a b hb hE (algebraMap A (FractionRing A)) (RingHom.flat_algebraMap_iff.2 inferInstance) _
    (IsFractionRing.lift hinj) ?_
  ext r
  simp only [RingHom.comp_apply]
  exact IsFractionRing.lift_algebraMap hinj (q r)

theorem stableUnderGeneralization_geometricallyConnected_fibre :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
      (e : Sp k ⟶ X), e ≫ p = 𝟙 _ → Smooth p → IsProper p →
      StableUnderGeneralization {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ X p e hs _ _ x y hyx hx
  have hle : y.asIdeal ≤ x.asIdeal := (PrimeSpectrum.le_iff_specializes y x).2 hyx
  have hq : Function.Surjective (Ideal.Quotient.mk y.asIdeal) := Ideal.Quotient.mk_surjective
  obtain ⟨Q, hQ, hcomap⟩ : ∃ Q : Ideal (k ⧸ y.asIdeal), ∃ _ : Q.IsPrime,
      x.asIdeal = Q.comap (Ideal.Quotient.mk y.asIdeal) := by
    refine ⟨x.asIdeal.map (Ideal.Quotient.mk y.asIdeal),
      Ideal.map_isPrime_of_surjective hq (by rw [Ideal.mk_ker]; exact hle), ?_⟩
    rw [Ideal.comap_map_of_surjective _ hq, eq_comm, sup_eq_left]
    refine le_trans ?_ hle
    rw [show Ideal.comap (Ideal.Quotient.mk y.asIdeal) ⊥ = RingHom.ker (Ideal.Quotient.mk y.asIdeal)
      from rfl, Ideal.mk_ker]
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_localization Q.primeCompl_le_nonZeroDivisors
  have := geometricallyConnected_of_localDomain (K := y.asIdeal.ResidueField) X p e hs
    (Ideal.Quotient.mk y.asIdeal) (algebraMap (k ⧸ y.asIdeal) (Localization.AtPrime Q))
    (IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors)
    (algebraMap k x.asIdeal.ResidueField)
    (Ideal.ResidueField.map x.asIdeal Q (Ideal.Quotient.mk y.asIdeal) hcomap)
    (by
      ext r
      simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
      rfl) hx
  exact this

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfCommGroupNsmulSurjectiveStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_of_commGroup_nsmul_surjective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 G) ^ n : G ⟶ G).left) → GeometricallyConnected G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow <;> assumption)
end

