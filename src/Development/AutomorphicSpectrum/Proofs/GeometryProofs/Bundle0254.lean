import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0251
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightCharFreeGeometric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0252
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0184
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0243
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0242
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0238
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0207
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0253
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0245
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0165
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationIsoTransferStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_pack_pure_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (τ : E →+* ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → LinearIndependent (𝓞 E) x → (∃ v w, X.IsCMFrame τ hx v w) ∧ ∀ v w, X.IsCMFrame τ hx v w → IsFramed (Set.range X.y) τ X.β X.y v w := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cm_pack_pure_frame | exact GlobalTheory.CompanionTheory.Relay.cm_pack_pure_frame | (intros; apply GlobalTheory.CompanionTheory.Relay.cm_pack_pure_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPeriodAlgebraicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmPack_field_ge_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ X : CMPack Z c FU i hP, k ≤ X.K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given | exact GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrame
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem gramAt_unique_of_polarisedAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ' → Γ = Γ' := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z r b Γ Γ' hP h1 h2
  obtain ⟨v, hv, hΓ⟩ := h1
  obtain ⟨v', hv', hΓ'⟩ := h2
  have hgen : GlobalTheory.CompanionTheory.Ar.IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hvv : v = v' := funext fun i => GlobalTheory.CompanionTheory.Ar.LieModel.ValAt.unique hgen (hv i) (hv' i)
  subst hvv
  obtain ⟨V, _, _, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨h, hh, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z V M' hP
  have hpre : ∀ i, ∃ e, M'.pt e = v i := by
    intro i
    have hT : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G z (v i) := by
      obtain ⟨-, hT, -⟩ := hΓ i i
      exact hT
    exact M'.onto (v i) hT
  ext p q
  obtain ⟨e, he⟩ := hpre p
  obtain ⟨f, hf⟩ := hpre q
  have k1 := (hh e f (Γ p q)).1 (by rw [he, hf]; exact hΓ p q)
  have k2 := (hh e f (Γ' p q)).1 (by rw [he, hf]; exact hΓ' p q)
  rw [k1, k2]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFrames
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem valAt_sum_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [AddCommGroup L] [Module Ω L] (M : LieModel G ξ L)
    {z : Spec (CommRingCat.of ℂ) ⟶ X} {V : Type} [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V)
    (hz : genPt ξ ⤳ centre z) {I : Type} (s : Finset I) (b : I → L) (x : I → V)
    (hx : ∀ p, M.ValAt z (b p) (Mz.pt (x p))) (a : I → Ω) (c : I → ℂ) (hc : ∀ p, ValAt ξ z (a p) (c p)) :
    M.ValAt z (∑ p ∈ s, a p • b p) (Mz.pt (∑ p ∈ s, c p • x p)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [Mz.pt_zero] using M.valAt_zero hz
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, Finset.sum_insert hp, Mz.add]
    refine LieModel.ValAt.add ?_ ih
    obtain ⟨h1, g, hg, hg'⟩ := hc p
    have := (hx p).smul h1 g
    rw [hg, hg', ← Mz.pt_smul] at this
    exact this

theorem gramAt_change (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b b' : Fin r → 𝔐.Li)
    (Γ Γ' : Matrix (Fin r) (Fin r) ℂ) (T : Matrix (Fin r) (Fin r) Ω) (Tz : Matrix (Fin r) (Fin r) ℂ)
    (hP : HodgeMetric.PolarisedAt 𝔐.t z) (hG : 𝔐.M.GramAt 𝔐.t.PP.L z b Γ) (hG' : 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ')
    (hb : ∀ q, b' q = ∑ p, T p q • b p) (hT : ∀ p q, ValAt 𝔐.ξ z (T p q) (Tz p q)) :
    Γ' = Tz.conjTranspose * Γ * Tz := by
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨h, hh, -, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z V Mz hP
  obtain ⟨v, hv, hΓ⟩ := hG
  obtain ⟨v', hv', hΓ'⟩ := hG'
  choose x hx using fun p => Mz.onto (v p) (hv p).isTanAt
  have hz : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have key : ∀ q, Mz.pt (∑ p, Tz p q • x p) = v' q := fun q => by
    have h1 := valAt_sum_smul 𝔐.M Mz hz Finset.univ b x (fun p => by rw [hx]; exact hv p)
      (fun p => T p q) (fun p => Tz p q) (fun p => hT p q)
    rw [← hb q] at h1
    exact h1.unique 𝔐.tie.gen (hv' q)
  have e1 : ∀ p q, Γ p q = h (x p) (x q) := fun p q =>
    (hh _ _ _).1 (by rw [hx, hx]; exact hΓ p q)
  have e2 : ∀ p q, Γ' p q = h (∑ i, Tz i p • x i) (∑ j, Tz j q • x j) := fun p q =>
    (hh _ _ _).1 (by rw [key, key]; exact hΓ' p q)
  ext p q
  rw [e2]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, e1, map_sum, LinearMap.sum_apply, map_smul,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, RCLike.star_def,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightCharFreeGeometricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_char_free_geometric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X), PowFns t → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X), GeomPF t x → ∀ (d r : ℕ) (g : GermAt t x d), HChar g.B r → HFree g.B r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hfree_geom | exact GlobalTheory.CompanionTheory.Ar.Flat.hfree_geom | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hfree_geom <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hol_unif_period_matrix_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (N : ℕ) (ζ : ℂˣ) (y y' : Fin g → ℂ), 0 < N → y ∈ e.per b → y' ∈ e.per b → GlobalTheory.UU.CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im : ℝ) : ℂ) / N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interior_point_lattice_data : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 1 ≤ D.p + D.q → 𝔐.Interior z → Top.Given → ∀ (A₀ : Type) (v : A₀ → (epsAt z ⟶ 𝔐.t.G)), (∀ i, IsTanAt 𝔐.t.G z (v i)) → ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (x : A₀ → Fin g → ℂ), FibreLatVec 𝔐.t z R x v ∧ (∀ i j, HodgeIP 𝔐.t.G 𝔐.t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j))) ∧ ∀ σ, 𝔐.LabVal z id σ → ∀ s, Module.finrank ℂ (eigSp R.B (σ s)) = labelRk D s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SabModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_obj_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → l.A = 1 → ∀ (ρ : L) (σ : L →+* ℂ),
    σ ρ = H.rt0 →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ D.q)) →
    TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)) →
    ∀ (F₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ F₀ → ∀ hK : KA l ≤ F₀,
    ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (hF : F₀ ≤ F) (e : L →+* F)
      (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion (hK.trans hF)).toRingHom)),
      (∀ x, ((e x : F) : ℂ) = σ x) ∧ Nonempty (SABMap o.t t (spMap e)) := by
  intro E _ _ _ H D l L _ _ t ht hA ρ σ hσ hs I F₀ hF₀ hK
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨F₁, hF₁, e₁, he₁, hT⟩ := GlobalTheory.T.torsion_points_number_field L σ (pol t ht) l.M hM
  have hfin : FiniteDimensional ℚ ↥(F₀ ⊔ F₁) := inferInstance
  let i₁ : F₁ →+* ↥(F₀ ⊔ F₁) := (IntermediateField.inclusion le_sup_right).toRingHom
  let e : L →+* ↥(F₀ ⊔ F₁) := i₁.comp e₁
  have he : ∀ x, ((e x : ↥(F₀ ⊔ F₁)) : ℂ) = σ x := he₁
  obtain ⟨t₂, ⟨m⟩⟩ := exists_sab (spMap e) t
  obtain ⟨w, gw, -⟩ := m.lin
  have hL₂ : LBIso t₂.PP.L (t.PP.L.pull m.cm.F) := ⟨w, gw⟩
  have ht₂ : IsPrincipal t₂ :=
    ⟨MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 ht.1,
      relAmple_pull m.cart.1 t.PP.isLB t₂.PP.isLB ((isGen_iff w).1 gw) ⊤ (isAffineOpen_top _) (fun _ => trivial) ht.2.1,
      kTriv_pull m.cart t.PP.isLB t₂.PP.isLB ((isGen_iff w).1 gw) ht.2.2⟩
  let x₂ : Sp ℂ ⟶ Sp ↥(F₀ ⊔ F₁) := spMap (algebraMap ↥(F₀ ⊔ F₁) ℂ)
  have hx : x₂ ≫ spMap e = spMap σ := by
    rw [← spMap_comp]
    exact congrArg spMap (RingHom.ext he)
  obtain ⟨Φ, hΦ, hW⟩ : ∃ Φ : (Over.mk x₂ ⟶ t₂.G) ≃* (Over.mk (spMap σ) ⟶ t.G),
      (∀ x, (Φ x).left = x.left ≫ m.φ) ∧ ∀ (k : ℕ) x y c, Out.WeilIs t.G t.PP.L k (Φ x) (Φ y) c →
        Out.WeilIs t₂.G t₂.PP.L k x y c := by
    have key : ∀ y : Sp ℂ ⟶ Sp L, x₂ ≫ spMap e = y → ∃ Φ : (Over.mk x₂ ⟶ t₂.G) ≃* (Over.mk y ⟶ t.G),
        (∀ x, (Φ x).left = x.left ≫ m.φ) ∧ ∀ (k : ℕ) x y c, Out.WeilIs t.G t.PP.L k (Φ x) (Φ y) c →
          Out.WeilIs t₂.G t₂.PP.L k x y c := by
      rintro _ rfl
      exact ⟨GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x₂), fun _ => rfl, fun k x y c h =>
        GlobalTheory.Relabel.weilIs_push t.PP.isLB t₂.PP.isLB m.cart hL₂ (Over.mk x₂) _ rfl k x y _ _ c rfl rfl h⟩
    exact key _ hx
  let I₂ : TateIso D ℂ (Over.mk x₂ ⟶ t₂.G) (fun a g => g ≫ t₂.act.act a)
      (fun n g g' c => Out.WeilIs t₂.G t₂.PP.L n g g' (unitOn c)) :=
    GlobalTheory.ObjPull.tateMove Φ (fun c x => Over.OverMorphism.ext (by
      show (Φ _).left = (Φ x ≫ _).left
      rw [hΦ, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc]
      exact congrArg _ (m.act c))) (fun n x y c h => hW n x y _ h) I
  have hsec : ∀ a : D.La, ∃ s : 𝟙_ (Over (Sp ↥(F₀ ⊔ F₁))) ⟶ t₂.G, toUnit _ ≫ s = I₂.ev l.M a := fun a => by
    obtain ⟨y₁, hy₁, hy₂⟩ : ∃ y : Sp F₁ ⟶ t.G.left, y ≫ t.G.hom = spMap e₁ ∧
        spMap (algebraMap F₁ ℂ) ≫ y = (I.ev l.M a).left := hT (I.ev l.M a) ((I.onto l.M hM _).2 ⟨a, rfl⟩)
    have hw₁ : (spMap i₁ ≫ y₁) ≫ t.G.hom = 𝟙 _ ≫ spMap e := by
      rw [Category.assoc]
      refine (congrArg (spMap i₁ ≫ ·) hy₁).trans ?_
      rw [Category.id_comp]
      exact (spMap_comp _ _).symm
    refine ⟨Over.homMk (m.cart.1.lift _ _ hw₁) (m.cart.1.lift_snd _ _ _), ?_⟩
    apply Φ.injective
    show Φ _ = Φ (Φ.symm _)
    rw [MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rw [hΦ, Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    show (x₂ ≫ m.cart.1.lift _ _ hw₁) ≫ m.φ = _
    rw [Category.assoc]
    refine (congrArg (x₂ ≫ ·) (m.cart.1.lift_fst _ _ hw₁)).trans ?_
    rw [← hy₂, ← Category.assoc]
    exact congrArg (· ≫ y₁) (spMap_comp _ _).symm
  have hK₂ : KA l ≤ F₀ ⊔ F₁ := hK.trans le_sup_left
  have hρ : IntermediateField.inclusion hK₂ (baseKA l).ρ = e ρ := Subtype.ext (by
    refine Eq.trans ?_ (he ρ).symm
    rw [hσ]
    rfl)
  obtain ⟨o, ho⟩ := GlobalTheory.T.principal_lie_multiplicity_type E H D l (F₀ ⊔ F₁) hK₂ t₂ ht₂ hA (fun k _ _ g τ => by
    have hp : ∀ n, LieMult t₂.act (spMap g) τ n ↔ LieMult t.act (spMap (g.comp e)) τ n := fun n =>
      (GlobalTheory.LiePull.lieMult_pull (𝓞 E) _ _ _ _ _ _ t.act t₂.act m.cart m.act k (spMap g) τ n).trans
        (iff_of_eq (congrArg (fun x => LieMult t.act x τ n) (spMap_comp _ _).symm))
    have h := hs k (g.comp e) τ
    rw [hρ, hp, hp]
    exact h) I₂ hsec
  refine ⟨F₀ ⊔ F₁, hfin, le_sup_left, e, o, he, ?_⟩
  rw [ho]
  exact ⟨m⟩

theorem exists_embedding_rt0 {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {L : Type} [Field L]
    [NumberField L] (ρ : L) (hρ : ρ ^ 2 = -(H.d : L)) : ∃ σ : L →+* ℂ, σ ρ = H.rt0 := by
  obtain ⟨σ₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  have h : (σ₀ ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨σ₀, h⟩
  · refine ⟨(starRingEnd ℂ).comp σ₀, ?_⟩
    have hc : starRingEnd ℂ H.rt0 = -H.rt0 := by
      have hre : H.rt0.re = 0 := by
        have h1 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
          have := congrArg Complex.im H.sqrt_neg_disc_sq
          simpa [pow_two, Complex.mul_im] using this
        have h2 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
          have := congrArg Complex.re H.sqrt_neg_disc_sq
          simpa [pow_two, Complex.mul_re] using this
        have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
        rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by linarith) with h3 | h3
        · exact h3
        · rw [h3] at h2
          nlinarith [mul_self_nonneg H.rt0.re]
      apply Complex.ext <;> simp [hre]
    show starRingEnd ℂ (σ₀ ρ) = _
    rw [h, map_neg, hc, neg_neg]

theorem exists_sab_model : N1ab → PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g ρ → LieMult t.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ q')) → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (t' : SAB H (Sp (𝓞 L'))) (tK : SAB H (Sp L')), Nonempty (SABMap tK t' (spMap (algebraMap (𝓞 L') L'))) ∧ Nonempty (SABMap tK t (spMap e)) := by
  intro hN hP E _ _ _ H L _ _ t ht ⟨ρ, p', q', hρ, hs⟩
  by_cases h0 : p' + q' = 0
  · obtain ⟨rfl, rfl⟩ : p' = 0 ∧ q' = 0 := by omega
    obtain ⟨t', ⟨m⟩⟩ := GlobalTheory.T.principal_good_reduction_extends E H L t ht fun σ τ => by
      by_cases h : τ H.rt = σ ρ
      · exact (hs ℂ σ τ).1 h
      · exact (hs ℂ σ τ).2 h
    exact ⟨L, inferInstance, inferInstance, RingHom.id L, t', t, ⟨m⟩,
      ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast (GlobalTheory.ObjComp.sabMapId t) (Spec.map_id _).symm⟩⟩
  · obtain ⟨σ, hσ⟩ := exists_embedding_rt0 H ρ hρ
    obtain ⟨D, rfl, rfl, ⟨I⟩⟩ := GlobalTheory.T.tate_iso_datum_exists E H L t ht σ p' q' fun τ => by
      have := hs ℂ σ τ
      rwa [hσ] at this
    have hD : 1 ≤ D.p + D.q := by omega
    let Xo : ∀ l : Level H, Moduli D l := fun l => (hN E H D l hD).some
    obtain ⟨l, hA, hg⟩ := GlobalTheory.GlobalModelGuards.exists_good_level H
    obtain ⟨c⟩ := GlobalTheory.ModuliProbe.coeff_nonempty l
    haveI := c.fin
    obtain ⟨Yl, -, h6⟩ := hP.2 E H D hD Xo
    obtain ⟨Y, -, -⟩ := h6 l c hg hA
    obtain ⟨F, hfin, hF, e, o, -, ⟨m⟩⟩ := exists_obj_ext E H D l L t ht hA ρ σ hσ hs I c.F c.fin c.le
    haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
    obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := (Xo l).rep (Sp F) _ inferInstance o
    let bF : c.F →+* F := (IntermediateField.inclusion hF).toRingHom
    let y : Sp F ⟶ (Xo l).XF c := pullback.lift f (spMap bF) (by
      rw [hf, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun x => Subtype.ext rfl))
    have hy1 : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
    have hy2 : y ≫ pullback.snd _ _ = spMap bF := pullback.lift_snd _ _ _
    obtain ⟨yt, hyt⟩ := GlobalTheory.T.number_field_point_integral_lift E H D l (Xo l) c c.fin Y F bF y hy2
    obtain ⟨t', ⟨m'⟩⟩ := exists_sab yt Y.t
    rw [← hy1] at mf
    obtain ⟨m₁, -⟩ := ObjComp.objMap_cancel Y.m0 mf
    obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m m₁.toSABMap
    have n' : SABMap o.t Y.t (spMap (algebraMap (𝓞 F) F) ≫ yt) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n (by
      rw [hyt]; rfl)
    obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m' n'
    exact ⟨F, inferInstance, inferInstance, e, t', o.t, ⟨k⟩, ⟨m⟩⟩

end GlobalTheory.CompanionTheory.Ar.SabModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalHermitianFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_hermitian_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (_ : SABMap tK t (spMap (algebraMap (𝓞 L) L))), IsPrincipal tK → ∃ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G (𝟙 _) B.carrier), IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeFibre.exists_hermitianBundle | exact GlobalTheory.CompanionTheory.Ar.HodgeFibre.exists_hermitianBundle | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeFibre.exists_hermitianBundle <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionArchimedeanFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameEx

theorem exists_goodUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X)
    (z : Sp ℂ ⟶ X) (t' : SAB H (Sp ℂ)) (m : SABMap t' t z), IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L →
    IsAbelianScheme t'.G ∧ ∃ (g : ℕ) (u : HolUnif t'.G (t.PP.L.pull m.φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  intro E _ _ _ H X t z t' m hP hA
  have hab : IsAbelianScheme t'.G := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ t'.G hab
  obtain ⟨u₀, hc⟩ := GlobalTheory.T.exists_exp_chart_coordinates t'.G t'.PP.L g hab hA hg
  obtain ⟨u, Hm, χ, hex, hH, hχ, hlaw⟩ := GlobalTheory.T.theta_multiplier_normal_form t'.G t'.PP t'.cub g u₀
  obtain ⟨N, J, Θ, hN, hd, hq, hne, hsep⟩ := GlobalTheory.T.exists_theta_basis_of_factor t'.G t'.PP.L g u Hm χ t'.PP.isLB hab hA hlaw
  have hpos := GlobalTheory.T.theta_functions_finite_dim g u.Λ u.discrete u.full Hm χ N J Θ hH hχ hN hd hq hne hsep
  have hAH : u.IsAH Hm χ := ⟨hH, hpos, hχ, hlaw⟩
  obtain ⟨ht₁, ht₂⟩ := @GlobalTheory.TangentOrigin.tangent_bijection_of_values @GlobalTheory.valAt'_rules t'.G _ t'.PP.L g u
    (by simpa only [hex] using hc)
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  have hL := t'.PP.isLB
  have hM := pull_isLB t.PP.isLB m.φ
  exact ⟨hab, g, GlobalTheory.ArchMetricCompare.carry u hL hM hw₀, Hm, χ, GlobalTheory.ArchMetricCompare.carry_isAH hL hM hw₀ hAH, ht₁, ht₂⟩

end GlobalTheory.CompanionTheory.Ar.Sl.FrameEx

open GlobalTheory.CompanionTheory.Ar.Sl.FrameEx in

theorem GlobalTheory.CompanionTheory.Ar.Sl.frames_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), Nonempty (D.Frame σ) ∧ ∀ a : D.Frame σ, (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n), ∃! θ, a.IsFn s θ) ∧ (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n) θ, a.IsFn s θ → a.IsTheta n θ) ∧ ∀ x : D.B.carrier, (∃! c, D.IsVec a x c) ∧ ∀ c, D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re ∧ (x ≠ 0 → c ≠ 0) := by
  intro E _ _ _ H L _ _ D σ
  obtain ⟨t', m, hP, hA⟩ := GlobalTheory.T.complex_abelian_fibre_ample E H L D σ
  obtain ⟨hab, g, u, Hm, χ, hAH, d₁, d₂⟩ := exists_goodUnif E H _ D.t (emb σ) t' m hP hA
  have hcart : IsGrpPullback t'.G D.t.G (emb σ) m.φ := m.cart
  have hg : D.g = g := GlobalTheory.T.uniformization_dim_eq_pp_dim E H L D σ t'.G m.φ _ g u hcart d₁ d₂
  subst hg
  refine ⟨GlobalTheory.T.exists_archimedean_frame _ D.t.G D.t.PP (emb σ) t'.G m.φ D.g u Hm χ hcart hAH, fun a => ?_⟩
  obtain ⟨e, hmon, -⟩ := grpPullback_iso a.cart hcart
  haveI := hmon
  obtain ⟨a₁, a₂⟩ := GlobalTheory.T.uniformization_iso_transfer t'.G a.A _ _ D.g u a.u e hab d₁ d₂
  refine ⟨fun n s => GlobalTheory.T.theta_function_unique _ D.t.G D.t.PP (emb σ) D.g a n s,
    fun n s θ h => ⟨GlobalTheory.T.theta_function_differentiable _ D.t.G D.t.PP (emb σ) D.g a n s θ h,
      GlobalTheory.T.theta_add_lattice_eq_of_isFn _ D.t.G D.t.PP (emb σ) D.g a n s θ h⟩,
    fun x => ⟨GlobalTheory.T.frame_coordinates_unique E H L D σ a a₁ a₂ x, fun c hc => ?_⟩⟩
  have hl := GlobalTheory.T.archimedean_frame_of_pullback E H L D σ t'.G m.φ D.g u Hm χ hab hcart d₁ d₂ hAH a x c hc
  exact ⟨hl, GlobalTheory.T.nonzero_coords_of_nonzero_vector E H L D σ a x c hl⟩

end
end

