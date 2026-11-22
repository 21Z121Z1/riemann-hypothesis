import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquiv
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0277
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0186
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquivStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactification_comp_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ σ, GoodEmb c σ → ∃ κ : Comp Xo c ≃ (U σ).Comp, (∀ Z k, Over (U σ) (e Z) k ↔ k = κ Z) ∧ ∀ Z k, k ≠ κ Z → ∀ y ∈ ((U σ).X k).dom, rdU (U σ) (e Z) k y = 0 ∧ ∀ a, ∀ f ∈ cuspOn U h a Z, rdU (U σ) f k y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.comp_over | exact GlobalTheory.CompanionTheory.Ar.Rec.comp_over | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.comp_over <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_line_p_adic_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (ϖ : O) (p : ℕ), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → Function.Injective β → (∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range) → Y.SplitFibres → Y.N3 → ∃ 𝓗 : HodgeLat Z.M.lat Z.ρ H.bar (D.p + D.q), ∀ σ : E →+* Z.Ω, 𝓗.DegZero σ (Z.inc (β ϖ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_model | exact GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Rec.FlatTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Comp Xo c) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), 1 ≤ r → IsUnf U → (∀ b : Om Z, IsAlgebraic c.F b → b ∈ (algebraMap c.F (Om Z)).range) → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → (Set.range y ⊆ (Z : Set (Xo.XF c)) ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp.comp_iff_period | exact GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp.comp_iff_period | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp.comp_iff_period <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpOnto

theorem isHolTo_slice {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {B : Set V} {b : V} (hb : b ∈ B) {c : V × V' → (Sp ℂ ⟶ X)}
    (h : IsHolTo (B ×ˢ Set.univ) c) : IsHolTo Set.univ (fun z => c (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hj : Differentiable ℂ (fun z : V' => (b, z)) := (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage hj.continuous
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_true, hb, true_and] using h3
  · exact h2.comp hj.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩

theorem isHolTo_const_param {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V']
    [NormedSpace ℂ V'] {X : Scheme.{0}} {c : V' → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ c) :
    IsHolTo (Set.univ ×ˢ Set.univ) (fun p : V × V' => c p.2) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage (continuous_snd (X := V) (Y := V'))
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_self, true_and] using h3
  · exact h2.comp differentiable_snd.differentiableOn fun z hz => ⟨trivial, hz.2⟩

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem isHolTo_ex (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    IsHolTo Set.univ (fun z => (e.ex b z).left) :=
  isHolTo_slice (V := Fin n → ℂ) (V' := Fin g → ℂ) (X := G.left) (b := b) (B := B)
    (c := fun bz => (e.ex bz.1 bz.2).left) hb e.hol

def atPoint (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    FamExp G M (Set.univ : Set (Fin 0 → ℂ)) (fun _ => ψ b) where
  ex _ z := e.ex b z
  add _ _ z w := e.add b hb z w
  hol := isHolTo_const_param (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (e.ex b z).left) (isHolTo_ex e hb)
  diff _ _ a := e.diff b hb a
  log b₀ _ := by
    obtain ⟨V, N, f, L, h1, h2, h3, h4⟩ := e.log b hb
    have hφ : Continuous (fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) := by fun_prop
    have hφ' : Continuous (fun p : (Fin 0 → ℂ) × (Fin g → ℂ) => (b, p.2)) := by fun_prop
    refine ⟨V, N, f, fun p => L (b, p.2), h1, ?_, ?_, ?_⟩
    · exact AnalyticAt.comp' (f := fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) h2
        (analyticAt_const.prod analyticAt_snd)
    · exact (hφ'.tendsto (b₀, 0)).eventually h3
    · exact (hφ.tendsto (b₀, _)).eventually h4

end GlobalTheory.CompanionTheory.Ar.Flat.ExpOnto

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ExpOnto

theorem famExp_ex_surjective : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ)
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ))
    (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Function.Surjective (e.ex b) := by
  intro R _ G _ _ g n M B ψ e hG b hb
  have hc : IsHolTo (Metric.ball (0 : ℂ) 1) (fun _ : ℂ => spMap (ψ b)) :=
    fun U f => ⟨Metric.isOpen_ball.inter isOpen_const, differentiableOn_const _⟩
  obtain ⟨m, ρ, u, hρ, -, -, hu, -⟩ := GlobalTheory.RelExp.exists_exp_along_disc (Sp R) G (fun _ => spMap (ψ b)) 1 hG one_pos hc
  obtain ⟨hadd, hsurj, hhol, -⟩ := hu 0 (Metric.mem_ball_self hρ)
  obtain ⟨h, -, hh⟩ := exists_linear_lift_of_additive_family R G g 0 M Set.univ (fun _ => ψ b) (atPoint e hb) m Set.univ
    (fun _ z => u 0 z) isOpen_univ subset_rfl (fun _ _ z w => hadd z w)
    (isHolTo_const_param (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (u 0 z).left) hhol)
  intro x
  obtain ⟨z, rfl⟩ := hsurj x
  exact ⟨h 0 z, (hh 0 trivial).1 z⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_generic_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), Nonempty (Small.GenFrame Or) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenEx.genFrame_exists | exact GlobalTheory.CompanionTheory.Ar.GenEx.genFrame_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.GenEx.genFrame_exists <;> assumption)
end

