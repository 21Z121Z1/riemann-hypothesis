import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0117
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyReindexed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationLower
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartFieldChange

theorem exists_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ := by
  intro E _ _ _ H S t L L' _ _ z P e
  obtain ⟨P', mK, mB, h₁, h₂, -⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange E H S t L L' z P e
  exact ⟨P', mK, mB, h₁, h₂⟩

end GlobalTheory.CompanionTheory.Ar.AbPartFieldChange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChangeAltBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abPart_comp_spMap_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ ∧ GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e P.τ P'.τ mK.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedGramDetPositiveStatement
section
open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_gram_det_positive : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) (r k : ℕ) (v : Fin r → V) (q : Fin k → A.Λ), IsOFamily A.ρ A.I v → A.IsAdapted s v q → (∀ i, (q i : V) ∈ A.eig s) → ∀ e : L →+* ℂ, 0 < A.gramDet e q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted | exact GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AntisymmetricPerturbationHoldsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antisymmetric_perturbation_holds : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.antisymPerturbation_holds | exact GlobalTheory.CompanionTheory.Ar.Link.antisymPerturbation_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.antisymPerturbation_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyReindexedStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_reindexed : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ (Gf : GenFibre (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (mCoordIdeal y)) (ch : ∀ k : FibreBlock bk, J k.1), (∀ k : FibreBlock bk, Gf.x' ⟨k.1, ch k⟩ ≠ 0) ∧ Module.finrank Gf.Φ (IntermediateField.adjoin Gf.Φ (Set.range fun q : Σ k : FibreBlock bk, J k.1 => Gf.x' ⟨q.1.1, q.2⟩ / Gf.x' ⟨q.1.1, ch q.1⟩)) = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | exact GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieMetricBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

theorem GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re :=
  @PositivityTheory.Xgn.quotient_uniformization_lower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charVal_multiplicative : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] (a : Sp A ⟶ S), (∀ t t' : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = charVal t' χ) → t = t') ∧ (∀ (t t' : Over.mk a ⟶ splitTorus S X) (χ : X), charVal (t * t') χ = charVal t χ * charVal t' χ) ∧ (∀ χ : X, charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1) ∧ (∀ (t : Over.mk a ⟶ splitTorus S X), charVal t 0 = 1 ∧ ∀ χ χ', charVal t (χ + χ') = charVal t χ * charVal t χ') ∧ (∀ w : Multiplicative X →* A, ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = w (Multiplicative.ofAdd χ)) ∧ ∀ (A' : Type) [CommRing A'] (g : A →+* A') (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk (spMap g ≫ a) ⟶ splitTorus S X), t'.left = spMap g ≫ t.left → ∀ χ, charVal t' χ = g (charVal t χ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusPoints.main | exact GlobalTheory.CompanionTheory.Ar.TorusPoints.main | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusPoints.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_closure_coords : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ w : (Σ k, J k) → ℂ, w ∈ closure {w' : (Σ k, J k) → ℂ | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w'} →
      (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchC.closed_coords' | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchC.closed_coords' | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchC.closed_coords' <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsInCoordRatioField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CstChart

theorem germ_top_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {q : X}
    (hq : ξ (IsLocalRing.closedPoint Ω) ⤳ q) :
    X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) ≫ X.presheaf.stalkSpecializes hq ≫
        Scheme.stalkClosedPointTo ξ = ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
  have e : ∀ (f : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ ξ ⁻¹ᵁ ⊤),
      (Spec (CommRingCat.of Ω)).presheaf.map f.op = 𝟙 _ := fun f => (Spec (CommRingCat.of Ω)).presheaf.map_id _
  erw [e]
  simp

theorem ringHom_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] (φ : O →+* Ω) (s : X ⟶ Spec (CommRingCat.of O))
    (h : ξ ≫ s = Spec.map (CommRingCat.ofHom φ)) (p : Cpt ξ) (o : O) : φ o ∈ regAt ξ p := by
  obtain ⟨q, hq⟩ := p
  refine ⟨X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial)
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)), ?_⟩
  have h1 := germ_top_stalk ξ hq
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ ξ.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom φ := by
    have : s.appTop ≫ ξ.appTop = (ξ ≫ s).appTop := by simp
    rw [reassoc_of% this, h]
    simp
  have h3 := congrArg (fun f => f.hom o) h2
  have h4 := congrArg (fun f => f.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  rw [CommRingCat.hom_ofHom] at h3
  refine Eq.trans ?_ (h4.trans h3)
  rfl

theorem segre_adjoin_le {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) (cc : (k : K) → J k) :
    Algebra.adjoin ℤ (Set.range fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, cc k⟩) ≤
      (Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩)).restrictScalars ℤ := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c', rfl⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, cc k⟩ ∈
    Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩)
  rw [← Finset.prod_div_distrib]
  exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩

theorem cst_mem_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (cc : (k : K) → J k), (∀ k, y ⟨k, cc k⟩ ≠ 0) → ∀ r : c.F, 𝔐.cst r ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 cc hcc r
  have hx : (∏ k, y ⟨k, cc k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hcc k
  have hint : ∀ a : 𝓞 c.F, 𝔐.cst (algebraMap (𝓞 c.F) c.F a) ∈
      Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := fun a =>
    segre_adjoin_le y cc ((𝔐.tie.ring cc hx _).2 fun p _ =>
      ringHom_mem_regAt 𝔐.ξ (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) (𝔐.f ≫ Y.s) 𝔐.cst_over p a)
  haveI : FiniteDimensional ℚ c.F := c.fin
  have halg : IsAlgebraic ℤ r := (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic r)
  obtain ⟨n, hn, hr⟩ := halg.exists_integral_multiple
  have hn' : (n : Ω) ≠ 0 := Int.cast_ne_zero.2 hn
  have e : 𝔐.cst r = algebraMap ℚ Ω (n : ℚ)⁻¹ *
      𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) (n • r) hr)) := by
    rw [IsIntegralClosure.algebraMap_mk', zsmul_eq_mul, map_mul, map_intCast]
    simp [hn']
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hint _)

end GlobalTheory.CompanionTheory.Ar.CstChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsValueOverPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constants_value_over_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p → ∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (κ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def PolarisedAt {X : Scheme.{0}} (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) : Prop :=
  ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

open Classical in

def gramFn (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) (w : (Σ k, J k) → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  if h : ∃ (Γ : Matrix (Fin r) (Fin r) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
      CoordsAt 𝔐.ξ y z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z b Γ then h.choose else 0

def recentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (ρ : ℂ)⁻¹ * (t (π.symm i) - t₀ (π.symm i))

def periodGram {n a₀ g r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (u : Fin n → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => Real.pi * (U j u ⬝ᵥ L.H u *ᵥ star (U i u))

def IsFramePeriods (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) {P : Ideal (MRing J)} {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω) {a₀ g : ℕ}
    {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) ∧ LinearIndependent ℂ (fun k => U k 0) ∧
  (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧
  ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧
    InFrameDomain y cc f (χ.γ (recentre t₀ ρ π u)) ∧ (χ.γ (recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) ∧
    (u ∈ Flat.punct n a₀ 1 → ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (χ.γ (recentre t₀ ρ π u)) →
      𝔐.M.GramAt 𝔐.t.PP.L z b (periodGram L U u))

theorem recentre_uncentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    recentre t₀ ρ π (uncentre t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [recentre, uncentre, h]

theorem isOpen_punct (n a : ℕ) (ρ : ℝ) : IsOpen (Flat.punct n a ρ) := by
  have : Flat.punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | i.val < a → z i ≠ 0} := by
    ext z; simp [Flat.punct]
  rw [this]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : i.val < a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

theorem contDiff_uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uncentre t₀ ρ π) := by
  unfold uncentre
  exact contDiff_pi.2 fun i => contDiff_const.mul ((contDiff_apply ℝ ℂ (π.symm i)).sub contDiff_const)

theorem uncentre_mem_ball {n : ℕ} {t₀ t : Fin n → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n))
    (h : ‖t - t₀‖ < ρ) : uncentre t₀ ρ π t ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖t (π.symm i) - t₀ (π.symm i)‖ ≤ ‖t - t₀‖ := norm_le_pi_norm (t - t₀) (π.symm i)
  simp only [uncentre, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  rw [inv_mul_lt_iff₀ hρ]
  linarith

theorem uncentre_self {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : uncentre t ρ π t = 0 := by
  funext i
  simp [uncentre]

theorem recentre_zero {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : recentre t ρ π 0 = t := by
  funext i
  simp [recentre]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsFiniteTypeOverIntegersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_finite_type_over_integers : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int <;> assumption)
end

