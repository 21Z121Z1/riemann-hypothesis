import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0280
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRight
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyPBOfKeyOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0170
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
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
import Development.AutomorphicSpectrum.Statements.GeometryStatements.GoodTwistGoodTwist

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorsQF

variable {X : Scheme.{0}} (G : Over X) [GrpObj G]

theorem pow_eq_one_of_res {A B : Scheme.{0}} (u : A ⟶ B) [Epi u] (ξ : B ⟶ X) (y : Over.mk ξ ⟶ G) (n : ℕ)
    (g : Over.mk (u ≫ ξ) ⟶ G) (hg : g.left = u ≫ y.left) (h : g ^ n = 1) : y ^ n = 1 := by
  let f : Over.mk (u ≫ ξ) ⟶ Over.mk ξ := Over.homMk u rfl
  have e : g = f ≫ y := by ext1; simpa [f] using hg
  have h1 : f ≫ y ^ n = f ≫ 1 := by rw [comp_pow, ← e, h, comp_one]
  ext1
  have h2 := congrArg (fun z => z.left) h1
  simp only [Over.comp_left] at h2
  exact (cancel_epi u).1 h2

theorem epi_spMap {K L : Type} [Field K] [Field L] (a : K →+* L) : Epi (spMap a) := by
  have : Flat (spMap a) := by
    rw [spMap, Flat.SpecMap_iff]
    letI := a.toAlgebra
    exact (RingHom.flat_algebraMap_iff (R := K) (S := L)).2 inferInstance
  have : Surjective (spMap a) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    exact ⟨z, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  exact Flat.epi_of_flat_of_surjective _

theorem torsion_qfGroup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (X : Scheme.{0})
    (G : Over X) [GrpObj G] (x : Sp R ⟶ X) (n : ℕ), IsSemiAbelian G → 0 < n →
    FullTorsion G (spMap (algebraMap R (FractionRing R)) ≫ x) n →
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T) (Q : BT.QFGroup R T) (i : Q.G.left ⟶ G.left),
      Q.IsTorsionAlong G x n i := by
  intro R _ _ _ _ X G _ x n hG hn hF
  have := hG.comm
  let ξ : Sp (FractionRing R) ⟶ X := spMap (algebraMap R (FractionRing R)) ≫ x
  let T : Subgroup (Over.mk ξ ⟶ G) := (powMonoidHom n).ker
  have hT : ∀ y : T, (y : Over.mk ξ ⟶ G) ^ n = 1 := fun y => MonoidHom.mem_ker.1 y.2
  have hfin : Finite T := by
    let L := AlgebraicClosure (FractionRing R)
    let a : FractionRing R →+* L := algebraMap (FractionRing R) L
    haveI := epi_spMap a
    let t : Sp L ⟶ X := spMap a ≫ ξ
    have h0 := GlobalTheory.finite_torsion_semiAbelian L ((Over.pullback t).obj G) (IsSemiAbelian.pullback t G hG) n hn
    have h1 : Finite {g : Over.mk t ⟶ G // g ^ n = 1} :=
      GlobalTheory.FewZeros.finite_torsion_of_mulEquiv
        (GlobalTheory.TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp L))) t (Category.id_comp t)) n h0
    let f : Over.mk t ⟶ Over.mk ξ := Over.homMk (spMap a) rfl
    let φ : T → {g : Over.mk t ⟶ G // g ^ n = 1} := fun y => ⟨f ≫ y.1, by rw [← comp_pow, hT y, comp_one]⟩
    refine Finite.of_injective φ fun y z e => ?_
    have e1 := congrArg (fun w => (w.1 : Over.mk t ⟶ G).left) e
    simp only [φ, f, Over.comp_left, Over.homMk_left] at e1
    exact Subtype.ext (Over.OverMorphism.ext ((cancel_epi (spMap a)).1 e1))
  obtain ⟨Γ, i, h, -⟩ := GlobalTheory.T.torsion_embedding_geometric_points R T X G hG x n hn T.subtype Subtype.val_injective hT
    (fun Ω _ _ a g hg => by
      obtain ⟨y, hy⟩ := hF Ω a g hg
      haveI := epi_spMap a
      exact ⟨⟨y, MonoidHom.mem_ker.2 (pow_eq_one_of_res G (spMap a) ξ y n g hy hg)⟩, hy⟩)
  exact ⟨T, inferInstance, hfin, Γ, i, h⟩

end GlobalTheory.CompanionTheory.Ar.TorsQF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteMapEqOfThickeningsEqStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_map_eq_of_thickenings_eq : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f g : X ⟶ Y), (∀ e, (Over.pullback (thick R I e)).map f = (Over.pullback (thick R I e)).map g) → f = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions | exact GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfClosedSubgroupStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_of_closed_subgroup : ∀ (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommGroup H] (Γf : QFGroup R H) (A E : Over (Spec (CommRingCat.of R))) (a : A ⟶ Γf.G) (b : Γf.G ⟶ E) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ E), IsClosedImmersion a.left → IsPullback a (toUnit A) b e → ∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.RatKer.exists_section_of_generic | exact GlobalTheory.CompanionTheory.Ar.BT.RatKer.exists_section_of_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.RatKer.exists_section_of_generic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfTorsionKernelStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_of_torsion_kernel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsSemiAbelian B → ∀ (N : ℕ), 1 ≤ N → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] [IsCommMonObj A] (j : A ⟶ B) [IsMonHom j], IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] → (∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g) → ∃ (C : Type) (_ : CommGroup C) (Γ : QFGroup R C) (φ : Γ.G ≅ A), IsMonHom φ.hom ∧ Γ.IsTorsionAlong B (𝟙 _) N (φ.hom.left ≫ j.left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_kernel | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_kernel | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_kernel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hol_unif_period_matrix_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → (∀ y ∈ e.per b, ℓ y ∈ u.Λ) ∧ ∀ p ∈ u.Λ, ∃ y ∈ e.per b, ℓ y = p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyInputFromPpData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]

def epsIso (R : Type) [CommRing R] : epsR R ≅ epsAt (𝟙 (Sp R)) :=
  Over.isoMk (Iso.refl _) (by simp [spMap])

def tanVec (M : LieModel G (𝟙 (Sp R)) E) (x : E) : epsR R ⟶ G := (epsIso R).hom ≫ M.pt x

theorem tanVec_left (M : LieModel G (𝟙 (Sp R)) E) (x : E) : (tanVec M x).left = (M.pt x).left := by
  simp [tanVec, epsIso]

theorem one_left : (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left = η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  have h : (toUnit (Over.mk (𝟙 (Sp R)))).left = 𝟙 _ := by
    have := Over.w (toUnit (Over.mk (𝟙 (Sp R))))
    simpa using this
  rw [h]
  exact Category.id_comp _

theorem isTangent_tanVec (M : LieModel G (𝟙 (Sp R)) E) (x : E) : IsTangent (tanVec M x) := by
  have h := M.tan x
  unfold IsTangent
  rw [tanVec_left]
  exact h.trans one_left

theorem exists_tanVec (M : LieModel G (𝟙 (Sp R)) E) (w : epsR R ⟶ G) (hw : IsTangent w) : ∃ x, tanVec M x = w := by
  obtain ⟨x, hx⟩ := M.onto ((epsIso R).inv ≫ w) (by
    unfold IsTanAt
    have e : ((epsIso R).inv ≫ w).left = w.left := by simp [epsIso]
    rw [e]
    exact Eq.trans hw one_left.symm)
  exact ⟨x, by rw [tanVec, hx]; simp⟩

theorem tanVec_injective (M : LieModel G (𝟙 (Sp R)) E) : Function.Injective (tanVec M) := fun a b h =>
  M.inj (Over.OverMorphism.ext (by rw [← tanVec_left, ← tanVec_left, h]))

theorem prod_ofFn_tanVec (M : LieModel G (𝟙 (Sp R)) E) :
    ∀ {n : ℕ} (f : Fin n → E), (List.ofFn fun j => tanVec M (f j)).prod = tanVec M (∑ j, f j)
  | 0, f => by simp [tanVec, M.pt_zero]
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_tanVec M, Fin.sum_univ_succ]
    simp only [tanVec, M.add, MonObj.comp_mul]

theorem isLieComb_tanVec_iff (M : LieModel G (𝟙 (Sp R)) E) {n : ℕ} (b : Fin n → E) (c : Fin n → R) (x : E) :
    IsLieComb c (fun i => tanVec M (b i)) (tanVec M x) ↔ x = ∑ i, c i • b i := by
  have hs : ∀ i, (tanVec M (c i • b i)).left = spMap (epsScaleR (c i)) ≫ (tanVec M (b i)).left := fun i => by
    rw [tanVec_left, tanVec_left, M.smul]
    rfl
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun i => tanVec M (c i • b i) := funext fun i =>
      Over.OverMorphism.ext ((hu i).trans (hs i).symm)
    rw [hu', prod_ofFn_tanVec M] at hw
    exact tanVec_injective M hw
  · rintro rfl
    exact ⟨fun i => tanVec M (c i • b i), hs, (prod_ofFn_tanVec M _).symm⟩

theorem isLieBasis_tanVec (M : LieModel G (𝟙 (Sp R)) E) {n : ℕ} (b : Fin n → E) (hli : LinearIndependent R b)
    (hsp : Submodule.span R (Set.range b) = ⊤) : IsLieBasis (fun i => tanVec M (b i)) := by
  refine ⟨fun i => isTangent_tanVec M _, fun w hw => ?_⟩
  obtain ⟨x, rfl⟩ := exists_tanVec M w hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hsp ▸ Submodule.mem_top : x ∈ Submodule.span R (Set.range b))
  refine ⟨c, (isLieComb_tanVec_iff M b c x).2 hc.symm, fun c' h => ?_⟩
  have h' := (isLieComb_tanVec_iff M b c' x).1 h
  have h0 : ∑ i, (c' i - c i) • b i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h', hc, sub_self]
  funext i
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 i)

end Lie

section Sec

variable {X : Scheme.{0}}

theorem mem_basicOpen_map {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : X) :
    y ∈ X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) ↔ y ∈ V ∧ y ∈ X.basicOpen f := by
  have e : X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
    Scheme.basicOpen_res X f (homOfLE h).op
  rw [e]
  rfl

theorem sameSec_ofPow {L : LB X} (s : Out.H0 L 1) : KeyDeg.SameSec s (GlobalTheory.GeneratorFrame.ofPow s) := fun _ => rfl

theorem nonzeroLocus_ofPow {L : LB X} (s : Out.H0 L 1) {y : X} (hy : y ∈ Out.nonzeroLocus s) :
    y ∈ Out.nonzeroLocus (GlobalTheory.GeneratorFrame.ofPow s) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨i, rfl⟩ : ∃ i, k = fun _ => i := ⟨k 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  have hU : y ∈ L.U i := GlobalTheory.GeneratorFrame.wchart_le' L (fun _ => i) (X.basicOpen_le _ hk)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (mem_basicOpen_map _ _ y).2 ⟨hU, hk⟩⟩

end Sec

section Main

theorem dualMapR_eq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Chart.dualMapR f = dualMap f := by
  ext a <;> simp [Chart.dualMapR, dualMap]

theorem mem_basicOpen_appLE {X Y : Scheme.{0}} (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (f : Γ(X, U))
    {z : Y} (hz : z ∈ V) (hy : φ z ∈ X.basicOpen f) : z ∈ Y.basicOpen ((φ.appLE U V h).hom f) := by
  have e : (φ.appLE U V h).hom f = (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom f) := rfl
  rw [e]
  refine (mem_basicOpen_map h _ z).2 ⟨hz, ?_⟩
  rw [← Scheme.preimage_basicOpen]
  exact hy

theorem exists_keyIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∀ (s : Out.H0 D.t.PP.L 1) (e : Fin D.g → D.B.carrier), KeyDeg.NonVan D.t.G.hom s → LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → ∃ (x : KeyIn L) (th : D.t.PP.L.Sec) (hg : x.P.g = D.g) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ D.t.G)), KeyDeg.SameSec s th ∧ KeyDeg.NonVan D.t.G.hom th ∧ KeyOver (algebraMap (𝓞 L) L) D.t th x v ∧ IsLieBasis v ∧ ∀ i, (v i).left = (D.MB.pt (e (i.cast hg))).left := by
  intro E _ _ _ H L _ _ D hg s e hs hli hsp
  have sm := D.tK.semi.smooth
  have gc := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.tK.G.hom) (𝟙 _) (𝟙 _) D.tK.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have hnv : KeyDeg.NonVan D.t.G.hom (GlobalTheory.GeneratorFrame.ofPow s) := fun b => by
    obtain ⟨y, hy, hy'⟩ := hs b
    exact ⟨y, hy, nonzeroLocus_ofPow s hy'⟩
  have hv := isLieBasis_tanVec D.MB e hli hsp
  obtain ⟨v', hv', hφ⟩ := GlobalTheory.exists_isLieBasis_baseChange (𝓞 L) L (algebraMap (𝓞 L) L) D.t.G D.tK.G D.m.φ D.m.cart
    D.t.semi.smooth D.g _ hv
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected D.tK.G.hom (eSec D.tK.G (default : PrimeSpectrum L))
  obtain ⟨u, hu⟩ := GlobalTheory.CM.TenDim.exists_isLieBasis D.tK.G hd
  have hdg : d = D.g := GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis D.m.cart hu hv'
  rw [hdg] at hd
  obtain ⟨hp, ha, hk⟩ := D.princ
  obtain ⟨w, hw, hr, -⟩ := D.m.lin
  have hw' := (isGen_iff w).1 hw
  obtain ⟨xth, hx⟩ := sec_pull_down hw' D.t.PP.isLB D.tK.PP.isLB (GlobalTheory.GeneratorFrame.ofPow s)
  have hcompat : ∀ (j : (D.t.PP.L.pull D.m.φ).ι) (i : D.tK.PP.L.ι)
      (h : (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i ≤ D.m.φ ⁻¹ᵁ D.t.PP.L.U (j PUnit.unit)),
      (D.m.φ.appLE _ _ h).hom ((GlobalTheory.GeneratorFrame.ofPow s).f (j PUnit.unit)) =
        (show Γ(D.tK.G.left, (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (xth.f i) := fun j i h => fn_ext fun y hy =>
    (gs_appLE D.m.φ _ _ h (𝟙 _) y hy _).trans ((hx _ (𝟙 _) y _ i (h hy) hy.2).trans
      (Eq.symm ((gs_mul (𝟙 _) y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res (𝟙 _) y _ hy _)))))
  have hne : ∀ s₀ : Sp L, ∃ z : D.tK.G.left, D.tK.G.hom z = s₀ ∧ z ∈ Out.nonzeroLocus xth := fun s₀ => by
    obtain ⟨y, hy, hyn⟩ := hnv (spMap (algebraMap (𝓞 L) L) s₀)
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback D.m.cart.1 y s₀ hy
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hyn
    obtain ⟨i, hi⟩ := exists_chart D.tK.PP.isLB z
    have hU : D.m.φ z ∈ D.t.PP.L.U l := Scheme.basicOpen_le _ _ hl
    let j : PUnit → D.t.PP.L.ι := fun _ => l
    have hV : z ∈ (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i := ⟨mem_pull.2 hU, hi⟩
    have hle : (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i ≤ D.m.φ ⁻¹ᵁ D.t.PP.L.U l := fun _ hy => mem_pull.1 hy.1
    have h1 := mem_basicOpen_appLE D.m.φ hle _ hV hl
    have e := hcompat j i hle
    refine ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩⟩
    change z ∈ D.tK.G.left.basicOpen ((D.m.φ.appLE _ _ hle).hom _) at h1
    rw [e, Scheme.basicOpen_mul] at h1
    exact ((mem_basicOpen_map _ _ z).1 h1.2).2
  obtain ⟨-, ws, gs', -⟩ := D.tK.sym
  refine ⟨KeyBadModel.keyInOf D.tK xth D.g hg v' hv' ⟨inferInstance, sm, hp, gc⟩ hd
    (fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩) ha hk hne, GlobalTheory.GeneratorFrame.ofPow s, rfl,
    fun i => tanVec D.MB (e i), sameSec_ofPow s, hnv, ?_, hv, fun i => tanVec_left _ _⟩
  have he : eSec D.tK.G ≫ D.m.φ = spMap (algebraMap (𝓞 L) L) ≫ eSec D.t.G := by
    have := D.m.cm.e_comm
    rwa [D.m.base] at this
  have hrig : ∀ (e' : (𝟙_ (Over (Sp L))).left ⟶ (𝟙_ (Over (Sp (𝓞 L)))).left) (he' : eSec D.tK.G ≫ D.m.φ = e' ≫ eSec D.t.G),
      e' = D.m.cm.e → rigPullOf D.m.φ e' he' D.t.PP.L D.t.PP.rig = D.m.cm.rigPull D.t.PP.L D.t.PP.rig := by
    rintro _ _ rfl
    rfl
  refine ⟨D.m.φ, he, w, D.m.cart, hw, ?_, hcompat, fun i => ?_⟩
  · have h2 : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D.tK.G) (fun _ => 1)) D.tK.PP.rig
        (rigPullOf D.m.φ (spMap (algebraMap (𝓞 L) L)) he D.t.PP.L D.t.PP.rig) := by
      rw [hrig _ he D.m.base.symm]
      exact hr
    exact h2
  · exact (hφ i).trans (by rw [dualMapR_eq])

end Main

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelLawsSectionVolumeBound
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.BergDual

theorem re_twist (g : ℂ →+* ℂ) (hg : g = RingHom.id ℂ ∨ g = starRingEnd ℂ) {n : ℕ} (b : Fin n → ℂ)
    (M : Fin n → Fin n → ℂ) :
    (∑ j, ∑ j', g (b j) * starRingEnd ℂ (g (b j')) * g (M j j')).re =
      (∑ j, ∑ j', b j * starRingEnd ℂ (b j') * M j j').re := by
  rcases hg with rfl | rfl
  · simp
  · have e : (∑ j, ∑ j', starRingEnd ℂ (b j) * starRingEnd ℂ (starRingEnd ℂ (b j')) * starRingEnd ℂ (M j j')) =
        starRingEnd ℂ (∑ j, ∑ j', b j * starRingEnd ℂ (b j') * M j j') := by
      simp only [map_sum, map_mul]
    rw [e, Complex.conj_re]

theorem sqrt_le_of_bounds {t N A pn hh lf : ℝ} (hN : 0 < N) (h1 : t * N ≤ (A * pn) ^ 2)
    (h2 : A ^ 2 ≤ lf ^ 2 * N * hh ^ 2) (hlf : 0 < lf) (hpn : 0 < pn) (hh0 : 0 < hh) :
    Real.sqrt t ≤ lf * pn * hh := by
  rw [Real.sqrt_le_left (by positivity)]
  have h3 : t * N ≤ (lf * pn * hh) ^ 2 * N := by
    calc t * N ≤ (A * pn) ^ 2 := h1
      _ = A ^ 2 * pn ^ 2 := by ring
      _ ≤ (lf ^ 2 * N * hh ^ 2) * pn ^ 2 := by gcongr
      _ = (lf * pn * hh) ^ 2 * N := by ring
  exact le_of_mul_le_mul_right h3 hN

theorem goodOf_goodOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c (goodOf c σ) = goodOf c σ := by
  exact if_pos (goodEmb_goodOf c σ)

theorem goodTwist_cases {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) :
    Small.goodTwist c σ = RingHom.id ℂ ∨ Small.goodTwist c σ = starRingEnd ℂ := by
  unfold Small.goodTwist
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

end GlobalTheory.CompanionTheory.Ar.Rec.BergDual

open GlobalTheory.CompanionTheory.Ar.Rec.BergDual in

theorem GlobalTheory.CompanionTheory.Ar.Rec.berg_dual : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r), CompLaws U h e → abelian₂.LevelLaws U W dict → FinVol W → ∀ (a₁ : WZ D.host.E) (Z : Comp Xo c) (n : ℕ) (ω : Fin n → Rul Xo c) (I : Type) [Fintype I] (L : HermLine (fun _ : Unit => I)) (ei : I ≃ Fin n), OntoZ U h e a₁ Z → Submodule.span c.F (Set.range ω) = cuspOn U h a₁ Z → ∀ (σ : c.F →+* ℂ) (k : (U (goodOf c σ)).Comp) (y : Frame ((U (goodOf c σ)).X k).Ψ D.R.r) (lin : Rul Xo c →ₛₗ[σ] ℂ), (∀ f, lin f = Small.goodTwist c σ (rdU (U (goodOf c σ)) f k y)) → (∀ as : Fin n → ℂ, ‖∑ j, as j * lin (ω j)‖ ^ 2 ≤ (∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipOn U W dict (xiR D) a₁ (e Z) σ (ω j) (ω j')).re * L.h (fun x => lin (ω (ei x.2))) ^ 2) → Over (U (goodOf c σ)) (e Z) k → y ∈ ((U (goodOf c σ)).X k).dom → ∀ (x0 : Frame ((U (goodOf c σ)).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U (goodOf c σ)).X k)))) (t : ℝ), IsOrth ((U (goodOf c σ)).X k) x0 → IsFundSet ((U (goodOf c σ)).X k) x0 FF → 0 < t → ThA.BergLB ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) y t → (∃ j, lin (ω j) ≠ 0) ∧ 0 < ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y ∧ Real.sqrt t ≤ lieFacZ Dw (xiR D) a₁ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y * L.h (fun x => lin (ω (ei x.2))) := by
  intro D H Dw l Xo c U h e W dict hL hLev hV a₁ Z n ω I _ L ei hOn hsp σ k y lin hlin hmet hOver hy x0 FF t hO hF ht hB
  have hg := goodEmb_goodOf c σ
  obtain ⟨P, hP, hN, hPy⟩ := hB
  obtain ⟨-, -, hTie⟩ := GlobalTheory.T.level_laws_frame_dictionary D H Dw l Xo c U h e W dict hL hLev hV (goodOf c σ) hg Z k hOver a₁ x0 FF hO hF
  obtain ⟨m, as, fs, hfs, hPeq⟩ := hOn (goodOf c σ) hg k hOver P hP
  have hω : ∀ j, ω j ∈ cuspOn U h a₁ Z := fun j => hsp ▸ Submodule.subset_span ⟨j, rfl⟩
  have hb : ∀ i, ∃ b : Fin n → c.F, ∑ j, b j • ω j = fs i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun c.F).1 (hsp ▸ hfs i)
  choose b hb using hb
  obtain ⟨as', has'⟩ : ∃ as' : Fin n → ℂ, as' = fun j => ∑ i, as i * goodOf c σ (b i j) := ⟨_, rfl⟩
  have hQ : ∀ x ∈ ((U (goodOf c σ)).X k).dom, P x = ∑ j, as' j * rdU (U (goodOf c σ)) (ω j) k x := by
    intro x hx
    rw [hPeq x hx]
    have e1 : ∀ i, rdU (U (goodOf c σ)) (fs i) k x = ∑ j, goodOf c σ (b i j) * rdU (U (goodOf c σ)) (ω j) k x := by
      intro i
      rw [← hb i, map_sum]
      simp [Finset.sum_apply, map_smulₛₗ]
    simp only [e1, has', Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hnrm : ThA.nrm2 ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) P =
      ThA.nrm2 ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k)
        (fun y => ∑ j, as' j * rdU (U (goodOf c σ)) (ω j) k y) := by
    unfold ThA.nrm2
    congr 1
    refine setIntegral_congr_fun hF.1 fun z hz => ?_
    simp only [Data.pnorm]
    rw [hQ _ (hF.2.1 hz)]
  have hT := hTie n as' ω hω
  rw [← hnrm] at hT
  have hm := hmet (fun j => Small.goodTwist c σ (as' j))
  have hip : ∀ f g, ipOn U W dict (xiR D) a₁ (e Z) σ f g =
      Small.goodTwist c σ (ipOn U W dict (xiR D) a₁ (e Z) (goodOf c σ) f g) := by
    intro f g
    unfold ipOn
    simp only [goodOf_goodOf, if_pos hg]
    unfold Small.goodTwist
    split_ifs <;> rfl
  have hsum : ∑ j, Small.goodTwist c σ (as' j) * lin (ω j) =
      Small.goodTwist c σ (P y) := by
    rw [hQ y hy, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlin, map_mul]
  have hre : (∑ j, ∑ j', Small.goodTwist c σ (as' j) * starRingEnd ℂ (Small.goodTwist c σ (as' j')) *
      ipOn U W dict (xiR D) a₁ (e Z) σ (ω j) (ω j')).re = lieFacZ Dw (xiR D) a₁ ^ 2 *
        ThA.nrm2 ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) P := by
    simp only [hip]
    rw [re_twist _ (goodTwist_cases c σ), hT]
  rw [hsum, Small.norm_goodTwist, hre] at hm
  have hpn : ∀ Q : Frame ((U (goodOf c σ)).X k).Ψ D.R.r → ℂ,
      ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) Q y =
        ‖Q y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y := by
    intro Q
    simp [Data.pnorm]
  rw [hpn P] at hPy
  have hpos : 0 < (‖P y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y) ^ 2 :=
    lt_of_lt_of_le (mul_pos ht hN) hPy
  have hne : ‖P y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hPy0 : P y ≠ 0 := fun h0 => hne (by simp [h0])
  have hpn0 : 0 < ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y := by
    have h1 : 0 ≤ ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y := by
      unfold Data.pnorm
      positivity
    exact lt_of_le_of_ne h1 fun h0 => hne (by rw [← h0, mul_zero])
  obtain ⟨j, hj⟩ : ∃ j, lin (ω j) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : Small.goodTwist c σ (P y) = 0 := by
      rw [← hsum]
      simp [hc]
    exact hPy0 ((map_eq_zero _).1 h0)
  have hh0 : 0 < L.h (fun x => lin (ω (ei x.2))) :=
    L.pos _ fun _ => ⟨ei.symm j, by simpa using hj⟩
  refine ⟨⟨j, hj⟩, hpn0, ?_⟩
  exact sqrt_le_of_bounds hN hPy hm (Real.exp_pos _) hpn0 hh0
end

