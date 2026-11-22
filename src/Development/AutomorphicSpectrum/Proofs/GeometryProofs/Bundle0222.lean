import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0219
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0213
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0217
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0218

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializationCoordRatioValueStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialization_coord_ratio_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (A : Subring Ω) (ev : A →+* 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → (∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x)) → ∀ (c : (k : K) → ι k), (∀ k, z ⟨k, c k⟩ ≠ 0) → (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, ev ⟨_, hr k i⟩ = z ⟨k, i⟩ / z ⟨k, c k⟩) ∧ ∀ a : A, ∃ b : A, ev b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DenValue.value_and_denominator | exact GlobalTheory.CompanionTheory.Ar.DenValue.value_and_denominator | (intros; apply GlobalTheory.CompanionTheory.Ar.DenValue.value_and_denominator <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLieModelLift
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonObj

theorem exists_val_of_isTan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (v : epsOver T.V T.V ⟶ G.G), IsTan v → ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  intro E _ _ _ H X tX T zV G Ψ hΨ EC _ _ MC v hv
  have hbase : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (epsOver T.V T.V).hom =
      Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [LieTangent.spec_comp, LieTangent.spec_comp]
    congr 2
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hover : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ) ≫ tX.G.hom =
      (epsAt (FinRd.Roots.gen T zV)).hom := by
    have hw : v.left ≫ G.G.hom = (epsOver T.V T.V).hom := Over.w v
    rw [Category.assoc, Category.assoc, hΨ.1.w, ← Category.assoc v.left, hw, ← Category.assoc, hbase,
      Category.assoc]
    rfl
  let vt : epsAt (FinRd.Roots.gen T zV) ⟶ tX.G := Over.homMk _ hover
  have ht : GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G (FinRd.Roots.gen T zV) vt := by
    have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
        (1 : ptOver T.V T.V ⟶ G.G).left := hv
    have h1 := FrameValue.one_left_grp hΨ (Spec.map (CommRingCat.ofHom (algebraMap T.V T.V))) _ rfl
    have hp : Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.V)) ≫ zV = FinRd.Roots.gen T zV := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    have h2 := FrameValue.one_left_pull (G := tX.G) (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) _ _ hp
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.Fr T.Fr T.Fr).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ = _
    rw [← Category.assoc, LieTangent.spec_fst_dual, Category.assoc, ← Category.assoc _ v.left Ψ, hv']
    exact (congrArg (fun u => Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ u) h1).trans h2
  obtain ⟨w, hw⟩ := MC.onto vt ht
  exact ⟨w, congrArg (fun u => u.left) hw⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TriangularSpanCoeffRatioStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_span_coeff_ratio : ∀ (V F EC : Type) [CommRing V] [Field F] [Algebra V F] [AddCommGroup EC] [Module F EC] [Module V EC] [IsScalarTower V F EC] (r : ℕ) (u v w : Fin r → EC) (a b : Fin r → F) (d : V), LinearIndependent F u → FinRd.Roots.TriIn u a v → FinRd.Roots.TriIn u b w → (∀ i, b i ≠ 0) → (∀ x ∈ Submodule.span V (Set.range v), d • x ∈ Submodule.span V (Set.range w)) → ∀ i, ∃ c : V, algebraMap V F d * a i = algebraMap V F c * b i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.diag_compare_of_triIn | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.diag_compare_of_triIn | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.diag_compare_of_triIn <;> assumption)
end

