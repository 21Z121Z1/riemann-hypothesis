import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0225
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0213
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0217
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointValuationRingLift
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0169
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0026

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelEigenFrameStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_map_lie_model_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → LinearIndependent F u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_map_lie_model_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (y' : FrPt Xo c F) (t : Ix Dw → Fˣ), FrBor t y y' → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u yb : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → (∀ i, (MC.pt (yb i)).left ≫ m.φ = Small.tanY Y y' τ (Fin.cast hr i)) → FinRd.Roots.TriIn u (fun i => (t (some ⟨τ, Fin.cast hr i⟩) : F)) yb := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.triIn_of_frBor | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.triIn_of_frBor | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.triIn_of_frBor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelAndHeckeOfZeroSignatureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_and_hecke_of_zero_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main | exact GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapLocallyQuasiFinite
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem locallyQuasiFinite_pow_semiAbelian :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N →
      LocallyQuasiFinite ((𝟙 G) ^ N).left := by
  intro S G _ hG N hN
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have hm : IsMonHom ((𝟙 G) ^ N) := GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have : LocallyOfFiniteType (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType ((𝟙 G) ^ N).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact ((𝟙 G) ^ N).left := QuasiCompact.of_comp _ G.hom
  refine GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker S G G _ hm inferInstance inferInstance
    fun Ω _ _ t => ?_
  simp only [MonObj.comp_pow, Category.comp_id]
  exact GlobalTheory.HomExt.finite_torsion_points hG t hN

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianGenericIsoExtends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.CommonModel

section Ext

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {A B : Over (Sp V)} [GrpObj A] [GrpObj B] {GK : Over (Sp K)} [GrpObj GK]

theorem hom_unique (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a) (g₁ g₂ : A ⟶ B) [IsMonHom g₁] [IsMonHom g₂]
    (h : a ≫ g₁.left = a ≫ g₂.left) : g₁ = g₂ := by
  obtain ⟨io, -, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  have hmap : (Over.pullback (spMap (algebraMap V K))).map g₂ =
      (Over.pullback (spMap (algebraMap V K))).map g₁ := by
    have L : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) =
          pullback.fst A.hom (spMap (algebraMap V K)) ≫ g.left := fun g => pullback.lift_fst _ _ _
    have R : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.snd B.hom (spMap (algebraMap V K)) =
          pullback.snd A.hom (spMap (algebraMap V K)) := fun g => pullback.lift_snd _ _ _
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [L, L, ← hio, Category.assoc, Category.assoc, h]
    · rw [R, R]
  obtain ⟨F, -, hu⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    ((Over.pullback (spMap (algebraMap V K))).map g₁) inferInstance
  exact (hu g₁ ⟨inferInstance, rfl⟩).trans (hu g₂ ⟨inferInstance, hmap⟩).symm

theorem hom_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ F : A ⟶ B, IsMonHom F ∧ a ≫ F.left = b := by
  obtain ⟨io, hiom, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  obtain ⟨ko, -, hko⟩ := grpPullback_iso ha (isGrpPullback_pullback A (spMap (algebraMap V K)))
  obtain ⟨ko', hko'm, hko'⟩ := grpPullback_iso hb (isGrpPullback_pullback B (spMap (algebraMap V K)))
  have := hiom
  have := hko'm
  obtain ⟨F, ⟨hFm, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    (io.hom ≫ ko'.hom) inferInstance
  have hkoio : ko.hom ≫ io.hom = 𝟙 _ := by
    apply Over.OverMorphism.ext
    apply ha.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hio, hko, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.id_left, Category.id_comp]
  refine ⟨F, hFm, ?_⟩
  rw [← hko, Category.assoc]
  have e : pullback.fst A.hom (spMap (algebraMap V K)) ≫ F.left =
      ((Over.pullback (spMap (algebraMap V K))).map F).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) :=
    (pullback.lift_fst _ _ _).symm
  rw [e, hF, ← Category.assoc, ← Over.comp_left, ← Category.assoc, hkoio, Category.id_comp, hko']

theorem iso_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ e : A ≅ B, IsMonHom e.hom ∧ a ≫ e.hom.left = b := by
  obtain ⟨F, hFm, hF⟩ := hom_exists V K hA hB ha hb
  obtain ⟨F', hF'm, hF'⟩ := hom_exists V K hB hA hb ha
  have := hFm
  have := hF'm
  have h₁ : F ≫ F' = 𝟙 _ := hom_unique V K hA hA ha _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF, hF', Over.id_left, Category.comp_id])
  have h₂ : F' ≫ F = 𝟙 _ := hom_unique V K hB hB hb _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF', hF, Over.id_left, Category.comp_id])
  exact ⟨⟨F, F', h₁, h₂⟩, hFm, hF⟩

end Ext

end GlobalTheory.CompanionTheory.Ar.CommonModel

namespace GlobalTheory.CompanionTheory.Ar

theorem semiAbelian_commonModel : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) (x : Sp V ⟶ X) (x' : Sp V ⟶ X') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left) (φ' : GK.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap V K) ≫ x) φ → IsGrpPullback GK G' (spMap (algebraMap V K) ≫ x') φ' → ∃ (G₀ : Over (Sp V)) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left) (ψ' : G₀.left ⟶ G'.left) (κ : GK.left ⟶ G₀.left), IsGrpPullback G₀ G x ψ ∧ IsGrpPullback G₀ G' x' ψ' ∧ IsGrpPullback GK G₀ (spMap (algebraMap V K)) κ ∧ κ ≫ ψ = φ ∧ κ ≫ ψ' = φ' := by
  intro V K _ _ _ _ _ _ X X' x x' G G' _ _ GK _ φ φ' hG hG' hφ hφ'
  have pA := isGrpPullback_pullback G x
  have pB := isGrpPullback_pullback G' x'
  have sA : IsSemiAbelian ((Over.pullback x).obj G) := IsSemiAbelian.pullback x G hG
  have sB : IsSemiAbelian ((Over.pullback x').obj G') := IsSemiAbelian.pullback x' G' hG'

  have lift : ∀ {Y : Scheme.{0}} (y : Sp V ⟶ Y) (H : Over Y) [GrpObj H] (θ : GK.left ⟶ H.left),
      IsGrpPullback GK H (spMap (algebraMap V K) ≫ y) θ →
      ∃ κ : GK.left ⟶ ((Over.pullback y).obj H).left,
        IsGrpPullback GK ((Over.pullback y).obj H) (spMap (algebraMap V K)) κ ∧
          κ ≫ pullback.fst H.hom y = θ := by
    intro Y y H _ θ hθ
    have hp := isGrpPullback_pullback H y
    have w : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ ((Over.pullback y).obj H).hom =
        GK.hom ≫ spMap (algebraMap V K) := hp.1.lift_snd _ _ _
    have f : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ pullback.fst H.hom y = θ := hp.1.lift_fst _ _ _
    exact ⟨_, hp.cancel (by rw [f]; exact hθ) w, f⟩
  obtain ⟨κ, hκ, hκφ⟩ := lift x G φ hφ
  obtain ⟨κ', hκ', hκφ'⟩ := lift x' G' φ' hφ'
  obtain ⟨e, hem, he⟩ := CommonModel.iso_exists V K sA sB hκ hκ'
  have := hem
  refine ⟨(Over.pullback x).obj G, inferInstance, pullback.fst G.hom x,
    e.hom.left ≫ pullback.fst G'.hom x', κ, pA, ?_, hκ, hκφ, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp pB).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, he, hκφ']

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointValuationRingLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_point_valuation_ring_lift : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (w : G.left), IsClosed ({w} : Set G.left) → ∃ (N : ℕ) (O : ValuationSubring (AlgebraicClosure L)) (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ G), 1 ≤ N ∧ y ^ N = 1 ∧ y.left (IsLocalRing.closedPoint O) = w ∧ ∀ a : 𝓞 L, ((ρ a : O) : AlgebraicClosure L) = algebraMap L (AlgebraicClosure L) (a : L) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.exists_torsion_point_reducing_to | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.exists_torsion_point_reducing_to | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.exists_torsion_point_reducing_to <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTwoTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.GenTors

theorem exists_finite_ext_torusExtension_two_torsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :=
  PositivityTheory.Xgn.stratum_generic_torsion_points

end GlobalTheory.CompanionTheory.Ar.GenTors
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionCardBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.RankBound

theorem rank_bound_of_points_of_order_two :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) :=
  @PositivityTheory.Xgn.two_torsion_rank_bound

end GlobalTheory.CompanionTheory.Ar.RankBound
end

