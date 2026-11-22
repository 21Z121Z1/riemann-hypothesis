import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0238
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsArcFamilyPointWithFramesProofStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsArcFamilyPointWithFrames_proof : GlobalTheory.LN.ArcFamSt := by
  first | exact @GlobalTheory.arcFam_closed | exact GlobalTheory.arcFam_closed | (intros; apply GlobalTheory.arcFam_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelAmpleFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevel_model_ample_frames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → TopAmpExists := by
  first | exact @GlobalTheory.Models.topAmpExists | exact GlobalTheory.Models.topAmpExists | (intros; apply GlobalTheory.Models.topAmpExists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliNonemptyPositiveDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ModuliInhabitant

theorem half_finrank_pos (E : Type) [Field E] [NumberField E] [IsCMField E] :
    0 < Module.finrank ℚ E / 2 := by
  have h1 := IsTotallyComplex.finrank E
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

theorem exists_not_mem_of_discrete {g : ℕ} (hg : 0 < g) (Λ : AddSubgroup (Fin g → ℂ))
    [DiscreteTopology Λ] : ∃ z, z ∉ Λ := by
  by_contra hne
  push Not at hne
  have hc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun c : ℂ => (⟨fun _ => c, hne _⟩ : Λ)) := fun a b h =>
    congrFun (congrArg Subtype.val h) ⟨0, hg⟩
  have : Countable ℂ := hinj.countable
  exact not_countable_iff.2 (inferInstance : Uncountable ℝ) Complex.ofReal_injective.countable

theorem exists_unif_point (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (hr : 1 ≤ D.p + D.q) (l : Level H) :
    ∃ (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 0 < g ∧ IsTypeFn H D.p D.q ty ∧
      Nonempty (FamilyUnif Xo (KA l).val.toRingHom ty) ∧
      ∃ (y : Sp ℂ ⟶ Xo.X), y ≫ Xo.s = spMap (KA l).val.toRingHom ∧ ∃ x : Over.mk y ⟶ Xo.univ.t.G, x ≠ 1 := by
  obtain ⟨Xo⟩ := GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level E H D l hr
  obtain ⟨⟨g, ty, h⟩, h2, -⟩ := GlobalTheory.PeriodExists.typeFn_period_exist E H D
  have hg : 0 < g := by
    rw [(h2 g ty h).1]
    exact Nat.mul_pos (half_finrank_pos E) hr
  obtain ⟨U⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (KA l).val.toRingHom g ty hr rfl h
  let i : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨-, P, hP⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (U.Di i)).2.1 g ty
    (by rw [(U.sig i).1, (U.sig i).2]; exact h)
  haveI := hP.2.2.1
  obtain ⟨z, hz⟩ := exists_not_mem_of_discrete hg P.range
  exact ⟨Xo, g, ty, hg, h, ⟨U⟩, U.u i P, U.over_σ i P hP, U.ex i P z, fun hx => hz ((U.ex_ker i P hP z).1 hx)⟩

theorem moduli_inhabited : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ∀ l : Level H, ∃ (Xo : Moduli D l) (y : Sp ℂ ⟶ Xo.X), y ≫ Xo.s = spMap (KA l).val.toRingHom ∧ ∃ x : Over.mk y ⟶ Xo.univ.t.G, x ≠ 1) ∧ ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l), 0 < D.dim ∧ Nonempty Xo.X ∧ ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), 0 < g ∧ IsTypeFn H D.p D.q ty ∧ Nonempty (FamilyUnif Xo (KA l).val.toRingHom ty) := by
  refine ⟨fun E _ _ _ H D hr l => ?_, ?_⟩
  · obtain ⟨Xo, g, ty, -, -, -, y, hy⟩ := exists_unif_point E H D hr l
    exact ⟨Xo, y, hy⟩
  · obtain ⟨Xo, g, ty, hg, h, hU, y, -⟩ := exists_unif_point _ GlobalTheory.HostModel.host
      (GlobalTheory.HostModel.hypDatum GlobalTheory.HostModel.host) (by simp) (GlobalTheory.HostModel.level GlobalTheory.HostModel.host 1 one_pos)
    refine ⟨_, inferInstance, inferInstance, inferInstance, GlobalTheory.HostModel.host, _, _, Xo, ?_,
      ⟨y.base (IsLocalRing.closedPoint ℂ)⟩, g, ty, hg, h, hU⟩
    simpa [Datum.dim] using half_finrank_pos GlobalTheory.HostModel.E21

end GlobalTheory.ModuliInhabitant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientReducedBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_heckeQuotient_reducedBase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (C : Over S) (j : C ⟶ o.t.G), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsReduced S → IsFinite C.hom → Etale C.hom → IsClosedImmersion j.left → HeckeSet D o.t 𝔓 p i (Set.range j.left) → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ∧ ∃ (o' : Ob D l s) (_ : ObjMap o' Xo.univ f) (ψ : o.t.G ⟶ o'.t.G), IsIsog o o' p ψ ∧ IsPullback j (toUnit C) ψ η[o'.t.G] := by
  first | exact @GlobalTheory.HkFam.existsUnique_heckeQuot | exact GlobalTheory.HkFam.existsUnique_heckeQuot | (intros; apply GlobalTheory.HkFam.existsUnique_heckeQuot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeCorrespondenceSecondProjectionFiniteEtaleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCorrespondence_secondProjection_finite_etale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo 𝔓 p i), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsFinite Z.π₂ ∧ Etale Z.π₂ ∧ (i ≤ D.p + D.q → Surjective Z.π₂) := by
  first | exact @GlobalTheory.HkFam.second_projection_finite_etale | exact GlobalTheory.HkFam.second_projection_finite_etale | (intros; apply GlobalTheory.HkFam.second_projection_finite_etale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.moduliScheme_levelMaps_heckePoints : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1
  exact ⟨_root_.GlobalTheory.Moduli.moduli_scheme_exists, fun E _ _ _ H D hD =>
    ⟨_root_.GlobalTheory.levelMaps_closed _root_.GlobalTheory.abelianSchemeLaws_all.1 E H D hD,
      _root_.GlobalTheory.heckePoints_of_laws _root_.GlobalTheory.abelianSchemeLaws_all.1
        _root_.GlobalTheory.AbLaw.CubeAssembly.cube_gen E H D hD⟩⟩

end GlobalTheory
end

