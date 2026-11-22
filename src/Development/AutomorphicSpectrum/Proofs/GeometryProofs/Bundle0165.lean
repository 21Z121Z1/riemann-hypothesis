import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0161
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0003
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSigma

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (φ : R →+* R') :
    (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap φ)
      = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem dualMap_comp_epsMul (φ : R →+* R') (a : R) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]

theorem comp_one_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  exact comp_one u

theorem comp_mul_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (p q : X ⟶ M) :
    u ≫ (p * q) = (u ≫ p) * (u ≫ q) := by
  exact comp_mul u p q

def pullEps (φ : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap φ)) (by
    simp only [Over.mk_hom, epsAt]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_algebraMap])

def pullPt (φ : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap φ ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap φ) rfl

theorem isTanAt_pull (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap φ ≫ x) (pullEps φ x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [← comp_one_over (pullPt φ x), Over.comp_left, Over.comp_left, ← hv]
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫ spMap (dualMap φ)
      = spMap φ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_comp_dualMap]
  simp only [pullEps, pullPt, Over.homMk_left]
  rw [reassoc_of% key]

theorem exists_linear (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S)
    {E E₀ : Type} [AddCommGroup E] [Module R E] [AddCommGroup E₀] [Module R' E₀] [Module R E₀]
    (hs : ∀ (a : R) (e : E₀), a • e = φ a • e) (M : LieModel G x E)
    (M₀ : LieModel G (spMap φ ≫ x) E₀) :
    ∃ j : E →ₗ[R] E₀, ∀ e, M₀.pt (j e) = pullEps φ x ≫ M.pt e := by
  choose j hj using fun e => M₀.onto _ (isTanAt_pull G φ x (M.pt e) (M.tan e))
  refine ⟨{ toFun := j, map_add' := ?_, map_smul' := ?_ }, hj⟩
  · intro e e'
    apply M₀.inj
    rw [M₀.add, hj, hj, hj, M.add, comp_mul_over]
  · intro c e
    apply M₀.inj
    rw [RingHom.id_apply, hs, hj]
    apply Over.OverMorphism.ext
    rw [M₀.smul, hj, Over.comp_left, Over.comp_left, M.smul]
    simp only [pullEps, Over.homMk_left, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, dualMap_comp_epsMul]

def transport {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (f : E' ≃ₗ[R] E) : LieModel G x E' where
  pt e := M.pt (f e)
  tan e := M.tan _
  inj := M.inj.comp f.injective
  onto v hv := by
    obtain ⟨e, he⟩ := M.onto v hv
    exact ⟨f.symm e, by simpa using he⟩
  add e e' := by simp only [map_add]; exact M.add _ _
  smul c e := by simp only [map_smul]; exact M.smul _ _

open GroundTheory.Heights₂.Heights in

theorem lieModel_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ S) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G z V) (σ : L →+* ℂ), ∃ Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V), ∀ e : V, M.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) e (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)) := by
  intro S G _ _ _ L _ _ z V _ _ M σ
  classical
  let _ : Algebra (𝓞 L) ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAlgebra
  obtain ⟨E₀, i1, i2, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists S G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
  let _ : Module (𝓞 L) E₀ := Module.compHom E₀ (σ.comp (algebraMap (𝓞 L) L))
  have _ : IsScalarTower (𝓞 L) ℂ E₀ := ⟨fun a b e => by
    show ((σ.comp (algebraMap (𝓞 L) L)) a * b) • e = (σ.comp (algebraMap (𝓞 L) L)) a • b • e
    rw [mul_smul]⟩
  obtain ⟨j, hj⟩ := exists_linear G (σ.comp (algebraMap (𝓞 L) L)) z (fun a e => rfl) M M₀
  have hl : ∀ e, M.Lifts (algebraMap (𝓞 L) ℂ) (𝟙 G.left) e (M₀.pt (j e)) := by
    intro e
    unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
    rw [hj e, Over.comp_left, Category.comp_id]
    rfl
  have hb := GlobalTheory.T.lie_model_isBaseChange S G (𝓞 L) ℂ z V E₀ M M₀ j hl
  let f : GroundTheory.Heights₂.Heights.Fibre σ V ≃ₗ[ℂ] E₀ := hb.equiv
  refine ⟨transport M₀ f, fun e => ?_⟩
  have hf : f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e) = j e := by
    show hb.equiv ((1 : ℂ) ⊗ₜ[𝓞 L] e) = j e
    rw [IsBaseChange.equiv_tmul, one_smul]
  unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
  show (M₀.pt (f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).left ≫ 𝟙 _ = _
  rw [hf, hj e, Over.comp_left, Category.comp_id]
  rfl

end GlobalTheory.CompanionTheory.Ar.LieSigma
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelRankEqGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.LieRank

variable {S : Scheme.{0}}

theorem dualMap_apply {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (a : DualNumber R) :
    dualMap c a = TrivSqZeroExt.inl (c a.fst) + TrivSqZeroExt.inr (c a.snd) := rfl

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, map_zero, TrivSqZeroExt.inr_zero, add_zero]

theorem fst_comp_dualMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  change (dualMap c a).fst = c a.fst
  simp [dualMap_apply]

theorem dualMap_comp_epsMul {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => ?_
  change dualMap c (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R)) a) =
    TrivSqZeroExt.map (c r • (LinearMap.id : R' →ₗ[R'] R')) (dualMap c a)
  ext <;> simp [dualMap_apply, mul_comm]

def epsPull {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) :
    epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_algebraMap c))

theorem one_left_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) :
    (1 : Over.mk (spMap c ≫ x) ⟶ G).left = spMap c ≫ (1 : Over.mk x ⟶ G).left := by
  have h := MonObj.comp_one (Over.homMk (spMap c) rfl : Over.mk (spMap c ≫ x) ⟶ Over.mk x) (M := G)
  exact (congrArg (fun k => k.left) h).symm

theorem isTanAt_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G (spMap c ≫ x) (epsPull c x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [one_left_pull, ← hv]
  change _ ≫ spMap (dualMap c) ≫ v.left = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (by
    refine RingHom.ext fun a => ?_
    exact (RingHom.congr_fun (fst_comp_dualMap c) a))

theorem epsPull_comp_left (G : Over S) {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) : (epsPull c x ≫ v).left = spMap (dualMap c) ≫ v.left := by
  simp [epsPull]

theorem exists_lift (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (x : Sp R ⟶ S) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] [Module R E']
    [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ j : E →ₗ[R] E', ∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (j e)) := by
  have hex : ∀ e, ∃ e', M'.pt e' = epsPull (algebraMap R R') x ≫ M.pt e := fun e =>
    M'.onto _ (isTanAt_pull G _ x _ (M.tan e))
  choose f hf using hex
  have hadd : ∀ a b, f (a + b) = f a + f b := fun a b => by
    apply M'.inj
    rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) a, f (r • a) = r • f a := fun r a => by
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [← algebraMap_smul R' r (f a), M'.smul, hf, hf, epsPull_comp_left, epsPull_comp_left, M.smul,
      ← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_epsMul (algebraMap R R') r)
  have hl : ∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (f e)) := fun e => by
    unfold LieModel.Lifts
    rw [hf, Category.comp_id, epsPull_comp_left]
  exact ⟨⟨⟨f, hadd⟩, hsmul⟩, hl⟩

theorem finrank_of_isBaseChange {A F : Type} [CommRing A] [Field F] [Algebra A F] {E E' : Type} [AddCommGroup E]
    [Module A E] [AddCommGroup E'] [Module F E'] [Module A E'] [IsScalarTower A F E'] [Module.Finite A E]
    [Module.Projective A E] (j : E →ₗ[A] E') (hj : IsBaseChange F j) (p : PrimeSpectrum F) :
    Module.finrank F E' = Module.rankAtStalk E (PrimeSpectrum.comap (algebraMap A F) p) := by
  rw [← Module.rankAtStalk_baseChange (S := F) (M := E) p]
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact (LinearEquiv.finrank_eq hj.equiv).symm

theorem finrank_eq_of_isBaseChange_fractionRing {D L : Type} [CommRing D] [IsDomain D] [Field L] [Algebra D L]
    [IsFractionRing D L] {E E' : Type} [AddCommGroup E] [Module D E] [AddCommGroup E'] [Module L E'] [Module D E']
    [IsScalarTower D L E'] (j : E →ₗ[D] E') (hj : IsBaseChange L j) :
    Module.finrank D E = Module.finrank L E' := by
  have : IsLocalizedModule (nonZeroDivisors D) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors D) L j).2 hj
  have h1 := IsLocalizedModule.rank_eq (nonZeroDivisors D) le_rfl j
  have h2 := IsLocalization.rank_eq L (N := E') (nonZeroDivisors D) le_rfl
  simp only [Module.finrank, h1, h2]

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar.LieRank

theorem exists_factor {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) [IsOpenImmersion i₀]
    (y : Sp F ⟶ X) (h : genPt y ∈ Set.range i₀) : ∃ φ : A →+* F, spMap φ ≫ i₀ = y := by
  have hr : Set.range y ⊆ Set.range i₀ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    rw [hp]
    exact h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom, ?_⟩
  have e : spMap (Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom = IsOpenImmersion.lift i₀ y hr :=
    Spec.map_preimage _
  rw [e]
  exact IsOpenImmersion.lift_fac i₀ y hr

theorem genPt_comp {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) (φ : A →+* F) :
    genPt (spMap φ ≫ i₀) = i₀ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := rfl

theorem finrank_fieldPt {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] {A F : Type} [CommRing A] [Field F]
    (i₀ : Sp A ⟶ S) {E Li : Type} [AddCommGroup E] [Module A E] [AddCommGroup Li] [Module F Li]
    (MA : LieModel G i₀ E) (φ : A →+* F) (M : LieModel G (spMap φ ≫ i₀) Li) :
    Module.finrank F Li = Module.rankAtStalk E (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := by
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective S G A i₀ E MA
  letI : Algebra A F := φ.toAlgebra
  letI : Module A Li := Module.compHom Li φ
  haveI : IsScalarTower A F Li := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := exists_lift G i₀ MA M
  exact finrank_of_isBaseChange j (GlobalTheory.T.lie_model_isBaseChange S G A F i₀ E Li MA M j hj) _

theorem finrank_eq_of_specializes {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (y₁ : Sp F₁ ⟶ X) (y₂ : Sp F₂ ⟶ X) (h : genPt y₁ ⤳ genPt y₂)
    {E₁ E₂ : Type} [AddCommGroup E₁] [Module F₁ E₁] [AddCommGroup E₂] [Module F₂ E₂]
    (M₁ : LieModel G y₁ E₁) (M₂ : LieModel G y₂ E₂) :
    Module.finrank F₁ E₁ = Module.finrank F₂ E₂ := by
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genPt y₂) (U := ⊤) trivial
  have h₁U : genPt y₁ ∈ U := h.mem_open U.isOpen hqU
  have hr : Set.range hU.fromSpec = (U : Set X) := hU.range_fromSpec
  obtain ⟨φ₁, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₁ (by rw [hr]; exact h₁U)
  obtain ⟨φ₂, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₂ (by rw [hr]; exact hqU)
  obtain ⟨E, _, _, ⟨MA⟩⟩ := lieModel_exists X G Γ(X, U) hU.fromSpec
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective X G Γ(X, U) hU.fromSpec E MA
  haveI := Module.finitePresentation_of_projective Γ(X, U) E
  rw [finrank_fieldPt G _ MA φ₁ M₁, finrank_fieldPt G _ MA φ₂ M₂]
  rw [genPt_comp, genPt_comp] at h
  have hs := (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).1 h
  exact (hs.map (Module.isLocallyConstant_rankAtStalk (R := Γ(X, U)) (M := E)).continuous).eq

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_finrank_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V), Module.finrank (𝓞 L) V = Module.finrank Ω Li := by
  intro X Ω _ ξ hsp G _ _ _ Li _ _ M L _ _ z V _ _ MB
  obtain ⟨V', _, _, ⟨M'⟩⟩ := lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)
  letI : Module (𝓞 L) V' := Module.compHom V' (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L V' := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := LieRank.exists_lift G z MB M'
  rw [LieRank.finrank_eq_of_isBaseChange_fractionRing j (GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) L z V V' MB M' j hj)]
  exact (LieRank.finrank_eq_of_specializes G ξ _ (hsp _) M M').symm

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalLieModelExtendsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lie_model_extends : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F) (_ : Module R F) (MR : LieModel G x F) (e : J → F), p.1 ∈ x.opensRange ∧ x.opensRange ≤ N ∧ ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 → ∀ (i : J) (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G), v.left = spMap (dualMap ψ) ≫ (MR.pt (e i)).left → M.Extends q (c i) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | exact GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropFTopHolds
section
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

def propFTopE {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N)
    (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (p : ℕ) (τ : Ψ) : ℝ :=
  if hp : 2 ≤ p then Classical.choose (GlobalTheory.T.delta_term_log_degree_bound Ψ N T.j p τ (frob p τ) T.j_lt.le hp) else 0

theorem propFTopE_spec {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N)
    (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (p : ℕ) (τ : Ψ) (hp : 2 ≤ p) :
    |propFTopE T frob p τ| ≤ N / ((p : ℝ) - 1) ∧
      ∀ Q : RP Ψ N, deltaTerm T.j p τ (frob p τ) 1 Q = propFTopE T frob p τ * Real.log p * degFl Q := by
  have h := Classical.choose_spec (GlobalTheory.T.delta_term_log_degree_bound Ψ N T.j p τ (frob p τ) T.j_lt.le hp)
  simp only [propFTopE, dif_pos hp]
  exact ⟨h.1, h.2.2.2⟩

theorem propFTop : PropFTop := by
  intro hPI hML hDS Ψ _ _ N T II frob rd Lval hII hConv hProp hP6 hrd hbad hNear
  classical
  choose R hR using hNear
  let good : ℕ → Finset ℕ := fun B => (Finset.Ioc 2 B).filter (fun p => p.Prime ∧ p ∉ T.bad)
  refine ⟨fun B c τ => (R c τ).ht - ∑ p ∈ good B, propFTopE T frob p τ * Real.log p, ?_, ?_⟩
  · intro B hB c τ Q hQ
    have hN : 1 ≤ N := by have := T.j_pos; have := T.j_lt; omega
    have hQ' : Q.IsHomogeneous (dimFl Ψ N + 1 - 1) := by rwa [Nat.add_sub_cancel]
    have h6 := hP6 2 B le_rfl hB c τ 1 le_rfl hN Q hQ'
    have hroot := GlobalTheory.T.root_flat_pushforward_geoFun hPI hML hDS Ψ N (T.M 2 c) II τ (R c τ) Q hII (hConv 2 c) hQ
    have hgeo := hProp.2.1 2 c Q
    have hd : ∀ p ∈ good B, deltaTerm T.j p τ (frob p τ) 1 Q = propFTopE T frob p τ * Real.log p * degFl Q :=
      fun p hp => (propFTopE_spec T frob p τ (Finset.mem_filter.mp hp).2.1.two_le).2 Q
    have h2 : T.PPc II 2 c (pk τ 1 * Q) = (R c τ).ht * (T.vol c * degFl Q) := by
      simp only [RootTower.PPc]; rw [hroot, hgeo]
    rw [Finset.sum_congr rfl hd] at h6
    rw [sub_mul, Finset.sum_mul]
    rw [h2] at h6
    rw [← Finset.sum_mul] at h6 ⊢
    change _ = _ + T.vol c * ((∑ p ∈ good B, propFTopE T frob p τ * Real.log p) * degFl Q) at h6
    linarith [h6]
  · intro B hB hcard c τ
    obtain ⟨hrec, d, v, hrec_le, hEq, hdv, hvsum⟩ := hR c τ
    have hdisj : Disjoint T.bad (good B) :=
      Finset.disjoint_left.mpr fun p hp hg => (Finset.mem_filter.mp hg).2.2 hp
    let d' : ℕ → ℝ := fun p => if p ∈ T.bad then d p else -(propFTopE T frob p τ * Real.log p)
    let v' : ℕ → ℝ := fun p => if p ∈ T.bad then v p else 0
    have hsb : ∑ p ∈ T.bad, d' p = ∑ p ∈ T.bad, d p :=
      Finset.sum_congr rfl fun p hp => by simp [d', hp]
    have hsg : ∑ p ∈ good B, d' p = -∑ p ∈ good B, propFTopE T frob p τ * Real.log p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p hp => by
        simp [d', Finset.disjoint_right.mp hdisj hp]
    have hvb : ∑ p ∈ T.bad ∪ good B, v' p * Real.log p = ∑ p ∈ T.bad, v p * Real.log p := by
      rw [Finset.sum_union hdisj]
      have h1 : ∑ p ∈ T.bad, v' p * Real.log p = ∑ p ∈ T.bad, v p * Real.log p :=
        Finset.sum_congr rfl fun p hp => by simp [v', hp]
      have h2 : ∑ p ∈ good B, v' p * Real.log p = 0 :=
        Finset.sum_eq_zero fun p hp => by simp [v', Finset.disjoint_right.mp hdisj hp]
      rw [h1, h2, add_zero]
    have hS : ∀ p ∈ T.bad ∪ good B, p.Prime ∧ (p ≤ B ∨ p ∈ T.bad) := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ⟨hbad p hp, Or.inr hp⟩
      · have := Finset.mem_filter.mp hp
        exact ⟨this.2.1, Or.inl (Finset.mem_Ioc.mp this.1).2⟩
    have hB3 : 3 ≤ B := by omega
    have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
    have hmain := hB_bound N T.j B (T.bad ∪ good B) d' v' (Real.log rd) Lval hrec
      ((R c τ).ht - ∑ p ∈ good B, propFTopE T frob p τ * Real.log p) T.j_lt.le hB3 hlrd hrec_le
      (by rw [Finset.sum_union hdisj, hsb, hsg, hEq]; ring)
      (fun p hp => (hS p hp).1)
      (fun p hp => by
        by_cases hb : p ∈ T.bad
        · simp only [v', hb, if_true]; exact (hdv p hb).1
        · simp [v', hb])
      (fun p hp => by
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        by_cases hb : p ∈ T.bad
        · simp only [d', v', hb, if_true]
          refine (hdv p hb).2.trans (le_of_eq ?_)
          ring
        · simp only [d', v', hb, if_false, mul_zero, add_zero, abs_neg, abs_mul, abs_of_nonneg hlog]
          exact mul_le_mul_of_nonneg_right
            (propFTopE_spec T frob p τ (hS p hp).1.two_le).1 hlog)
      (by rw [hvb]; exact hvsum)
      (GlobalTheory.T.sum_log_prime_div_pred_bound B T.bad (T.bad ∪ good B) hB hcard hS)
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hrdpos : (0 : ℝ) < rd := by linarith
    simp only [bigLam]
    rw [Real.log_mul hBpos.ne' hrdpos.ne']
    simpa [add_assoc] using hmain

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesFlagDegree
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

theorem rootLine_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (r : CMType H × Fin (D.p + D.q)) (q : Cpt 𝔐.ξ) (cc : (k : K) → J k) (b : Fin (labelRk D (HodgeCpt.rootIdx D r).1) → 𝔐.Li) (t : Ω), Fl.RootLines xdeg e → InChart 𝔐.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc q → (∀ j, flagStep Ω b j = flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) j) → (𝔐.V (HodgeCpt.rootIdx D r).1).IsFrameAt b q → b (HodgeCpt.rootIdx D r).2 - t • Fl.b (HodgeCpt.rootIdx D r).1 (HodgeCpt.rootIdx D r).2 ∈ flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2 → unitAt 𝔐.ξ q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r / t ^ HodgeCpt.rootSgn D r) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 Fl xdeg e r q cc b t hd hq hF hL hc
  have ht := FlagModel.gr_isGenAt _ b (Fl.b (HodgeCpt.rootIdx D r).1) q hL hF _ t hc
  have hT : (Fl.rootLat r).IsGenAt q (t ^ HodgeCpt.rootSgn D r) := by
    simpa [HodgeCpt.Flag.rootLat] using FlagModel.tens_isGenAt
      (fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
      (fun _ => HodgeCpt.rootSgn D r) q (fun _ => t) fun _ => ht
  obtain ⟨he, h⟩ := hd r
  have h1 := h q (Set.mem_univ _) cc hq
  have hy : (∏ k, y ⟨k, cc k⟩ ^ xdeg r k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hq.1 k hk)
  have hW : (Fl.rootLat r).IsGenAt q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r) := ⟨mul_ne_zero hy he, h1⟩
  have hw0 := hW.1
  have ht0 := hT.1
  refine ⟨div_ne_zero hw0 ht0, ?_, ?_⟩
  · simpa using FlagModel.zpow_ratio _ q _ _ hT hW 1
  · simpa using FlagModel.zpow_ratio _ q _ _ hW hT 1

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenAtComponentStalkStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_eigen_at_component_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (p : Cpt (Z.ξ₀ ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk p.1) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt (Y.X.fromSpecStalk p.1) ⟶ Y.t.G)), (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc → StableEig Y.t (Y.X.fromSpecStalk p.1) κ σ e → ∃ b : Fin r → Z.V, (∀ i, Z.M.Extends p (b i) (e i)) ∧ (Z.eig σ).IsFrameAt b p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig | exact GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsSpreadFromStalkStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vectors_spread_from_stalk : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (P : X) (ι : Type) [Finite ι] (e : ι → (epsAt (X.fromSpecStalk P) ⟶ G)) (f : X.presheaf.stalk P), (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G (X.fromSpecStalk P) (e i)) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (θ : R →+* X.presheaf.stalk P) (e' : ι → (epsAt x ⟶ G)) (f' : R), P ∈ x.opensRange ∧ spMap θ ≫ x = X.fromSpecStalk P ∧ θ f' = f ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (e' i)) ∧ ∀ i, (e i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e' i).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusEmbeddingLieInjectiveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_embedding_lie_injective : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] [Smooth G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (MT : LieModel (splitTorus S X) b (X →+ R)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G b E) (A : (X →+ R) →ₗ[R] E), (∀ δ, M.pt (A δ) = MT.pt δ ≫ u) → Function.Injective A ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range A → y ∈ LinearMap.range A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusSat.lie_torus_saturated | exact GlobalTheory.CompanionTheory.Ar.TorusSat.lie_torus_saturated | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusSat.lie_torus_saturated <;> assumption)
end

