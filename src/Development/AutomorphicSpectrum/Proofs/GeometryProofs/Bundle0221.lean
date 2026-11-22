import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0213
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0217
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDegreeEq
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0216
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0165
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0218

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLieModelCompleteDvr
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan

open MonObj
open GlobalTheory.CompanionTheory.Ar.LieTangent (epsBase epsScale isTanAt_iff isTanAt_scale spec_dual_eps spec_eps_alg)

section Push

variable (T : CDVR) {X : Scheme.{0}} (zV : Spec (CommRingCat.of T.V) ⟶ X) {A : CategoryTheory.Over X} [GrpObj A]
  {B : CategoryTheory.Over (Spec (CommRingCat.of T.V))} [GrpObj B] {Ψ : B.left ⟶ A.left}

theorem epsOver_hom :
    (epsOver T.V T.V).hom = Spec.map (CommRingCat.ofHom (algebraMap T.V (DualNumber T.V))) :=
  rfl

def idU : epsAt zV ⟶ CategoryTheory.Over.mk ((epsOver T.V T.V).hom ≫ zV) :=
  CategoryTheory.Over.homMk (𝟙 _) (by rw [Category.id_comp]; rfl)

def pushAt (h : IsGrpPullback B A zV Ψ) : (epsOver T.V T.V ⟶ B) →* (epsAt zV ⟶ A) :=
  (preHom (idU T zV)).comp (pushHom h (epsOver T.V T.V))

def pushGen (h : IsGrpPullback B A zV Ψ) : (epsOver T.V T.V ⟶ B) →* (epsAt (gen T zV) ⟶ A) :=
  (preHom (epsBase (algebraMap T.V T.Fr) rfl)).comp (pushAt T zV h)

variable {T zV}

theorem pushAt_left (h : IsGrpPullback B A zV Ψ) (v : epsOver T.V T.V ⟶ B) :
    (pushAt T zV h v).left = v.left ≫ Ψ := by
  simp [pushAt, preHom, pushHom, pushPt, idU]

theorem pushGen_left (h : IsGrpPullback B A zV Ψ) (v : epsOver T.V T.V ⟶ B) :
    (pushGen T zV h v).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  simp [pushGen, preHom, pushAt_left, GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase]
private theorem key_lemma' {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {Y : Scheme.{0}} (zV : Y ⟶ X)
    {f : Y ⟶ X} (hf : f = zV) :
    (1 : CategoryTheory.Over.mk f ⟶ A).left = (1 : CategoryTheory.Over.mk zV ⟶ A).left := by
  subst hf
  rfl

private theorem one_left_comp_of_isGrpPullback_over {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {Tb : CDVR}
    {zV : Spec (CommRingCat.of Tb.V) ⟶ X} {B : CategoryTheory.Over (Spec (CommRingCat.of Tb.V))} [GrpObj B]
    {Ψ : B.left ⟶ A.left} (h : IsGrpPullback B A zV Ψ) (T' : CategoryTheory.Over (Spec (CommRingCat.of Tb.V))) :
    (1 : T' ⟶ B).left ≫ Ψ = (1 : CategoryTheory.Over.mk (T'.hom ≫ zV) ⟶ A).left := by
  have := congrArg CategoryTheory.Over.Hom.left (map_one (pushHom h T'))
  simpa [pushHom, pushPt] using this

theorem one_left (h : IsGrpPullback B A zV Ψ) :
    (1 : ptOver T.V T.V ⟶ B).left ≫ Ψ = (1 : CategoryTheory.Over.mk zV ⟶ A).left := by
  have hf : (ptOver T.V T.V).hom ≫ zV = zV := by
    simp [ptOver, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
  rw [← key_lemma' zV hf]
  exact one_left_comp_of_isGrpPullback_over h (ptOver T.V T.V)

theorem isTanAt_push (h : IsGrpPullback B A zV Ψ) {v : epsOver T.V T.V ⟶ B} (hv : IsTan v) :
    IsTanAt A zV (pushAt T zV h v) := by
  have e : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
      (1 : ptOver T.V T.V ⟶ B).left := hv
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ (pushAt T zV h v).left =
    (1 : CategoryTheory.Over.mk zV ⟶ A).left
  rw [pushAt_left, ← Category.assoc, e]
  exact one_left h

theorem isTan_of_push (h : IsGrpPullback B A zV Ψ) {v : epsOver T.V T.V ⟶ B}
    (hv : IsTanAt A zV (pushAt T zV h v)) : IsTan v := by
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
    (1 : ptOver T.V T.V ⟶ B).left
  have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ (pushAt T zV h v).left =
      (1 : CategoryTheory.Over.mk zV ⟶ A).left := hv
  rw [pushAt_left, ← Category.assoc, ← one_left h] at hv'
  refine h.1.hom_ext hv' ?_
  rw [Category.assoc, CategoryTheory.Over.w v, CategoryTheory.Over.w (1 : ptOver T.V T.V ⟶ B), epsOver_hom,
    GlobalTheory.CompanionTheory.Ar.LieTangent.spec_comp]
  simp [ptOver, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]

theorem pushAt_surj (h : IsGrpPullback B A zV Ψ) (v : epsAt zV ⟶ A) :
    ∃ v' : epsOver T.V T.V ⟶ B, pushAt T zV h v' = v := by
  have hw : v.left ≫ A.hom = (epsOver T.V T.V).hom ≫ zV := by
    rw [CategoryTheory.Over.w v, epsOver_hom]
    rfl
  refine ⟨CategoryTheory.Over.homMk (h.1.lift v.left (epsOver T.V T.V).hom hw) (h.1.lift_snd _ _ _), ?_⟩
  apply CategoryTheory.Over.OverMorphism.ext
  rw [pushAt_left]
  exact h.1.lift_fst _ _ _

end Push

section Model

variable {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {R : Type} [CommRing R]
  {x : Spec (CommRingCat.of R) ⟶ X} {EC : Type} [AddCommGroup EC] [Module R EC]

theorem pt_list_sum (MC : LieModel A x EC) (l : List EC) : MC.pt l.sum = (l.map MC.pt).prod := by
  induction l with
  | nil =>
    simp only [List.sum_nil, List.map_nil, List.prod_nil]
    exact MC.pt_zero
  | cons a l ih => rw [List.sum_cons, MC.add, ih, List.map_cons, List.prod_cons]

theorem pt_sum (MC : LieModel A x EC) {r : ℕ} (f : Fin r → EC) :
    MC.pt (∑ i, f i) = (List.ofFn fun i => MC.pt (f i)).prod := by
  rw [← List.sum_ofFn, pt_list_sum, List.map_ofFn]
  rfl

theorem mem_eigSp_iff {O : Type} [CommRing O] (ρ : O →+* Module.End R EC) (σ : O →+* R) (w : EC) :
    w ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ↔ ∀ a, ρ a w = σ a • w := by
  simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

end Model

section Main

variable (T : CDVR) {X : Scheme.{0}} (zV : Spec (CommRingCat.of T.V) ⟶ X) {A : CategoryTheory.Over X} [GrpObj A]
  {B : CategoryTheory.Over (Spec (CommRingCat.of T.V))} [GrpObj B] {Ψ : B.left ⟶ A.left}

theorem eigen_span_lie_basis (h : IsGrpPullback B A zV Ψ) {O : Type} [CommRing O] (aA : O → (A ⟶ A))
    (hA : ∀ a, IsMonHom (aA a)) (aB : O → (B ⟶ B)) (hc : ∀ a, (aB a).left ≫ Ψ = Ψ ≫ (aA a).left)
    {EC : Type} [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC]
    (MC : LieModel A (FinRd.Roots.gen T zV) EC) (ρC : O →+* Module.End T.Fr EC) (hρ : MC.IsActOf aA ρC)
    (σ : O →+* T.V) {r : ℕ} (ub : Fin r → (epsOver T.V T.V ⟶ B)) (hut : ∀ i, IsTan (ub i))
    (hue : ∀ i a, (ub i ≫ aB a).left =
      Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left)
    (hub : ∀ w : epsOver T.V T.V ⟶ B, IsTan w →
      (∀ a, (w ≫ aB a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) →
      ∃ cf : Fin r → T.V, IsComb ub cf w)
    (yb : Fin r → EC)
    (hyb : ∀ i, (MC.pt (yb i)).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ)
    (L : Submodule T.V EC)
    (hL : ∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ A, GlobalTheory.CompanionTheory.Ar.IsTanAt A zV v ∧
      (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) :
    L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V =
      Submodule.span T.V (Set.range yb) := by
  have hue' : ∀ i a, (ub i ≫ aB a).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (σ a))) ≫ (ub i).left := hue
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V (FractionRing T.V)
  apply le_antisymm
  · rintro w ⟨hwL, hwE⟩
    obtain ⟨v, hvt, hvl⟩ := (hL w).1 hwL
    obtain ⟨v', rfl⟩ := pushAt_surj h v
    have hv't := isTan_of_push h hvt
    have hwE' : ∀ a, ρC a w = ((algebraMap T.V T.Fr).comp σ) a • w := (mem_eigSp_iff _ _ _).1 hwE
    have hpw : MC.pt w = pushGen T zV h v' := by
      apply CategoryTheory.Over.OverMorphism.ext
      rw [pushGen_left, hvl, pushAt_left]
    have hv'e : ∀ a, (v' ≫ aB a).left =
        Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ v'.left := by
      intro a
      have hp := isTanAt_push h hv't
      have ht1 : GlobalTheory.CompanionTheory.Ar.IsTanAt A zV (pushAt T zV h v' ≫ aA a) := by
        have hp' := hp
        unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at hp' ⊢
        rw [CategoryTheory.Over.comp_left, ← Category.assoc, hp', ← CategoryTheory.Over.comp_left]
        have := hA a
        simp
      have ht2 : GlobalTheory.CompanionTheory.Ar.IsTanAt A zV (GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale zV (σ a) ≫ pushAt T zV h v') :=
        isTanAt_scale (σ a) hp
      have eq1 : pushAt T zV h v' ≫ aA a = GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale zV (σ a) ≫ pushAt T zV h v' := by
        refine GlobalTheory.CompanionTheory.Ar.LieTangent.tan_ext hinj ht1 ht2 ?_
        have e1 := congrArg CategoryTheory.Over.Hom.left (hρ a w)
        rw [hwE' a, MC.smul, hpw, CategoryTheory.Over.comp_left, pushGen_left] at e1
        simp only [CategoryTheory.Over.comp_left, pushAt_left, Category.assoc] at e1 ⊢
        rw [← e1]
        simp only [GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale, CategoryTheory.Over.homMk_left]
        simp only [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]
      refine h.1.hom_ext ?_ ?_
      · rw [CategoryTheory.Over.comp_left, Category.assoc, hc a, ← Category.assoc, ← pushAt_left h v',
          ← CategoryTheory.Over.comp_left, eq1, CategoryTheory.Over.comp_left, pushAt_left]
        simp only [GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale, CategoryTheory.Over.homMk_left, Category.assoc]
        rfl
      · rw [CategoryTheory.Over.w (v' ≫ aB a), Category.assoc, CategoryTheory.Over.w v', epsOver_hom]
        exact (GlobalTheory.CompanionTheory.Ar.LieTangent.spec_eps_alg (σ a)).symm
    obtain ⟨cf, hcf⟩ := hub v' hv't hv'e
    obtain ⟨u, hu, hv'u⟩ := hcf
    have hw : w = ∑ i, cf i • yb i := by
      apply MC.inj
      rw [hpw, pt_sum, hv'u, map_list_prod, List.map_ofFn]
      congr 1
      apply congrArg List.ofFn
      funext i
      apply CategoryTheory.Over.OverMorphism.ext
      rw [Function.comp_apply, pushGen_left, hu i, ← algebraMap_smul T.Fr (cf i) (yb i), MC.smul, hyb i]
      simp only [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
      rw [show Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (cf i))) =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (cf i))) from rfl, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨(hL _).2 ⟨pushAt T zV h (ub i), isTanAt_push h (hut i), by rw [hyb i, pushAt_left]⟩, ?_⟩
    show yb i ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)
    rw [mem_eigSp_iff]
    intro a
    apply MC.inj
    apply CategoryTheory.Over.OverMorphism.ext
    rw [hρ a (yb i), MC.smul, CategoryTheory.Over.comp_left, hyb i]
    simp only [Category.assoc]
    rw [← hc a, ← Category.assoc (ub i).left, ← CategoryTheory.Over.comp_left, hue' i a]
    simp only [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]

end Main

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan

theorem GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → (∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left) → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf tX.act.act ρC → ∀ (σ : 𝓞 E →+* T.V) (r : ℕ) (ub : Fin r → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i a, (ub i ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → (∀ a, (w ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) → ∃ cf : Fin r → T.V, IsComb ub cf w) → ∀ yb : Fin r → EC, (∀ i, (MC.pt (yb i)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ) → ∀ L : Submodule T.V EC, (∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ tX.G, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G zV v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) → L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V = Submodule.span T.V (Set.range yb) := by
  intro E _ _ _ H X tX T zV G Ψ h hc EC _ _ _ _ MC ρC hρ σ r ub hut hue hub yb hyb L hL
  exact eigen_span_lie_basis T zV h tX.act.act tX.act.hom G.act.act hc MC ρC hρ σ ub hut hue hub yb hyb L hL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDegreeEqStatement
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_degree_eq : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricToTangentPowerFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.geometric_to_tangent_power_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0), GeomPF t x → TanPF t x p := by
  first | exact @PositivityTheory.HtPt.Ce.geompf_tan | exact PositivityTheory.HtPt.Ce.geompf_tan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianBundleFibreTangentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_bundle_fibre_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (tC : SAB H (Sp ℂ)) (e : L →+* ℂ) (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L))) (mB : SABMap tC tB (spMap e)) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB → ∀ (V' : Type) (Tn : V' → (epsAt (𝟙 (Sp ℂ)) ⟶ tC.G)), (∀ x, IsTanAt tC.G (𝟙 _) (Tn x)) → ∃ hb : V' → V' → ℂ, (∀ x x', HodgeIP tC.G tC.PP.L (𝟙 _) (Tn x) (Tn x') (hb x x')) ∧ ∀ (x x' : V') (y y' : B.carrier), (Tn x).left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y).left → (Tn x').left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y').left → hb x x' = (B.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeBC.main | exact GlobalTheory.CompanionTheory.Ar.HodgeBC.main | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeBC.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDegreeCompositionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_degree_composition : ∀ (e d : ℕ) (X Y Z : Type) [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TopologicalSpace Z] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (C : FinHolAtlas e Z) (π : Y → X) (h : Z → Y) (br : Set Y), HoloMap B A π → Function.Bijective π → HoloMap C B h → IsDegreeOff B C h d br → HoloMap C A (π ∘ h) ∧ IsDegreeOff A C (π ∘ h) d (π '' br) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff | exact GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff | (intros; apply GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntegralFibreAppendEqMulImageStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | exact GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | (intros; apply GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompleteDvrBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_complete_dvr_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module T.Fr EC) (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.exists_lieModel_act_gen | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.exists_lieModel_act_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.exists_lieModel_act_gen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameArchimedeanStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ s : CMType H ⊕ CMType H, ∃ σ : 𝓞 E →+* T.V, (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) ∧ ∀ a, algebraMap T.V T.Fr (σ a) = io (labelEmb c s a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameLocalBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_local_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)), ∃ w : EC, FinRd.Roots.IsFrameVec Or io zT MC w s i ∧ Or.𝔐.M.ValAt (FinRd.Roots.gen T zV) (Or.Fl.b s i) (MC.pt w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameNonarchimedeanStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_nonarchimedean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → InFibre Or.𝔐.ξ p ⟨centre zV, Or.𝔐.all _⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameFinal
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.PtEq

set_option backward.isDefEq.respectTransparency false

theorem exists_factor' {O' R Ω C : Type} [CommRing O'] [CommRing R] [CommRing Ω] [CommRing C] (g : O' →+* Ω)
    (cl : O' →+* C) (hg : Function.Injective g) (φ : R →+* Ω) (ψ : R →+* C)
    (h : ∀ r, ∃ s, g s = φ r ∧ cl s = ψ r) : ∃ θ : R →+* O', g.comp θ = φ ∧ cl.comp θ = ψ := by
  choose θ h1 h2 using h
  exact ⟨{ toFun := θ
           map_one' := hg (by simp [h1])
           map_mul' := fun a b => hg (by simp [h1])
           map_zero' := hg (by simp [h1])
           map_add' := fun a b => hg (by simp [h1]) }, RingHom.ext h1, RingHom.ext h2⟩

theorem pts_eq' {O' Ω R₀ : Type} [CommRing O'] [Field Ω] [CommRing R₀] (g : O' →+* Ω) (hg : Function.Injective g)
    {B : Scheme.{0}} (s : B ⟶ Sp R₀) [IsSeparated s] {a b : Sp O' ⟶ B} (h : spMap g ≫ a = spMap g ≫ b) : a = b := by
  haveI : IsDomain O' := hg.isDomain g
  haveI : IsDominant (spMap g) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot g).1 hg]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated s ?_ (spMap g) h
  refine ext_of_isDominant (spMap g) ?_
  rw [← Category.assoc, h, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.PtEq

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

open PtEq in
set_option maxHeartbeats 600000 in

theorem ptY_eq_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → (letI := io.toAlgebra; Small.ptY Y zT = FinRd.Roots.gen T zV ≫ Or.𝔐.f) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hv hG la T io e y evT zT t hI zV hR
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  obtain ⟨-, -, -, -, -, -, ⟨q, φ, ψ, yq, hφ, hψ, hr⟩, -⟩ := hI
  have hgen : genPt Or.𝔐.ξ ⤳ centre (gen T zV) := Or.𝔐.all _
  let P : Cpt Or.𝔐.ξ := ⟨centre (gen T zV), hgen⟩
  have hinj : Function.Injective (genMap Or.𝔐.ξ P) := Or.𝔐.tie.gen.inj P
  have hreg : ∀ r, ∃ s', genMap Or.𝔐.ξ P s' = φ.toRingHom r ∧
      (Scheme.stalkClosedPointTo (gen T zV)).hom s' = ψ.toRingHom r := fun r => by
    obtain ⟨h, e'⟩ := hr r
    obtain ⟨h', s', hs, hs'⟩ := hR ⟨φ r, h⟩
    exact ⟨s', hs, hs'.trans e'.symm⟩
  obtain ⟨θ, hθ1, hθ2⟩ := exists_factor' _ _ hinj φ.toRingHom ψ.toRingHom hreg
  have hsep : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have he : Or.𝔐.X.fromSpecStalk P.1 ≫ Or.𝔐.f = spMap θ ≫ Small.ptY Y yq := by
    refine pts_eq' (genMap Or.𝔐.ξ P) hinj Y.s ?_
    rw [← Category.assoc, ← Category.assoc]
    have e1 : spMap (genMap Or.𝔐.ξ P) ≫ Or.𝔐.X.fromSpecStalk P.1 = Or.𝔐.ξ := LieTangent.spec_genMap _ _
    rw [e1, ← Fr.pt_eq, Small.ptY_map Y hφ, ← hθ1, LieTangent.spec_comp]
  have e2 : spMap (Scheme.stalkClosedPointTo (gen T zV)).hom ≫ Or.𝔐.X.fromSpecStalk P.1 = gen T zV :=
    LieTangent.spec_centre (gen T zV)
  rw [Small.ptY_map Y hψ]
  have e3 : ψ.toRingHom = (Scheme.stalkClosedPointTo (gen T zV)).hom.comp θ := hθ2.symm
  have e4 : spMap ((Scheme.stalkClosedPointTo (gen T zV)).hom.comp θ) =
      spMap (Scheme.stalkClosedPointTo (gen T zV)).hom ≫ spMap θ := (LieTangent.spec_comp θ _).symm
  rw [e3, e4, Category.assoc]
  exact (congrArg (fun u => spMap (Scheme.stalkClosedPointTo (gen T zV)).hom ≫ u) he.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun u => u ≫ Or.𝔐.f) e2))

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginRootIndexBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_root_index_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (ρ : RootIx Dw) (q : Cpt Or.𝔐.ξ) (ch : (k : RM.K) → RM.ι k), InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) ch q → ∀ (b : Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1) → Or.𝔐.Li) (Tm : Matrix (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) RM.Ω), (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) i) → (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).IsFrameAt b q → (∀ i, b i = ∑ j, Tm i j • Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1 j) → (∀ i, Tm i i ≠ 0) → ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ) ∈ regAt Or.𝔐.ξ q ∧ (((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ))⁻¹ ∈ regAt Or.𝔐.ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit.root_unit | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit.root_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit.root_unit <;> assumption)
end

