import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivialMonodromyOrbitConvergesSymmetricDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X} {v : Sp (DualNumber k) ⟶ t.G.left}

theorem preimage_le_of_isTanAtG (hv : IsTanAtG t x v) {V : X.Opens} {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) :
    (specO k (DualNumber k)).hom ⁻¹ᵁ T ≤ v ⁻¹ᵁ W := by
  intro y hy
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero y
  have h₁ : s ∈ (sec (epsZero k) ≫ (specO k (DualNumber k)).hom) ⁻¹ᵁ T := hy
  rw [sec_hom] at h₁
  have h₂ : s ∈ (x ≫ unitSec t.G) ⁻¹ᵁ W := hW (hT h₁)
  rw [← epsZero_comp_of_isTanAtG t hv] at h₂
  exact h₂

theorem tanForm_dUnit (hv : IsTanAtG t x v) {V : X.Opens} {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) (f : Γ(t.G.left, W))
    (a b : Γ(Sp k, T))
    (e : (v.appLE W _ (preimage_le_of_isTanAtG t hv hW hT) f :
        Γ((specO k (DualNumber k)).left, (specO k (DualNumber k)).hom ⁻¹ᵁ T)) =
      (specO k (DualNumber k)).hom.appLE T _ le_rfl a +
        (specO k (DualNumber k)).hom.appLE T _ le_rfl b * resG _ le_top (epsFn k)) :
    (tanForm t hv).app T (pullbackSections x (omega t.G) hT (dUnit t.G hW f)) = b := by
  have hV : T ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  have c := baseMap_d (sec_hom (MonObj.one (X := t.G))) (sec_hom (epsZero k)) hv.1
    (epsZero_comp_of_isTanAtG t hv) hW hT hV (preimage_le_of_isTanAtG t hv hW hT) f
  refine (congrArg ((epsIso k).hom.app T) c).trans ?_
  rw [e, map_add, d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, GlobalTheory.LB.resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp k) (le_top : T ≤ ⊤)))).trans (_root_.mul_one b)

variable {k' : Type} [CommRing k'] (φ : k →+* k')

theorem spMap_dualMap_comp : spMap (Formalism.L2.Pj.dualMap φ) ≫ (specO k (DualNumber k)).hom =
    (specO k' (DualNumber k')).hom ≫ spMap φ := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_dualMap_epsFn :
    (spMap (Formalism.L2.Pj.dualMap φ)).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn k) = epsFn k' := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Formalism.L2.Pj.dualMap φ))) DualNumber.eps).symm.trans ?_
  refine congrArg (Scheme.ΓSpecIso (.of (DualNumber k'))).inv.hom ?_
  change Formalism.L2.Pj.dualMap φ DualNumber.eps = _
  ext <;> simp [Formalism.L2.Pj.dualMap]

theorem tanForm_baseChange {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (hv : IsTanAtG t x v)
    (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V)
    (s : Γ(omega t.G, V)) :
    ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      (spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) : Γ(Sp k, ⊤)) := by
  have := t.semi
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) : Γ(Sp k, ⊤))) := by
    obtain ⟨U, W, hU, hle, c⟩ := exists_isChart (sec_hom (MonObj.one (X := t.G))) (V := V)
      (x := x (spMap φ y.1)) (h trivial)
    obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap φ y.1) hU
    obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := t.G))) (resM _ hle s)
    have hf' : dUnit t.G c.le f = resM (omega t.G) hle s := hf
    have hTU' : spMap φ ⁻¹ᵁ T ≤ (spMap φ ≫ x) ⁻¹ᵁ U := (spMap φ).preimage_mono hTU
    obtain ⟨⟨a, b⟩, e⟩ := (bijective_add_mul_epsFn k T hT).2
      (v.appLE W _ (preimage_le_of_isTanAtG t hv c.le hTU) f)
    have e₁ := tanForm_dUnit t hv c.le hTU f a b e.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        spMap (Formalism.L2.Pj.dualMap φ) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_dualMap_comp φ)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap φ) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap φ).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_dualMap_comp φ) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_dualMap_epsFn φ)))
    have e₂ := tanForm_dUnit t hv' c.le hTU' f ((spMap φ).appLE T _ le_rfl a)
      ((spMap φ).appLE T _ le_rfl b) (by
        refine (appLE_appLE rfl (preimage_le_of_isTanAtG t hv c.le hTU) kk _ f).symm.trans ?_
        refine (congrArg ((spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk) e.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf', QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap φ ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (tanForm t hv') le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap φ) (le_top : T ≤ ⊤) le_rfl _).trans
      (resG_appLE (spMap φ) le_top (le_preimage_top _ _) _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (tanForm t hv) le_top _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

theorem tanEv_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (v : Sp (DualNumber k) ⟶ t.G.left) (hv : IsTanAtG t x v) (k' : Type) [CommRing k'] (φ : k →+* k') (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) (s : Γ(GlobalTheory.LieVB.omega t.G, V)), tanEv t hv' h' s = φ (tanEv t hv h s) := by
  intro E _ _ _ H X t k _ x V h v hv k' _ φ hv' h' s
  refine (congrArg (Scheme.ΓSpecIso (.of k')).hom (tanForm_baseChange t φ h hv hv' h' s)).trans ?_
  refine (congrArg (Scheme.ΓSpecIso (.of k')).hom (appLE_top (spMap φ) _)).trans ?_
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) _)

end GlobalTheory.LocM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

theorem cotMap_list_prod {S : Scheme.{0}} {T G : Over S} [GrpObj G] [QuasiSeparated G.hom] {s : 𝟙_ (Over S) ⟶ T} :
    ∀ {m : ℕ} (z : Fin m → (T ⟶ G)) (hz : ∀ i, s ≫ z i = η) (h : s ≫ (List.ofFn z).prod = η),
      cotMap (List.ofFn z).prod h = ∑ i, cotMap (z i) (hz i)
  | 0, z, hz, h => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact cotMap_eq_zero (by rw [List.ofFn_zero, List.prod_nil, Hom.one_def]) _
  | m + 1, z, hz, h => by
    have e : (List.ofFn z).prod = z 0 * (List.ofFn fun i : Fin m => z i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    have h₁ : (η : 𝟙_ (Over S) ⟶ G) = 1 := by rw [Hom.one_def]; simp
    have h' : s ≫ (List.ofFn fun i : Fin m => z i.succ).prod = η := by
      have := h
      rw [e, MonObj.comp_mul, hz 0, h₁, _root_.one_mul] at this
      exact this.trans h₁.symm
    rw [Fin.sum_univ_succ, ← cotMap_list_prod (fun i : Fin m => z i.succ) (fun i => hz _) h',
      ← cotMap_mul (hz 0) h' (e ▸ h)]
    congr 1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
variable {G' : Over (Sp k)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}

theorem exists_fibre_vector (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ y : specO k (DualNumber k) ⟶ G', epsZero k ≫ y = η ∧ y.left ≫ φ = v := by
  refine ⟨Over.homMk (hp.1.lift v _ hv.1) (hp.1.lift_snd _ _ _), Over.OverMorphism.ext (hp.1.hom_ext ?_ ?_),
    hp.1.lift_fst _ _ _⟩
  · refine (Category.assoc _ _ _).trans ((congrArg (sec (epsZero k) ≫ ·) (hp.1.lift_fst _ _ _)).trans ?_)
    exact (epsZero_comp_of_isTanAtG t hv).trans (unitSec_comp hp).symm
  · exact (Over.w _).trans (Over.w _).symm

theorem tanForm_eq_fibre (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v)
    {y : specO k (DualNumber k) ⟶ G'} (hy : epsZero k ≫ y = η) (e : y.left ≫ φ = v) :
    tanForm t hv = omegaBase hp ≫ cotMap y hy ≫ (epsIso k).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso k).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ := le_of_sq (unitSec_comp hp) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₂ := le_of_sq (epsZero_comp_of_isTanAtG t hv) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₃ := (le_preimage_of_comp e).2 (le_refl (v ⁻¹ᵁ W))
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl
    k₂ le_rfl a).trans (Eq.symm ?_)
  refine (congrArg ((cotMap y hy).app _) (omegaBase_dUnit hp le_rfl le_rfl k₁ le_rfl a)).trans ?_
  exact (cotMap_d y hy k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE e _ _ _ a))

theorem tanEv_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V),
    ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i)) (cf : Fin m → k)
      (w : Sp (DualNumber k) ⟶ t.G.left) (hw : IsTanAtG t x w), IsCombAtG t x v cf w →
      ∀ s : Γ(GlobalTheory.LieVB.omega t.G, V), tanEv t hw h s = ∑ i, cf i * tanEv t (hv i) h s := by
  rintro E _ _ _ H X t k _ x V h m v hv cf w hw ⟨u, hu, hw'⟩ s
  have hp := isGrpPullback_pullback t.G x
  have := t.semi
  have : QuasiSeparated ((Over.pullback x).obj t.G).hom := MorphismProperty.of_isPullback hp.1 inferInstance
  choose y hy ey using fun i => exists_fibre_vector t hp (hv i)
  obtain ⟨yw, hyw, eyw⟩ := exists_fibre_vector t hp hw
  let z := fun i => ptMap (dualScale (cf i)) ≫ y i
  have hz (i : Fin m) : epsZero k ≫ z i = η := by
    rw [← Category.assoc, epsZero_dualScale, hy]
  have hu' : u = fun i => pushHom hp _ (z i) := funext fun i => Over.OverMorphism.ext <| by
    refine (hu i).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    rw [ey]
    rfl
  have hprod : yw = (List.ofFn z).prod := by
    refine Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    refine eyw.trans (hw'.symm.trans ?_)
    rw [hu']
    exact (congrArg (fun q => q.left) ((map_list_prod (pushHom hp (specO k (DualNumber k))) (List.ofFn z)).trans
      (congrArg List.prod List.map_ofFn))).symm
  subst hprod
  let σ := (omegaBase hp).app ⊤ (pullbackSections x (omega t.G) h s)
  let F : (conormal (unitSec ((Over.pullback x).obj t.G)) ⟶ conormal (sec (epsZero k))) →+ k :=
    AddMonoidHom.mk' (fun α => (Scheme.ΓSpecIso (.of k)).hom ((epsIso k).hom.app ⊤ (α.app ⊤ σ))) fun α β =>
      (congrArg (Scheme.ΓSpecIso (.of k)).hom (map_add ((epsIso k).hom.app ⊤).hom (α.app ⊤ σ) (β.app ⊤ σ))).trans
        (map_add _ _ _)
  have hF {v' : Sp (DualNumber k) ⟶ t.G.left} (hv' : IsTanAtG t x v') {y'} (hy' : epsZero k ≫ y' = η)
      (e : y'.left ≫ pullback.fst t.G.hom x = v') : tanEv t hv' h s = F (cotMap y' hy') := by
    rw [tanEv, tanForm_eq_fibre t hp hv' hy' e]
    rfl
  rw [hF hw hyw eyw, cotMap_list_prod z hz, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := cotMap_comp (hy i) (epsZero_dualScale (cf i)) rfl (hz i)
  rw [cotMap_dualScale] at e
  rw [hF (hv i) (hy i) (ey i), ← e]
  refine (congrArg (Scheme.ΓSpecIso (.of k)).hom
    ((epsIso k).hom.app_smul (cst k (cf i)) ((cotMap (y i) (hy i)).app ⊤ σ))).trans ?_
  refine (map_mul _ _ _).trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentFamilyOfUniqueLiftPrime
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.GrNormPos

theorem sInf_pos {C M : Type} [NontriviallyNormedField C] [AddCommGroup M] [Module C M] {g m : ℕ} (V : Fin g → M)
    (U : Fin m → M) (hU : LinearIndependent C U) (L : Set M) (a : C) (ha : a ≠ 0)
    (h1 : ∀ w, ∃ c : Fin g → C, w = ∑ j, c j • V j)
    (h2 : ∀ c : Fin g → C, (∀ j, ‖c j‖ ≤ 1) → ∑ j, c j • V j ∈ L)
    (h3 : ∀ w ∈ L, ∃ c : Fin g → C, (∀ j, ‖c j‖ ≤ 1) ∧ a • w = ∑ j, c j • V j) (i : Fin m) :
    0 < sInf {r | ∃ cf : Fin m → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∑ k, cf k • U k ∈ L) ∧
      r = ‖cf i‖⁻¹} := by
  classical
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination C U)
    (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hU))
  have hl' : ∀ cf : Fin m → C, l (∑ k, cf k • U k) = cf := fun cf => by
    have := LinearMap.congr_fun hl cf
    rwa [LinearMap.comp_apply, Fintype.linearCombination_apply] at this
  set B : ℝ := ∑ j, ‖l (V j) i‖ + 1 with hB
  have hB0 : 0 < B := by positivity
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  refine lt_of_lt_of_le (div_pos ha0 hB0) (le_csInf ?_ ?_)
  · obtain ⟨c, hc⟩ := h1 (U i)
    obtain ⟨e, he⟩ := NormedField.exists_lt_norm C ‖c‖
    have he0 : 0 < ‖e‖ := (norm_nonneg c).trans_lt he
    have he1 : e ≠ 0 := norm_pos_iff.1 he0
    refine ⟨_, Pi.single i e⁻¹, by simpa using he1, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_, rfl⟩
    have : ∑ k, (Pi.single i e⁻¹ : Fin m → C) k • U k = ∑ j, (e⁻¹ * c j) • V j := by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), Pi.single_eq_same, hc,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    rw [this]
    refine h2 _ fun j => ?_
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ he0, mul_one]
    exact (norm_le_pi_norm c j).trans he.le
  · rintro r ⟨cf, h0, -, hL, rfl⟩
    obtain ⟨c, hc, e⟩ := h3 _ hL
    have e2 : a * cf i = ∑ j, c j * l (V j) i := by
      have := congrArg (fun z => l z i) e
      simpa [map_smul, hl', map_sum, Finset.sum_apply] using this
    have e3 : ‖a‖ * ‖cf i‖ ≤ B := by
      rw [← norm_mul, e2]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans (le_add_of_nonneg_right zero_le_one))
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc j)
    have h0' : 0 < ‖cf i‖ := norm_pos_iff.2 h0
    rw [div_le_iff₀ hB0, le_inv_mul_iff₀ h0', mul_comm]
    exact e3

open GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X}

theorem isComb_iff_eq {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ i, IsTanAtG t x (u i))
    (a : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ i, a i • tanOf (hu i))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ i, a i • tanOf (hu i))).left := (isComb_iff (fun i => tanOf (hu i)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨v, hv, e⟩ := h
  obtain ⟨v', hv', e'⟩ := h0
  have : v = v' := funext fun i => Over.OverMorphism.ext ((hv i).trans (hv' i).symm)
  rw [← e, ← e', this]

end

theorem grNorm_pos : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) (C : Formalism.MainNotions.DIV.Cons.SCF p) (b : Bool) (xO : Sp ↥(intO ↥C.S) ⟶ X), p.Prime → (∀ y : Sp ↥(intO ↥C.S) ⟶ X, spMap (intO ↥C.S).subtype ≫ y = spMap (intO ↥C.S).subtype ≫ xO → y = xO) → ∀ (m : ℕ) (u : Fin m → (Sp (DualNumber ↥C.S) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ xO) (u i)) → (∀ cf cf' w, IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf w → IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf' w → cf = cf') → ∀ i, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ xO) (lat t p (spMap (intO ↥C.S).subtype ≫ xO) b) u i := by
  intro hHT E _ _ _ H X t p C b xO hp huniq m u hu hinj i
  haveI : Fact p.Prime := Fact.mk hp
  obtain ⟨g, v, hv, hb, hL⟩ := GlobalTheory.LatDRFree.latDR_free E H X t C.S xO huniq
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpa : ‖(p : C.S)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    rw [C.norm_p, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
    rw [div_le_one (by linarith)]
    linarith
  have hsub : latDR t (spMap (intO ↥C.S).subtype ≫ xO) ⊆ lat t p (spMap (intO ↥C.S).subtype ≫ xO) b := by
    cases b
    · exact subset_rfl
    · exact latDR_subset_latHT E H X t C.S p _
  have hsup : lat t p (spMap (intO ↥C.S).subtype ≫ xO) b ⊆ latHT t p (spMap (intO ↥C.S).subtype ≫ xO) := by
    cases b
    · exact latDR_subset_latHT E H X t C.S p _
    · exact subset_rfl
  have h1 : ∀ w : TanM (spMap (intO ↥C.S).subtype ≫ xO) t.G, ∃ c : Fin g → C.S, w = ∑ j, c j • tanOf (hv j) :=
    fun w => by
      obtain ⟨c, hc, -⟩ := hb _ (isTan_tv w)
      exact ⟨c, tan_ext ((isComb_iff_eq hv c _).1 hc)⟩
  have key := sInf_pos (fun j => tanOf (hv j)) (fun k => tanOf (hu k)) ?_
    {w | (tv w).left ∈ lat t p (spMap (intO ↥C.S).subtype ≫ xO) b} (p : C.S) (Nat.cast_ne_zero.2 hp.ne_zero) h1
    ?_ ?_ i
  · unfold GlobalTheory.ShFam.Pad.grNorm
    refine key.trans_eq (congrArg sInf (Set.ext fun r => exists_congr fun cf => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr_left fun _ => Iff.symm ?_))
    refine ⟨?_, fun h => ⟨_, h, (isComb_iff_eq hu cf _).2 rfl⟩⟩
    rintro ⟨w, hw, hc⟩
    rw [(isComb_iff_eq hu cf _).1 hc] at hw
    exact hw
  · refine Fintype.linearIndependent_iff.2 fun c hc k => ?_
    have := hinj c 0 _ ((isComb_iff_eq hu c _).2 rfl) ((isComb_iff_eq hu 0 _).2 (by rw [hc]; simp))
    exact congrFun this k
  · intro c hc
    exact hsub ((hL c _ ((isComb_iff_eq hv c _).2 rfl)).2 hc)
  · intro w hw
    have h := hHT E H X t p C.S C.norm_p xO huniq _ (hsup hw) (p : C.S) hpa
    obtain ⟨c, hc⟩ := h1 ((p : C.S) • w)
    refine ⟨c, (hL c _ ((isComb_iff_eq hv c _).2 rfl)).1 ?_, hc⟩
    rw [← hc]
    exact h

end GlobalTheory.GrNormPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPulledTraitPointField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ToricOverField

theorem unitOn_val_map {U B : Type} [CommRing U] [CommRing B] (w : U →+* B) (x : Uˣ) (y : Bˣ)
    (h : (y : B) = w x) : (unitOn y).val = (spMap w).appTop.hom (unitOn x).val := by
  have k := congrArg (fun φ => φ.hom (x : U)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom w))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at k
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (y : B) = _
  rw [h]
  exact k

theorem exists_point {A B X : Type} [CommRing A] [CommRing B] [AddCommGroup X] (f : A →+* B)
    (τ : Multiplicative X →* Bˣ) : ∃ z : Over.mk (spMap f) ⟶ splitTorus (Sp A) X,
      ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ)) := by
  refine ⟨(GlobalTheory.splitTorusPointsEquiv (Sp A) X (Over.mk (spMap f))).symm
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom).comp τ), fun χ => ?_⟩
  rw [GlobalTheory.UU.chV, MulEquiv.apply_symm_apply]
  rfl

theorem toric_section_eq_over_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W]
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (k : ℕ)
    (s' : ∀ (A : Type) [CommRing A] (a : W →+* A) (τ : Multiplicative P'.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t'.G)),
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : W →+* A) (ha : ∀ x ∈ maximalIdeal W, a x = 0) (a' : W →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t' (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P'.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s' A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P' ha m₀).left ≫ m₀.φ) →
    ∀ (R : Type) [CommRing R] (t : SAB H (Sp R)) (g : R →+* W) (m : SABMap t' t (spMap g))
      (V : Type) [CommRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
      (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
      (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G),
      GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
      n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (Ω' : Type) [Field Ω'] (σ : Ω →+* Ω') (a' : W →+* Ω'), a' = σ.comp β →
    ∀ (U : Type) [CommRing U] (u : V →+* U) (w : U →+* Ω'), w.comp u = σ.comp α →
    ∀ (τU : Multiplicative P'.D.toPre.X →* Uˣ) (τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ) (h : τ'' ^ k = 1),
      (∀ χ, (τ'' χ : Ω') = w (τU χ : U)) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s' Ω' a' τ'' h).left ≫ m.φ = spMap w ≫ (z ≫ j).left ≫ mV.φ := by
  intro E _ _ _ H W _ _ _ t' P' k s' hs R _ t g m V _ ψ tV mV Ω _ α β hβ tΩ n n' j hj hn
    Ω' _ σ a' ha' U _ u w hw τU τ'' h hτ z hz
  obtain ⟨z', hz'⟩ := exists_point σ τ''
  have key : z'.left ≫ SplitTorus.bcMap (spMap α) P'.D.toPre.X = spMap w ≫ z.left := by
    refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [Category.assoc, SplitTorus.bcMap_hom, ← Category.assoc, Over.w z', Category.assoc, Over.w z]
      change spMap σ ≫ spMap α = spMap w ≫ spMap u
      simp only [spMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hw]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
        Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      have e1 := (GlobalTheory.UU.chV_val z' χ).symm.trans (congrArg Units.val (hz' χ))
      have e2 := (GlobalTheory.UU.chV_val z χ).symm.trans (congrArg Units.val (hz χ))
      exact e1.trans ((unitOn_val_map w _ _ (hτ _)).trans (congrArg _ e2.symm))
  rw [hs Ω Ω' β hβ a' σ tΩ n' τ'' h z' ha' hz', ← hj, Category.assoc, ← hn, Over.comp_left, Over.comp_left,
    Category.assoc, ← Category.assoc _ n.φ, GlobalTheory.TorusPart.pullTorus_left, Category.assoc,
    ← Category.assoc z'.left, key]
  simp only [Category.assoc]

end GlobalTheory.ToricOverField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivialMonodromyOrbitConvergesSymmetricDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (x : ℂ → Frame X.Ψ N), IsOrbit X T M 1 x → ∃ x₀ ∈ X.dom, ∃ x' : ℂ → Frame X.Ψ N, Tendsto x' imTop (𝓝 x₀) ∧ ∀ᶠ w in imTop, x' w ∈ X.dom ∧ SamePos X (x w) (x' w) := by
  first | exact @GlobalTheory.ShFam.OrbitLimit.orbit_limit | exact GlobalTheory.ShFam.OrbitLimit.orbit_limit | (intros; apply GlobalTheory.ShFam.OrbitLimit.orbit_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartLevelCharactersRationalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chain_chart_level_characters_rational : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch),
    V4.MuIsW (w.st Z) f T Wt w.I.xi →
    ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
    ∀ (u : (w.D Z).what₂.Word) (μ : (w.D Z).what₂.Tup) (hμ : μ ≠ (w.D Z).what₂.mu0) (j : ℕ) (hj : j + 1 ≤ (w.D Z).R.m)
      (β : tt.ch.Ch u μ (j + 1)),
      Formalism.L2.G.Cmp.ChiRatAll (tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (w.D Z).what₂.embLL := by
  first | exact @GlobalTheory.ChiRatStd.chiRatAll_twChart | exact GlobalTheory.ChiRatStd.chiRatAll_twChart | (intros; apply GlobalTheory.ChiRatStd.chiRatAll_twChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyDataStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_triple_fibres_base_change_key_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Nontrivial S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S) (z : FrPt Xo c S') (Φ : FibKey Xo S y.x) (Φ' : FibKey Xo S' z.x), FrMap φ y z → Tied e y.s y.u Φ → Tied e z.s z.u Φ' → KeyPB Φ'.key Φ.key φ.toRingHom := by
  first | exact @GlobalTheory.KeyFourth.tied_keyPB | exact GlobalTheory.KeyFourth.tied_keyPB | (intros; apply GlobalTheory.KeyFourth.tied_keyPB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedAdelicDataSaturatedOverFixedFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 → StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok) (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧ (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧ ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | exact GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | (intros; apply GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSignStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  first | exact @GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | exact GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | (intros; apply GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight <;> assumption)
end

