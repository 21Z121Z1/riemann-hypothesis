import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0333
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelPreservesCofilteredLimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

lemma cechLev_π {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) (j : Fin (k.unop.len + 1)) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫ WidePullback.π (fun _ => g.hom) j =
      WidePullback.π (fun _ => f.hom) j ≫ F.left := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_π]

lemma cechLev_base {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫
        WidePullback.base (fun _ : Fin (k.unop.len + 1) => g.hom) =
      WidePullback.base (fun _ => f.hom) ≫ F.right := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_base]

theorem cech_level_limit (I : Type) [SmallCategory I] [IsCofiltered I] (A : I ⥤ Arrow PSh) (cA : Cone A)
    (hl : IsLimit (Arrow.leftFunc.mapCone cA)) (_hA : ∀ ⦃i j : I⦄ (f : i ⟶ j), IsIso (A.map f).right)
    (hR : ∀ i, IsIso (cA.π.app i).right) (k : SimplexCategoryᵒᵖ) :
    Nonempty (IsLimit (((evaluation _ PSh).obj k).mapCone (SimplicialObject.cechNerve.mapCone cA))) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  let L : ∀ (s : Cone ((A ⋙ SimplicialObject.cechNerve) ⋙ (evaluation _ PSh).obj k))
      (j : Fin (k.unop.len + 1)), s.pt ⟶ cA.pt.left := fun s j =>
    hl.lift
      { pt := s.pt
        π :=
          { app := fun i => s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j
            naturality := by
              intro i i' f
              have h := s.w f
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                Functor.comp_obj, Arrow.leftFunc_obj, Functor.comp_map, Arrow.leftFunc_map] at h ⊢
              rw [← h]
              exact (Category.assoc _ _ _).trans
                ((congrArg (s.π.app i ≫ ·) (cechLev_π (A.map f) k j)).trans (Category.assoc _ _ _).symm) } }
  have hLfac : ∀ s j i, L s j ≫ (cA.π.app i).left =
      s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j := by
    intro s j i
    exact hl.fac _ i
  have hLbase : ∀ s j i, L s j ≫ cA.pt.hom ≫ (cA.π.app i).right =
      s.π.app i ≫ WidePullback.base (fun _ : Fin (k.unop.len + 1) => (A.obj i).hom) := by
    intro s j i
    have hw : (cA.π.app i).left ≫ (A.obj i).hom = cA.pt.hom ≫ (cA.π.app i).right := Arrow.w (cA.π.app i)
    rw [← hw, ← Category.assoc, hLfac]
    exact (Category.assoc _ _ _).trans (congrArg (s.π.app i ≫ ·) (WidePullback.π_arrow _ j))
  refine ⟨{ lift := fun s => WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) (fun j => by
              rw [← cancel_mono (cA.π.app i₀).right, Category.assoc, Category.assoc, hLbase, hLbase])
            fac := ?_
            uniq := ?_ }⟩
  · intro s i
    apply WidePullback.hom_ext
    · intro j
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_π (cA.π.app i) k j)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).left) (WidePullback.lift_π _ _ _ _ j)).trans ?_
      exact hLfac s j i
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_base (cA.π.app i) k)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).right) (WidePullback.lift_base _ _ _ _)).trans ?_
      exact (Category.assoc _ _ _).trans (hLbase s 0 i)
  · intro s m hm
    have hmj : ∀ j, m ≫ WidePullback.π (fun _ => cA.pt.hom) j = L s j := by
      intro j
      apply hl.hom_ext
      intro i
      refine Eq.trans ?_ (hLfac s j i).symm
      refine Eq.trans ?_ (congrArg (· ≫ WidePullback.π (fun _ => (A.obj i).hom) j) (hm i))
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (cechLev_π (cA.π.app i) k j).symm
    apply WidePullback.hom_ext
    · intro j
      exact (hmj j).trans (WidePullback.lift_π _ _ _ _ j).symm
    · refine Eq.trans ?_ (WidePullback.lift_base _ _ _ _).symm
      refine Eq.trans ?_ (congrArg (· ≫ cA.pt.hom) (hmj 0))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (WidePullback.π_arrow _ 0).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta : ∀ (R : Type) [CommRing R] , (∀ E : Spc, ((chains R).obj E).IsStrictlyLE 0) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (p : ℕ), ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom = (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p)))) ∧ ∀ (E : Spc) (p : ℕ), (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
  first | (exact @GlobalTheory.EtC.chains_basic) | (exact GlobalTheory.EtC.chains_basic) | (intros; apply GlobalTheory.EtC.chains_basic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
open Simplicial SimplicialObject.Augmented
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EtC.CechSplit

variable {P Q : PSh} (φ : P ⟶ Q) (hφ : ∀ U, Function.Surjective (φ.app U)) (U : Scheme.{0})

def lft (c : yoneda.obj U ⟶ Q) : yoneda.obj U ⟶ P :=
  yonedaEquiv.symm (hφ (op U) (yonedaEquiv c)).choose

@[reassoc (attr := simp)]
lemma lft_comp (c : yoneda.obj U ⟶ Q) : lft φ hφ U c ≫ φ = c := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, lft, Equiv.apply_symm_apply]
  exact (hφ (op U) (yonedaEquiv c)).choose_spec

def sf (n : ℕ) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n + 1⦌) :=
  WidePullback.lift (x ≫ WidePullback.base _)
    (Fin.cases (lft φ hφ U (x ≫ WidePullback.base _)) (fun i => x ≫ WidePullback.π _ i))
    (fun i => by cases i using Fin.cases <;> simp)

def sf' (c : yoneda.obj U ⟶ Q) : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋0⦌) :=
  lft φ hφ U c ≫ WidePullback.lift φ (fun _ => 𝟙 P) (by simp)

lemma sf'_comp_aug (c : yoneda.obj U ⟶ Q) : sf' φ hφ U c ≫ (Arrow.mk φ).augmentedCechNerve.hom.app (op ⦋0⦌) = c := by
  simp [sf']

lemma sf_zero_comp_δ_one (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋0⦌)) :
    sf φ hφ U 0 x ≫ (Arrow.mk φ).cechNerve.δ 1 =
      sf' φ hφ U (x ≫ (Arrow.mk φ).augmentedCechNerve.hom.app (op ⦋0⦌)) := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf, sf']
  ext j
  · fin_cases j
    simp
  · simp

lemma sf_comp_δ_zero (n : ℕ) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    sf φ hφ U n x ≫ (Arrow.mk φ).cechNerve.δ 0 = x := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf]
  ext j
  · simp
  · simp

lemma sf_succ_comp_δ_succ (n : ℕ) (i : Fin (n + 2)) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n + 1⦌)) :
    sf φ hφ U (n + 1) x ≫ (Arrow.mk φ).cechNerve.δ i.succ = sf φ hφ U n (x ≫ (Arrow.mk φ).cechNerve.δ i) := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf]
  ext j
  · induction j using Fin.cases <;> simp
  · simp

lemma sf_comp_σ_succ (n : ℕ) (i : Fin (n + 1)) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    sf φ hφ U n x ≫ (Arrow.mk φ).cechNerve.σ i.succ = sf φ hφ U (n + 1) (x ≫ (Arrow.mk φ).cechNerve.σ i) := by
  dsimp [SimplicialObject.σ, SimplexCategory.σ, sf]
  ext j
  · induction j using Fin.cases <;> simp
  · simp

def ed : ExtraDegeneracy (((whiskering _ _).obj (coyoneda.obj (op (yoneda.obj U)))).obj
    (Arrow.mk φ).augmentedCechNerve) where
  s' := TypeCat.ofHom (sf' φ hφ U)
  s n := TypeCat.ofHom (sf φ hφ U n)
  s'_comp_ε := by ext c; exact sf'_comp_aug φ hφ U c
  s₀_comp_δ₁ := by ext x; exact sf_zero_comp_δ_one φ hφ U x
  s_comp_δ₀ n := by ext x; exact sf_comp_δ_zero φ hφ U n x
  s_comp_δ n i := by ext x; exact sf_succ_comp_δ_succ φ hφ U n i x
  s_comp_σ n i := by ext x; exact sf_comp_σ_succ φ hφ U n i x

def toConst : (Arrow.mk φ).augmentedCechNerve ⟶ SimplicialObject.Augmented.const.obj Q where
  left := (Arrow.mk φ).augmentedCechNerve.hom
  right := 𝟙 Q
  w := by ext : 1; simp

include hφ in
theorem free_sections_quasiIso (R : Type) [CommRing R] :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map
      (((SimplicialObject.whiskering _ _).obj ((evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙
        ModuleCat.free (ULift.{1} R))).map
          (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from (Arrow.mk φ).augmentedCechNerve.hom))) := by
  let G : PSh ⥤ ModuleCat.{1} (ULift.{1} R) :=
    (evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R)
  let X := (Arrow.mk φ).augmentedCechNerve
  let e1 : coyoneda.obj (op (yoneda.obj U)) ⋙ ModuleCat.free (ULift.{1} R) ≅ G :=
    Functor.isoWhiskerRight (largeCurriedYonedaLemma.app (op U)) (ModuleCat.free (ULift.{1} R))
  let ed0 : ExtraDegeneracy (((whiskering _ _).obj (coyoneda.obj (op (yoneda.obj U)) ⋙
      ModuleCat.free (ULift.{1} R))).obj X) := (ed φ hφ U).map (ModuleCat.free (ULift.{1} R))
  let ed1 : ExtraDegeneracy (((whiskering _ _).obj G).obj X) :=
    ed0.ofIso (((whiskering _ _).mapIso e1).app X)
  have h1 := ed1.homotopyEquiv.quasiIso_hom
  have h2 := ((ExtraDegeneracy.const Q).map G).homotopyEquiv.quasiIso_hom
  have nat := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := ModuleCat.{1} (ULift.{1} R))).naturality
    (((whiskering _ _).obj G).map (toConst φ))
  have hp : (point ⋙ ChainComplex.single₀ _).map (((whiskering _ _).obj G).map (toConst φ)) = 𝟙 _ := by
    change (ChainComplex.single₀ _).map (G.map (𝟙 Q)) = 𝟙 _
    rw [G.map_id, CategoryTheory.Functor.map_id]
  rw [hp, Category.comp_id] at nat
  haveI : QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q))) := h2
  rw [← quasiIso_iff_comp_right _ (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q)))]
  have key : QuasiIso ((drop ⋙ AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map
        (((whiskering _ _).obj G).map (toConst φ)) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q))) := by
    rw [nat]; exact h1
  exact key

end GlobalTheory.EtC.CechSplit

namespace GlobalTheory.EtC

theorem chains_cechNerve_quasiIso_of_surjective : ∀ (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q),
    (∀ U, Function.Surjective (φ.app U)) →
      QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from
        (Arrow.mk φ).augmentedCechNerve.hom)) := by
  intro R _ P Q φ hφ
  exact chains_quasiIso_of_sections R _ (fun U => CechSplit.free_sections_quasiIso φ hφ U R)

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ n : ℤ, Injective ((res R F).X n)) ∧ (∀ n : ℤ, n < 0 → IsZero ((res R F).X n)) ∧ Mono (resι R F) ∧ (∃ w : resι R F ≫ (res R F).d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧ (∀ n : ℤ, n ≠ 0 → (res R F).ExactAt n) ∧ ∀ (E : Spc) (n : ℤ), 0 < n → IsZero (((chains R).obj E).X n) := by
  first | exact @GlobalTheory.EtC.res_basic | exact GlobalTheory.EtC.res_basic | (intros; apply GlobalTheory.EtC.res_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧ (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧ resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G), resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧ resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  first | exact @GlobalTheory.EtC.ResBasic.res_basic | exact GlobalTheory.EtC.ResBasic.res_basic | (intros; apply GlobalTheory.EtC.ResBasic.res_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosurePrimeRegularHeight
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_prime_regular_height : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∀ (Q : Ideal (GlobalTheory.KeyOriginNoeth.closure A R D)) [Q.IsPrime],
      (∀ a : A, a ≠ 0 → algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a) ∉ Q) →
      Algebra.IsEtaleAt R Q := by
  first | (exact @GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint) | (exact GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint) | (intros; apply GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycleCompHomComplex_assoc_on_cohomology_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  first | (exact @GlobalTheory.cocycle_comp_assoc_classes) | (exact GlobalTheory.cocycle_comp_assoc_classes) | (intros; apply GlobalTheory.cocycle_comp_assoc_classes  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleEqChainMapShiftCompatClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_eq_chainMap_shift_compat_classes : ∀ (R : Type) [CommRing R] (L C : Cx R) (d : ℤ) (ψ : Cocycle L C d), ∃ (L' : Cx R) (g : L' ⟶ C), (∀ m, L.IsStrictlyGE m → L'.IsStrictlyGE (m + d)) ∧ ((∀ n, CategoryTheory.Injective (L.X n)) → ∀ n, CategoryTheory.Injective (L'.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : CohomologyClass K L (n - d) ≃ CohomologyClass K L' n, ∀ a, cpush K g n (e a) = cpost K ψ (n - d) n (by omega) a := by
  first | (exact @GlobalTheory.EtC.cocycle_as_chainMap_of_shift) | (exact GlobalTheory.EtC.cocycle_as_chainMap_of_shift) | (intros; apply GlobalTheory.EtC.cocycle_as_chainMap_of_shift  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spcᵒᵖ) (n : ℤ), n < 0 → IsZero (((HC R F).obj E).X n)) ∧ ∃ cl : ∀ (E : Spc) (n : ℤ) (z : ((HC R F).obj (op E)).X n), ((HC R F).obj (op E)).d n (n + 1) z = 0 → H R E F n, (∀ E n x, ∃ z hz, cl E n z hz = x) ∧ (∀ E n z hz z' hz', cl E n z hz = cl E n z' hz' ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = z' + ((HC R F).obj (op E)).d (n - 1) n y) ∧ (∀ E n z hz, cl E n z hz = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = ((HC R F).obj (op E)).d (n - 1) n y) ∧ ∀ (E E' : Spc) (f : E ⟶ E') n z hz, ∃ h, pull R f F n (cl E' n z hz) = cl E n (((HC R F).map f.op).f n z) h := by
  first | exact @GlobalTheory.EtC.HCElements.main | exact GlobalTheory.EtC.HCElements.main | (intros; apply GlobalTheory.EtC.HCElements.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvariantOfLocallyConstantTwistStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinvariant_of_locally_constant_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (R : Finset (GL (Fin a) k)),
    Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) → IsLocallyConstant χ →
    (∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y) →
    (∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) → Φ ∈ coinv ν β a (a + b) := by
  first | exact @GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | exact GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | (intros; apply GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantDiagonalBlockUnitLowerPos
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.ColGramPos

open scoped ComplexOrder

theorem blkW_upper {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i j : Fin (r - 1)) (h : i < j) :
    blkW p0 w i j = 0 := by
  have h' : (i : ℕ) < j := h
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dif_neg (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]
  · unfold lowMat
    rw [dif_neg (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]

theorem blkW_diag {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i : Fin (r - 1)) :
    blkW p0 w i i = 1 := by
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dif_neg (lt_irrefl _), if_pos rfl]
  · unfold lowMat
    rw [dif_neg (lt_irrefl _), if_pos rfl]

theorem lowerTri_det_one {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ i j, i < j → T i j = 0) (hd : ∀ i, T i i = 1) : T.det = 1 := by
  rw [Matrix.det_of_lowerTriangular T (fun i j hij => hu i j hij)]
  simp [hd]

theorem colGram_blkW_pos : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  intro r p0 w k
  set B := blkW p0 w with hB
  have hk : (k : ℕ) ≤ r - 1 := Nat.le_of_lt_succ k.isLt
  set N : Matrix (Fin (r - 1)) (Fin k) ℂ := B.submatrix id (Fin.castLE hk) with hN
  have hsub : (Bᴴ * B).submatrix (Fin.castLE hk) (Fin.castLE hk) = Nᴴ * N := by
    ext a b
    simp [N, Matrix.mul_apply, Matrix.conjTranspose_apply]
  set T : Matrix (Fin k) (Fin k) ℂ := B.submatrix (Fin.castLE hk) (Fin.castLE hk) with hT
  have hTdet : T.det = 1 := by
    apply lowerTri_det_one
    · intro i j hij
      exact blkW_upper p0 w _ _ (by rw [Fin.lt_def] at hij ⊢; simpa using hij)
    · intro i
      exact blkW_diag p0 w _
  have hinj : Function.Injective N.mulVec := by
    intro u v huv
    have h0 : N *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have hT0 : T *ᵥ (u - v) = 0 := by
      ext i
      have := congrFun h0 (Fin.castLE hk i)
      simpa [T, N, Matrix.mulVec, dotProduct] using this
    have := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hTdet]; exact one_ne_zero) hT0
    exact sub_eq_zero.mp this
  have hpd : (Nᴴ * N).PosDef := Matrix.PosDef.conjTranspose_mul_self N hinj
  have hdet : (Nᴴ * N).det ≠ 0 := hpd.det_pos.ne'
  unfold colGram lminor
  rw [hsub]
  exact norm_pos_iff.mpr hdet

end GlobalTheory.IntBall.ColGramPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerBlockLastEqOne
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem blkW_det_eq_one (r p0 : ℕ) (w : Low r → ℂ) : (blkW p0 w).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [blkW, lowMat]
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    simp only [blkW, lowMat]
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals first
      | rfl
      | (exfalso; simp only [Fin.lt_def, Fin.ext_iff] at *; omega)

theorem colGram_blkW_last (r p0 : ℕ) (w : Low r → ℂ) :
    colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  unfold colGram lminor
  have : (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r - 1)).isLt) : Fin (r - 1) → Fin (r - 1)) = id := by
    funext i; ext; simp
  rw [this, Matrix.submatrix_id_id, Matrix.det_mul, Matrix.det_conjTranspose, blkW_det_eq_one]
  simp

theorem colGramLast : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 :=
  colGram_blkW_last

end GlobalTheory.IntBall
end

