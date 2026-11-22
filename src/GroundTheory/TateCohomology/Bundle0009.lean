import Mathlib
import GroundTheory.TateCohomology.Bundle0007
import GroundTheory.TateCohomology.Bundle0005

-- bundled from GroundTheory.TateCohomology.ResCoresPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

universe u

section Incl

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

noncomputable def barInclF (n : ℕ) :
    free k S (Fin n → S) ⟶ res S.subtype (free k G (Fin n → G)) :=
  freeLift k S (res S.subtype (free k G (Fin n → G)))
    (fun v => Finsupp.single (S.subtype ∘ v) (MonoidAlgebra.single (1 : G) (1 : k)))

set_option backward.isDefEq.respectTransparency false in
lemma barInclF_single (n : ℕ) (v : Fin n → S) (s : S) (r : k) :
    (barInclF S n).hom (Finsupp.single v (MonoidAlgebra.single s r)) =
      Finsupp.single (S.subtype ∘ v) (MonoidAlgebra.single (s : G) r) := by
  simp [barInclF]

omit [Group G] in
lemma contractNth_subtype {G : Type u} [Group G] (S : Subgroup G) {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → S) :
    j.contractNth (· * ·) (Subtype.val ∘ x) = S.subtype ∘ j.contractNth (· * ·) x := by
  funext i
  simp only [Fin.contractNth, Function.comp_apply]
  split_ifs <;> simp

set_option backward.isDefEq.respectTransparency false in
lemma barInclF_comm (j : ℕ) :
    barInclF S (j + 1) ≫ (resFunctor S.subtype).map (barComplex.d k G j) =
      barComplex.d k S j ≫ barInclF S j := by
  refine free_ext _ _ _ _ _ fun x => ?_
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [barInclF_single, barComplex.d_single]
  rw [Rep.resMap_hom_apply, OneMemClass.coe_one, barComplex.d_single]
  rw [map_add, map_sum, barInclF_single]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
  rw [barInclF_single, OneMemClass.coe_one]
  exact congrArg (fun v => Finsupp.single v _) (contractNth_subtype S i x)

set_option backward.isDefEq.respectTransparency false in

noncomputable def barIncl :
    (barResolution k S).complex ⟶ (resBarResolution (k := k) S).complex where
  f n := barInclF S n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    have h := barInclF_comm (k := k) S j
    simp only [resBarResolution, Functor.mapProjectiveResolution,
      Functor.mapHomologicalComplex_obj_d]
    show barInclF S (j + 1) ≫ resMap S.subtype ((barComplex k G).d (j + 1) j) =
      (barComplex k S).d (j + 1) j ≫ barInclF S j
    rw [barComplex.d_def, barComplex.d_def]
    exact h

set_option backward.isDefEq.respectTransparency false in

lemma barIncl_π : barIncl (k := k) S ≫ (resBarResolution (k := k) S).π = (barResolution k S).π := by
  ext : 1
  refine free_ext _ _ _ _ _ fun x => ?_
  simp only [barIncl, resBarResolution, Functor.mapProjectiveResolution, HomologicalComplex.comp_f,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  simp
  erw [barInclF_single]
  erw [barResolution_π_f_zero_single (k := k) (G := G)]
  erw [barResolution_π_f_zero_single (k := k) (G := S)]

noncomputable def barInclHomotopy :
    Homotopy ((barHomotopyEquiv (k := k) S).inv ≫ barIncl S) (𝟙 _) :=
  ProjectiveResolution.liftHomotopy (𝟙 _) _ _
    (by rw [Category.assoc, barIncl_π, barHomotopyEquiv, ProjectiveResolution.homotopyEquiv_inv_π,
      CategoryTheory.Functor.map_id, Category.comp_id])
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp])

end Incl

section Key

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

set_option backward.isDefEq.respectTransparency false in

noncomputable def resHomComplex (A : Rep.{u} k G) :
    (barComplex k G).linearYonedaObj k A ⟶
      (resBarResolution (k := k) S).complex.linearYonedaObj k (res S.subtype A) where
  f n := ModuleCat.ofHom
    { toFun := fun f => (resFunctor S.subtype).map f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm' i j hij := by
    ext f
    simp [resBarResolution, Functor.mapProjectiveResolution]
    rfl

set_option backward.isDefEq.respectTransparency false in

lemma freeLift_cochainsMap_subtype (A : Rep.{u} k G) (n : ℕ) (y : (Fin n → G) → A) :
    freeLift k S (res S.subtype A) (((cochainsMap S.subtype (𝟙 (res S.subtype A))).f n).hom y) =
      barInclF S n ≫ (resFunctor S.subtype).map (freeLift k G A y) := by
  refine free_ext _ _ _ _ _ fun w => ?_
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [barInclF_single]
  simp [cochainsMap_f_hom]
  exact (show (freeLift k G A y).hom (Finsupp.single (Subtype.val ∘ w) (MonoidAlgebra.single 1 1)) =
    y (Subtype.val ∘ w) by simp).symm

set_option backward.isDefEq.respectTransparency false in

lemma cochainsMap_subtype_comp_iso (A : Rep.{u} k G) :
    cochainsMap S.subtype (𝟙 (res S.subtype A)) ≫ (inhomogeneousCochainsIso (res S.subtype A)).hom =
      (inhomogeneousCochainsIso A).hom ≫ resHomComplex S A ≫
        linearYonedaObjMap (barIncl (k := k) S) (res S.subtype A) := by
  ext n y : 3
  exact freeLift_cochainsMap_subtype S A n y

set_option backward.isDefEq.respectTransparency false in

lemma iso_resHomComplex_adj_iso (A : Rep.{u} k G) :
    (inhomogeneousCochainsIso A).hom ≫ resHomComplex S A ≫
      (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
        (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv =
      cochainsMap (MonoidHom.id G) ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A) := by
  ext n y : 3
  funext v
  refine Subtype.ext (funext fun g => ?_)
  change ((resCoindToHom S.subtype ((barResolution k G).complex.X n) (res S.subtype A)
      ((resFunctor S.subtype).map (freeLift k G A y))).hom
        (Finsupp.single v (MonoidAlgebra.single 1 1))).1 g =
    ((resCoindToHom S.subtype A (res S.subtype A) (𝟙 _)).hom (y v)).1 g
  rw [resCoindToHom_hom_apply_coe, resCoindToHom_hom_apply_coe]
  change (A.ρ.freeLift y) ((Representation.free k G (Fin n → G)) g
    (Finsupp.single v (MonoidAlgebra.single 1 1))) = _
  simp

theorem homologyMap_cochainsMap_unit (A : Rep.{u} k G) (n : ℕ) :
    HomologicalComplex.homologyMap (cochainsMap (MonoidHom.id G)
        ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)) n =
      groupCohomology.map S.subtype (𝟙 (res S.subtype A)) n ≫
        HomologicalComplex.homologyMap (shapiroCochainsHomotopyEquiv S (res S.subtype A)).hom n := by
  have H := ((linearYonedaObjHomotopy (R := k) (barInclHomotopy (k := k) S)
    (res S.subtype A)).compRight
      ((linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
        (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv)).compLeft
    ((inhomogeneousCochainsIso A).hom ≫ resHomComplex S A)
  have e1 : ((inhomogeneousCochainsIso A).hom ≫ resHomComplex S A) ≫
      linearYonedaObjMap ((barHomotopyEquiv (k := k) S).inv ≫ barIncl S) (res S.subtype A) ≫
        (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
          (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv =
      cochainsMap S.subtype (𝟙 (res S.subtype A)) ≫
        (shapiroCochainsHomotopyEquiv S (res S.subtype A)).hom := by
    calc _ = ((inhomogeneousCochainsIso A).hom ≫ resHomComplex S A ≫
            linearYonedaObjMap (barIncl (k := k) S) (res S.subtype A)) ≫
          linearYonedaObjMap (barHomotopyEquiv (k := k) S).inv (res S.subtype A) ≫
            (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
              (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv := by
          rw [linearYonedaObjMap_comp]; simp only [Category.assoc]
      _ = (cochainsMap S.subtype (𝟙 (res S.subtype A)) ≫
            (inhomogeneousCochainsIso (res S.subtype A)).hom) ≫
          linearYonedaObjMap (barHomotopyEquiv (k := k) S).inv (res S.subtype A) ≫
            (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
              (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv :=
          congrArg (· ≫ _) (cochainsMap_subtype_comp_iso S A).symm
      _ = _ := by simp only [Category.assoc]; rfl
  have e2 : ((inhomogeneousCochainsIso A).hom ≫ resHomComplex S A) ≫
      linearYonedaObjMap (𝟙 _) (res S.subtype A) ≫
        (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
          (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv =
      cochainsMap (MonoidHom.id G) ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A) := by
    rw [linearYonedaObjMap_id, Category.id_comp, Category.assoc]
    exact iso_resHomComplex_adj_iso S A
  rw [← e2, ← H.homologyMap_eq, e1, HomologicalComplex.homologyMap_comp]
  rfl

end Key

section Compare

lemma comp_cancel_of_isos {C : Type*} [Category C] {X X' Y Y' Z Z' : C} (pG : X ≅ X') (pS : Y ≅ Y')
    (pGc : Z ≅ Z') (a : X ⟶ Z) (cu : X' ⟶ Z') (m : X' ⟶ Y') (sh : Y' ⟶ Z') (b : Y ⟶ Z) (c : Z ⟶ Y)
    (ha : a = pG.hom ≫ cu ≫ pGc.inv) (hcu : cu = m ≫ sh) (hsh : sh = pS.inv ≫ b ≫ pGc.hom)
    (hb : b ≫ c = 𝟙 Y) : a ≫ c ≫ pS.hom = pG.hom ≫ m := by
  subst ha hcu hsh
  simp [reassoc_of% hb]

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

theorem tateRes_comp_isoGroupCohomology (n : ℕ) [NeZero n] (A : Rep.{u} k G) :
    (tateRes S n).app A ≫ (TateCohomology.isoGroupCohomology n).hom.app (res S.subtype A) =
      (TateCohomology.isoGroupCohomology n).hom.app A ≫
        groupCohomology.map S.subtype (𝟙 (res S.subtype A)) n := by
  have h1 : HomologicalComplex.homologyMap
      (tateComplex.map ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)) n =
      ((tateComplexConnectData A).homologyIsoPos n n rfl).hom ≫
        HomologicalComplex.homologyMap (cochainsMap (MonoidHom.id G)
          ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)) n ≫
        ((tateComplexConnectData (coind S.subtype (res S.subtype A) : Rep.{u} k G)).homologyIsoPos
          n n rfl).inv :=
    CochainComplex.ConnectData.homologyMap_map_of_eq_succ _ _ _ _ _ n n rfl
  have h2 : HomologicalComplex.homologyMap (tateShapiroMap S (res S.subtype A)) n = _ :=
    CochainComplex.ConnectData.homologyMap_map_of_eq_succ
    (tateComplexConnectData (res S.subtype A))
    (tateComplexConnectData (coind S.subtype (res S.subtype A) : Rep.{u} k G))
    (groupHomology.chainsMap S.subtype (toResCoind S (res S.subtype A)))
    (shapiroCochainsHomotopyEquiv S (res S.subtype A)).hom (shapiro_comm_zero S (res S.subtype A))
    n n rfl
  have hb := homologyMap_tateShapiroMap_comp_tateCoindIso_hom S (res S.subtype A) n
  have h2' : HomologicalComplex.homologyMap (shapiroCochainsHomotopyEquiv S (res S.subtype A)).hom n =
      ((tateComplexConnectData (res S.subtype A)).homologyIsoPos n n rfl).inv ≫
        HomologicalComplex.homologyMap (tateShapiroMap S (res S.subtype A)) n ≫
          ((tateComplexConnectData (coind S.subtype (res S.subtype A) : Rep.{u} k G)).homologyIsoPos n n rfl).hom := by
    rw [h2]; simp
  rw [tateRes_app, Category.assoc]
  show HomologicalComplex.homologyMap
      (tateComplex.map ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)) n ≫
        (tateCoindIso S (res S.subtype A) n).hom ≫
          ((tateComplexConnectData (res S.subtype A)).homologyIsoPos n n rfl).hom =
      ((tateComplexConnectData A).homologyIsoPos n n rfl).hom ≫
        groupCohomology.map S.subtype (𝟙 (res S.subtype A)) n
  exact comp_cancel_of_isos _ _ _ _ _ _ _ _ _ h1 (homologyMap_cochainsMap_unit S A n) h2' hb

end Compare

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.TateTransport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology groupHomology

universe u

variable {k H K : Type u} [CommRing k] [Group H] [Group K]

section Complex

variable (e : H ≃* K)

noncomputable def transportChainsMor (B : Rep.{u} k K) :
    B ⟶ res (e.symm : K →* H) (res (e : H →* K) B) :=
  Rep.ofHom ⟨LinearMap.id, fun x => by
    ext b
    simp⟩

@[simp]
lemma transportChainsMor_hom_apply (B : Rep.{u} k K) (b : B) :
    (transportChainsMor e B).hom b = b := rfl

variable [Fintype H] [Fintype K]

lemma transport_comm_zero (B : Rep.{u} k K) :
    (chainsMap (e.symm : K →* H) (transportChainsMor e B)).f 0 ≫
        (tateComplexConnectData (res (e : H →* K) B)).d₀ =
      (tateComplexConnectData B).d₀ ≫ (cochainsMap (e : H →* K) (𝟙 _)).f 0 := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun v b => ?_)
  refine funext fun w => ?_
  have e1 : ((tateComplexConnectData B).d₀).hom (Finsupp.single v b) = fun _ => B.ρ.norm b := by
    simp [Rep.tateNorm_eq]
    rfl
  have e2 : ((tateComplexConnectData (res (e : H →* K) B)).d₀).hom
      (((chainsMap (e.symm : K →* H) (transportChainsMor e B)).f 0).hom (Finsupp.single v b)) =
      fun _ => (res (e : H →* K) B).ρ.norm b := by
    rw [chainsMap_f_single]
    simp [Rep.tateNorm_eq]
    rfl
  change ((tateComplexConnectData (res (e : H →* K) B)).d₀).hom
      (((chainsMap (e.symm : K →* H) (transportChainsMor e B)).f 0).hom (Finsupp.single v b)) w =
    ((cochainsMap (e : H →* K) (𝟙 _)).f 0).hom
      (((tateComplexConnectData B).d₀).hom (Finsupp.single v b)) w
  rw [e1, e2, norm_res_of_bijective (e : H →* K) e.bijective]
  rfl

noncomputable def tateTransportComplex (B : Rep.{u} k K) :
    tateComplex B ⟶ tateComplex (res (e : H →* K) B) :=
  CochainComplex.ConnectData.map _ _ (chainsMap (e.symm : K →* H) (transportChainsMor e B))
    (cochainsMap (e : H →* K) (𝟙 _)) (transport_comm_zero e B)

lemma tateTransportComplex_naturality {B B' : Rep.{u} k K} (φ : B ⟶ B') :
    tateTransportComplex e B ≫ tateComplex.map ((resFunctor (e : H →* K)).map φ) =
      tateComplex.map φ ≫ tateTransportComplex e B' := by
  ext (m | m) : 1
  · rfl
  · change (chainsMap (e.symm : K →* H) (transportChainsMor e B) ≫ chainsMap (MonoidHom.id H)
      ((resFunctor (e : H →* K)).map φ)).f m = (chainsMap (MonoidHom.id K) φ ≫
        chainsMap (e.symm : K →* H) (transportChainsMor e B')).f m
    rw [← chainsMap_comp, ← chainsMap_comp]
    congr 1

@[simps]
noncomputable def tateTransportComplexNatTrans :
    tateComplexFunctor k K ⟶ resFunctor (e : H →* K) ⋙ tateComplexFunctor k H where
  app := tateTransportComplex e
  naturality _ _ φ := (tateTransportComplex_naturality e φ).symm

end Complex

section Cohomology

variable [Fintype H] [Fintype K] (e : H ≃* K)

noncomputable def tateTransport (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := K) n ⟶
      resFunctor (e : H →* K) ⋙ tateCohomologyFunctor (R := k) (G := H) n :=
  Functor.whiskerRight (tateTransportComplexNatTrans e) (HomologicalComplex.homologyFunctor _ _ n)

lemma tateTransport_app (n : ℤ) (B : Rep.{u} k K) :
    (tateTransport e n).app B = HomologicalComplex.homologyMap (tateTransportComplex e B) n := rfl

@[simps]
noncomputable def tateTransportShortComplex (X : ShortComplex (Rep.{u} k K)) :
    X.map (tateComplexFunctor k K) ⟶
      (X.map (resFunctor (e : H →* K))).map (tateComplexFunctor k H) where
  τ₁ := tateTransportComplex e X.X₁
  τ₂ := tateTransportComplex e X.X₂
  τ₃ := tateTransportComplex e X.X₃
  comm₁₂ := tateTransportComplex_naturality e X.f
  comm₂₃ := tateTransportComplex_naturality e X.g

omit [Fintype H] [Fintype K] in

lemma shortExact_map_resFunctor_equiv {X : ShortComplex (Rep.{u} k K)} (hX : X.ShortExact) :
    (X.map (resFunctor (e : H →* K))).ShortExact :=
  (Rep.shortExact_res (e : H →* K)).2 hX

theorem tateTransport_δ {X : ShortComplex (Rep.{u} k K)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateTransport e (n + 1)).app X.X₁ =
      (tateTransport e n).app X.X₃ ≫
        TateCohomology.δ (shortExact_map_resFunctor_equiv e hX) n :=
  HomologicalComplex.HomologySequence.δ_naturality (tateTransportShortComplex e X)
    (TateCohomology.map_tateComplexFunctor_shortExact hX)
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_map_resFunctor_equiv e hX))
    n (n + 1) rfl

omit [Fintype H] [Fintype K] in

def invariantsTransport {B : Rep.{u} k K} (x : B.ρ.invariants) :
    (res (e : H →* K) B).ρ.invariants :=
  ⟨x, fun h => x.2 (e h)⟩

omit [Fintype H] [Fintype K] in
@[simp]
lemma coe_invariantsTransport {B : Rep.{u} k K} (x : B.ρ.invariants) :
    (invariantsTransport e x : B) = x := rfl

theorem tateTransport_tateZeroClass (B : Rep.{u} k K) (x : B.ρ.invariants) :
    ((tateTransport e 0).app B).hom (tateZeroClass B x) =
      tateZeroClass (res (e : H →* K) B) (invariantsTransport e x) :=
  homologyMap_tateZeroClass _ x _ (funext fun _ => rfl)

end Cohomology

end GroundTheory.GroupCoh
end

