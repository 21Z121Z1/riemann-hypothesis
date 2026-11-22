import Development.EtaleCohomology.EtaleSheaves.Bundle0035
import Development.EtaleCohomology.EtaleSheaves.LeafRepCut

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPfEmpty
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

theorem etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme (R : Type) [CommRing R] (E : Scheme.{0}) [IsEmpty E] :
    IsZero ((free R).obj (yoneda.obj E)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _ |>.injective
  ext T : 2
  by_cases hT : IsEmpty T.unop
  · haveI := hT
    exact ((Sheaf.isTerminalOfBotCover _ T.unop
      (AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology T.unop)).isZero).eq_of_tgt _ _
  · rw [not_isEmpty_iff] at hT
    obtain ⟨t⟩ := hT
    have hP : IsEmpty ((yoneda.obj E).obj T) := ⟨fun f => isEmptyElim (f.base t)⟩
    apply IsZero.eq_of_src
    change IsZero ((ModuleCat.free (ULift.{1} R)).obj (ULift.{1} ((yoneda.obj E).obj T)))
    rw [ModuleCat.isZero_iff_subsingleton]
    haveI : IsEmpty (ULift.{1} ((yoneda.obj E).obj T)) := inferInstance
    change Subsingleton (ULift.{1} ((yoneda.obj E).obj T) →₀ ULift.{1} R)
    infer_instance

theorem leafEmptyVanish : LeafEmptyVanish := by
  intro R _ X F n
  have hE : IsEmpty (((⊥ : X.Opens) : Scheme.{0}) : Type) := by
    change IsEmpty ((⊥ : X.Opens) : Set X); simp
  have hfree := etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme R ((⊥ : X.Opens) : Scheme.{0})
  have hN : IsZero ((chainsN R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro j
    refine IsZero.eq_of_src ?_ _ _
    exact hfree
  have hC : IsZero ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) :=
    Functor.map_isZero (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) hN
  have hX : ∀ p, IsZero (((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))).X p) := fun p =>
    Functor.map_isZero (HomologicalComplex.eval _ _ p) hC
  have : Subsingleton (Cochain ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hX p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  change Subsingleton (CohomologyClass _ _ n)
  unfold CohomologyClass
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

end LateralTheory.E.E8

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafBaseChangeFieldPf
section
noncomputable section
open Polynomial IntermediateField

namespace LateralTheory.E.LeafBaseChangeFieldPf

def ratMap (F G : Type) [Field F] [Field G] [Algebra F G] : RatFunc F →+* RatFunc G :=
  RatFunc.liftRingHom ((algebraMap G[X] (RatFunc G)).comp (Polynomial.mapRingHom (algebraMap F G))) (show
      nonZeroDivisors F[X] ≤ Submonoid.comap ((algebraMap G[X] (RatFunc G)).comp
        (Polynomial.mapRingHom (algebraMap F G))) (nonZeroDivisors (RatFunc G)) from by
    intro p hp
    rw [Submonoid.mem_comap]
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom]
    intro h
    apply hp0
    have h1 := RatFunc.algebraMap_injective G (h.trans (map_zero _).symm)
    exact (Polynomial.map_eq_zero_iff (algebraMap F G).injective).1 h1)

lemma ratMap_algebraMap (F G : Type) [Field F] [Field G] [Algebra F G] (f : F) :
    ratMap F G (algebraMap F (RatFunc F) f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
  have e1 : algebraMap F (RatFunc F) f = algebraMap F[X] (RatFunc F) (C f) / algebraMap F[X] (RatFunc F) 1 := by
    rw [map_one, div_one, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [e1, ratMap, RatFunc.liftRingHom_apply_div]
  simp [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

lemma mem_adjoin_of_ratFunc {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] (x : RatFunc G) :
    algebraMap (RatFunc G) L x ∈ G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := by
  have key : ∀ p : G[X], algebraMap (RatFunc G) L (algebraMap G[X] (RatFunc G) p) =
      aeval (algebraMap (RatFunc G) L RatFunc.X) p := by
    intro p
    rw [aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]
  rw [← RatFunc.num_div_denom x, map_div₀, key, key]
  exact div_mem (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))
    (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))

lemma transc_X_image {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] : Transcendental G (algebraMap (RatFunc G) L RatFunc.X) := by
  rw [transcendental_iff_injective]
  intro p q h
  rw [aeval_algebraMap_apply, aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap,
    RatFunc.aeval_X_left_eq_algebraMap] at h
  exact RatFunc.algebraMap_injective G ((algebraMap (RatFunc G) L).injective h)

lemma finite_over_adjoin {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] [Module.Finite (RatFunc G) L] :
    FiniteDimensional G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L := by
  let c : RatFunc G →+* G⟮algebraMap (RatFunc G) L RatFunc.X⟯ :=
    (algebraMap (RatFunc G) L).codRestrict _ mem_adjoin_of_ratFunc
  letI : Algebra (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := c.toAlgebra
  haveI : IsScalarTower (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact Module.Finite.of_restrictScalars_finite (RatFunc G) _ L

end LateralTheory.E.LeafBaseChangeFieldPf

open LateralTheory.E.LeafBaseChangeFieldPf in
theorem LateralTheory.E.LeafBaseChangeFieldPf.LeafBaseChangeField_of : LateralTheory.E.LeafCurveVCut.LeafBaseChangeField := by
  intro F G K _ _ _ _ _ t ht hfin
  let e := RatFunc.algEquivOfTranscendental t ht
  let h : F⟮t⟯ →+* RatFunc G := (ratMap F G).comp e.symm.toRingHom
  letI : Algebra F⟮t⟯ (RatFunc G) := h.toAlgebra
  haveI : Nontrivial (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ h.injective
      (algebraMap F⟮t⟯ K).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct F⟮t⟯ (RatFunc G) K)
  letI : Field (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Module.Finite.base_change F⟮t⟯ (RatFunc G) K
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (RatFunc G) M).toLinearMap Ideal.Quotient.mk_surjective
  haveI : IsScalarTower G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := inferInstance
  refine ⟨TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M, inferInstance, inferInstance,
    algebraMap (RatFunc G) _ RatFunc.X,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight (R := F⟮t⟯) (A := RatFunc G) (B := K)).toRingHom,
    transc_X_image, finite_over_adjoin, ?_⟩
  ext f
  have h1 : h (algebraMap F F⟮t⟯ f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
    show ratMap F G (e.symm (algebraMap F F⟮t⟯ f)) = _
    rw [AlgEquiv.commutes]
    exact ratMap_algebraMap F G f
  rw [RingHom.comp_apply, RingHom.comp_apply, IsScalarTower.algebraMap_apply F F⟮t⟯ K, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes, IsScalarTower.algebraMap_apply F⟮t⟯ (RatFunc G)]
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M), ← h1]
  rfl
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafConsPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafConsPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves

def LeafLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1),
  ∃ (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L),
    Rep q i p ι K0 l0 ∧ Rep q i (g1 ≫ p) ι K1 l1 ∧ Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 ∧ RepB q i ι L lL ∧
    MorRep q i p g1 ι l0 l1 f ∧ MorRep q i (g1 ≫ p) g2 ι l1 l2 g ∧ MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ

def LeafGlob : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
  (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
  (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L),
  Rep q i p ι K0 l0 → Rep q i (g1 ≫ p) ι K1 l1 → Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 → RepB q i ι L lL →
  MorRep q i p g1 ι l0 l1 f → MorRep q i (g1 ≫ p) g2 ι l1 l2 g → MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ →
  ∃ (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj L)),
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (shiftFunctor _ n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (shiftFunctor _ n).map ℓ)

theorem LeafCons_of (hL : LeafLoc) (hG : LeafGlob) : LateralTheory.E.EtaleTopologySheaves.LeafCons := by
  intro q _ i B W Y0 Y1 Y2 ι _ p g1 g2
  obtain ⟨K0, K1, K2, L, f, g, ℓ, l0, l1, l2, lL, r0, r1, r2, rL, mf, mg, mℓ⟩ := hL q i ι p g1 g2
  obtain ⟨e0, e2, eL, h1, h2, h3, h4⟩ :=
    hG q i ι p g1 g2 K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  exact ⟨K0, K1, K2, L, f, g, ℓ, l0, l1, l2, lL, e0, e2, eL, r0, r1, r2, rL, mf, mg, mℓ, h1, h2, h3, h4⟩

end LateralTheory.E.LeafConsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafConsPfA
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafConsPfA
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

theorem HK_pull_mk (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) (z : Cocycle L (res R F) n) :
    HK.pull R f F n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom f) z (zero_add n)) := rfl

theorem HK_pull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (y : HK R M F n) : HK.pull R (f ≫ g) F n y = HK.pull R f F n (HK.pull R g F n y) := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  rw [HK_pull_mk, HK_pull_mk, HK_pull_mk]
  congr 1
  apply Cocycle.ext
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem HK_pull_id (R : Type) [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ)
    (y : HK R K F n) : HK.pull R (𝟙 K) F n y = y := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  rw [HK_pull_mk]
  congr 1
  apply Cocycle.ext
  simp [zcomp]

theorem map_congr {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂} (ha : a = a') (hb : b = b')
    (c : φ₁ ≫ b = a ≫ φ₂) (c' : φ₁ ≫ b' = a' ≫ φ₂) :
    mappingCone.map φ₁ φ₂ a b c = mappingCone.map φ₁ φ₂ a' b' c' := by
  subst ha hb; rfl

theorem rmap_congr (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') {u u2 : U' ⟶ U} {e e2 : E' ⟶ E}
    (hu : u = u2) (he : e = e2) (c : f' ≫ e = u ≫ f) (c2 : f' ≫ e2 = u2 ≫ f) :
    rmap R f f' u e c = rmap R f f' u2 e2 c2 := by
  subst hu he; rfl

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (c'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) c'' = rmap R f' f'' u' e' c' ≫ rmap R f f' u e c := by
  unfold rmap
  exact (map_congr _ _ ((chains R).map_comp _ _) ((chains R).map_comp _ _) _ _).trans
    (mappingCone.map_comp _ _ _ _ _ _ _ _ _)

theorem rmap_id (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (c : f ≫ 𝟙 E = 𝟙 U ≫ f) :
    rmap R f f (𝟙 U) (𝟙 E) c = 𝟙 _ := by
  unfold rmap
  exact (map_congr _ _ ((chains R).map_id _) ((chains R).map_id _) _ _).trans (mappingCone.map_id _)

theorem rpl_comp (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (c'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (n : ℤ) (y) :
    rpl q i f f'' (u' ≫ u) (e' ≫ e) c'' n y = rpl q i f' f'' u' e' c' n (rpl q i f f' u e c n y) := by
  simp only [rpl, rpull]
  rw [← HK_pull_comp, ← rmap_comp _ _ _ _ _ _ _ _ _ _ (by simp only [← Functor.map_comp, c'', Category.assoc])]
  congr 1

theorem rpl_id (q : ℕ) (i : ℤ) {U E : Scheme.{0}} (f : U ⟶ E) (c : f ≫ 𝟙 E = 𝟙 U ≫ f) (n : ℤ) (y) :
    rpl q i f f (𝟙 U) (𝟙 E) c n y = y := by
  simp only [rpl, rpull]
  rw [rmap_congr _ _ _ (sch.map_id _) (sch.map_id _) _ (by simp), rmap_id, HK_pull_id]

theorem rpl_bij (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (c : f' ≫ e = u ≫ f) [IsIso u] [IsIso e] (n : ℤ) : Function.Bijective (rpl q i f f' u e c n) := by
  have c2 : f ≫ inv e = inv u ≫ f' := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine Function.bijective_iff_has_inverse.2 ⟨rpl q i f' f (inv u) (inv e) c2 n, fun y => ?_, fun y => ?_⟩
  · rw [← rpl_comp q i f f' f u e (inv u) (inv e) c c2 (by simp), ]
    simp only [IsIso.inv_hom_id]
    exact rpl_id q i f _ n y
  · rw [← rpl_comp q i f' f f' (inv u) (inv e) u e c2 c (by simp)]
    simp only [IsIso.hom_inv_id]
    exact rpl_id q i f' _ n y

end LateralTheory.E.LeafConsPfA
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointPfClear
section
noncomputable section

namespace LateralTheory.E.LeafCoordsPointPf

open LateralTheory.E.LeafCoordsPf
open scoped Pointwise

theorem clear {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B) (hP : P.IsPrime)
    (L N : Submodule B M) (hL : L.FG) (H : ∀ x ∈ L, ∃ s ∉ P, s • x ∈ N) :
    ∃ h ∉ P, ∀ x ∈ L, h • x ∈ N := by
  classical
  obtain ⟨S, rfl⟩ := hL
  have key : ∀ T : Finset M, T ⊆ S → ∃ h ∉ P, ∀ g ∈ T, h • g ∈ N := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
    | insert a T ha ih =>
      intro hT
      obtain ⟨h, hh, hg⟩ := ih (fun x hx => hT (Finset.mem_insert_of_mem hx))
      obtain ⟨s, hs, hsa⟩ := H a (Submodule.subset_span (hT (Finset.mem_insert_self a T)))
      refine ⟨s * h, fun H' => (hP.mem_or_mem H').elim hs hh, ?_⟩
      intro g hg'
      rcases Finset.mem_insert.mp hg' with rfl | hg'
      · rw [mul_comm, mul_smul]; exact N.smul_mem h hsa
      · rw [mul_smul]; exact N.smul_mem s (hg g hg')
  obtain ⟨h, hh, hg⟩ := key S subset_rfl
  refine ⟨h, hh, fun x hx => ?_⟩
  have : Submodule.span B (S : Set M) ≤ N.comap (h • LinearMap.id) :=
    Submodule.span_le.mpr fun g hgS => by simpa using hg g hgS
  simpa using this hx

def LeafCoordsPointLoc : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ (t : Fin d → B) (y : Fin e → B),
    (∀ j, t j ∈ I) ∧ (∀ x ∈ I, ∃ s ∉ P, s • x ∈ Ideal.span (Set.range t) ⊔ P • I) ∧
    (∀ ω : Ω[B⁄A], ∃ s ∉ P, s • ω ∈ Submodule.span B (Set.range (dyt (A := A) y t)) ⊔ P • ⊤)

theorem LeafCoordsPoint_of (hLoc : LeafCoordsPointLoc) : LeafCoordsPoint := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨t, y, ht, hI, hΩ⟩ := hLoc d e A B I hB hBI P hP hIP
  obtain ⟨h1, hh1, h1I⟩ := clear P hP I _ (ideal_fg I _ _ hB hBI) hI
  have := hB.isStandardSmooth
  obtain ⟨h2, hh2, h2Ω⟩ := clear P hP ⊤ _ Module.Finite.fg_top (fun ω _ => hΩ ω)
  refine ⟨h1 * h2, fun H => (hP.mem_or_mem H).elim hh1 hh2, t, y, ht, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    show (h1 * h2) • x ∈ _
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem _ h2 (h1I x hx)
  · rintro _ ⟨x, -, rfl⟩
    show (h1 * h2) • x ∈ _
    rw [mul_smul]
    exact Submodule.smul_mem _ h1 (h2Ω x trivial)

end LateralTheory.E.LeafCoordsPointPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDegCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafDegCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves

def Cov {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop) : Prop :=
  ∃ S ∈ (EtTop B) U, ∀ (U' : B.Etale) (a : U' ⟶ U), S a → P U' a

theorem Cov.mono {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' a, P U' a → Q U' a) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun U' a ha => hPQ U' a (hP U' a ha)⟩

theorem Cov.and {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P) (h' : Cov U Q) :
    Cov U (fun U' a => P U' a ∧ Q U' a) := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hQ⟩ := h'
  exact ⟨S ⊓ S', (EtTop B).intersection_covering hS hS', fun U' a ha => ⟨hP U' a ha.1, hQ U' a ha.2⟩⟩

theorem Cov.all {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : ∀ U' a, P U' a) : Cov U P :=
  ⟨⊤, (EtTop B).top_mem U, fun U' a _ => h U' a⟩

def SHV (q : ℕ) (i : ℤ) {B Y0 Y1 Y2 : Scheme.{0}} (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) : Prop :=
  ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)

abbrev rY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prU p ι U) (prU p ι U') (resYW p ι a) (resY p a) (pullback.lift_fst _ _ _).symm m

abbrev rB (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prB ι U) (prB ι U') (resBW ι a) a.left (pullback.lift_fst _ _ _).symm m

abbrev gY (q : ℕ) (i : ℤ) {B W Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prU p ι U) (prU (g ≫ p) ι U) (mW p g ι U) (mY p g U) (pullback.lift_fst _ _ _).symm m

abbrev bY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prB ι U) (prU p ι U) (toBW p ι U) (toBY p U) (pullback.lift_fst _ _ _).symm m

def LeafNeg : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ), m < 0 →
  Subsingleton (Hrel R f F m)

def LeafShMapZero : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (K K' : DerivedCategory (SShv B q)) (f : K ⟶ K') (m : ℤ),
  (∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0)) →
  (DerivedCategory.homologyFunctor (SShv B q) m).map f = 0

def LeafShIso : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (L K : DerivedCategory (SShv B q)) (ℓ : L ⟶ K) (m : ℤ),
  (∀ (U : B.Etale) (x x' : (OU B q).obj U ⟶ (shiftFunctor _ m).obj L),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map ℓ = (OU B q).map a ≫ x' ≫ (shiftFunctor _ m).map ℓ) →
    Cov U (fun U' a => (OU B q).map a ≫ x = (OU B q).map a ≫ x')) →
  (∀ (U : B.Etale) (y : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ (shiftFunctor _ m).obj L, (OU B q).map a ≫ y = x ≫ (shiftFunctor _ m).map ℓ)) →
  IsIso ((DerivedCategory.homologyFunctor (SShv B q) m).map ℓ)

def LeafVan0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 2 < m → ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m,
  Cov U (fun U' a => rY q i p ι a m y = 0)

def LeafKill2 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) 2,
  Cov U (fun U' a => rY q i (g1 ≫ p) ι a 2 (gY q i p g1 ι U 2 y) = 0)

def LeafKill1 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g1 ≫ p) ι U)) (tw q i) 1,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1 (gY q i (g1 ≫ p) g2 ι U 1 y) = 0)

def LeafVanB : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 0 < m → ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m,
  Cov U (fun U' a => rB q i ι a m c = 0)

def LeafInj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  Cov U (fun U' a => rB q i ι a 0 c = 0)

def LeafSurj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  Cov U (fun U' a => ∃ c : Hrel (ZMod q) (sch.map (prB ι U')) (tw q i) 0,
    bY q i (g2 ≫ g1 ≫ p) ι U' 0 c = rY q i (g2 ≫ g1 ≫ p) ι a 0 y)

theorem loc_zero_map {B : Scheme.{0}} {q : ℕ} {K K' : DerivedCategory (SShv B q)} (f : K ⟶ K') {m : ℤ}
    (X X' : B.Etale → Type 1) [∀ U, Zero (X' U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K))
    (e' : ∀ U, X' U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K'))
    (hb : ∀ U, Function.Surjective (e U))
    (res' : ∀ U U', (U' ⟶ U) → X' U → X' U') (φ : ∀ U, X U → X' U)
    (hnat : ∀ U U' (a : U' ⟶ U) y, e' U' (res' U U' a y) = (OU B q).map a ≫ e' U y)
    (hf : ∀ U y, e' U (φ U y) = e U y ≫ (shiftFunctor _ m).map f)
    (hv : ∀ U y, Cov U (fun U' a => res' U U' a (φ U y) = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0) := by
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  refine (Cov.and (hv U y) (hv U y0)).mono fun U' a ⟨h1, h2⟩ => ?_
  rw [← hf, ← hnat, h1, ← h2, hnat, hf, hy0, zero_comp, comp_zero]

theorem loc_zero {B : Scheme.{0}} {q : ℕ} {K : DerivedCategory (SShv B q)} {m : ℤ}
    (X : B.Etale → Type 1) [∀ U, Zero (X U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U))
    (res : ∀ U U', (U' ⟶ U) → X U → X U')
    (hnat : ∀ U U' (a : U' ⟶ U) y, e U' (res U U' a y) = (OU B q).map a ≫ e U y)
    (hv : ∀ U y, Cov U (fun U' a => res U U' a y = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0) :=
  loc_zero_map (𝟙 K) X X e e hb res (fun _ y => y) hnat (fun U y => by simp) hv U x

theorem isZero_of (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (h : ∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
      Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id]
  exact hZ B q K K (𝟙 K) m h

theorem isZero_neg (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (X : B.Etale → Type 1) (hs : ∀ U, Subsingleton (X U))
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  refine isZero_of hZ K m fun U x => Cov.all fun U' a => ?_
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  rw [Subsingleton.elim y y0, hy0]
  simp

theorem goal_of (hN : LeafNeg) (hZ : LeafShMapZero) (hI : LeafShIso) (hV0 : LeafVan0) (hK2 : LeafKill2)
    (hK1 : LeafKill1) (hVB : LeafVanB) (hIn : LeafInj0) (hSu : LeafSurj0) : LateralTheory.E.EtaleTopologySheaves.LeafDeg := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  have hS : SHV q i V p g1 g2 := hA
  refine ⟨fun m hm => ?_, ?_, ?_, fun m hm => ?_, fun m hm => ?_, ?_⟩
  · exact isZero_of hZ K0 m (loc_zero _ (l0 · m) (fun U => (r0.1 U m).2) (fun U U' a => rY q i p ι a m)
      (fun U U' a y => r0.2 U U' a m y) (fun U y => hV0 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm y))
  · exact hZ B q K0 K1 f 2 (loc_zero_map f _ _ (l0 · 2) (l1 · 2) (fun U => (r0.1 U 2).2)
      (fun U U' a => rY q i (g1 ≫ p) ι a 2) (fun U => gY q i p g1 ι U 2)
      (fun U U' a y => r1.2 U U' a 2 y) (fun U y => mf U 2 y)
      (fun U y => hK2 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact hZ B q K1 K2 g 1 (loc_zero_map g _ _ (l1 · 1) (l2 · 1) (fun U => (r1.1 U 1).2)
      (fun U U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1) (fun U => gY q i (g1 ≫ p) g2 ι U 1)
      (fun U U' a y => r2.2 U U' a 1 y) (fun U y => mg U 1 y)
      (fun U y => hK1 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact isZero_neg hZ K2 m _ (fun U => hN _ _ _ m hm) (l2 · m) (fun U => (r2.1 U m).2)
  · rcases lt_or_gt_of_ne hm with hm | hm
    · exact isZero_neg hZ L m _ (fun U => hN _ _ _ m hm) (lL · m) (fun U => (rL.1 U m).2)
    · exact isZero_of hZ L m (loc_zero _ (lL · m) (fun U => (rL.1 U m).2) (fun U U' a => rB q i ι a m)
        (fun U U' a c => rL.2 U U' a m c) (fun U c => hVB hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm c))
  · refine hI B q L K2 ℓ 0 (fun U x x' hx => ?_) (fun U y => ?_)
    · obtain ⟨c, rfl⟩ := (rL.1 U 0).2 x
      obtain ⟨c', rfl⟩ := (rL.1 U 0).2 x'
      have hd := hIn hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U (c - c') (hx.mono fun U' a h => by
        rw [← mℓ U 0 c, ← mℓ U 0 c', ← r2.2 U U' a 0, ← r2.2 U U' a 0] at h
        rw [map_sub, map_sub, (r2.1 U' 0).1 h, sub_self])
      refine hd.mono fun U' a h => ?_
      rw [← rL.2 U U' a 0 c, ← rL.2 U U' a 0 c', sub_eq_zero.1 ((map_sub _ c c').symm.trans h)]
    · obtain ⟨z, rfl⟩ := (r2.1 U 0).2 y
      refine (hSu hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U z).mono fun U' a ⟨c, hc⟩ => ⟨lL U' 0 c, ?_⟩
      rw [← r2.2 U U' a 0 z, ← hc, mℓ U' 0 c]

end LateralTheory.E.LeafDegCut
end
end

