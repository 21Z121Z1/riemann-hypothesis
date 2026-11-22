import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasTransitionCompatibleFramesOfNoCompleteDVRPoin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

def noTraitZero {X : Scheme.{0}} (M : LB X) : M.Sec := ⟨fun _ => 0, by simp⟩

theorem noTrait_gs_zero {Y X : Scheme.{0}} (r : Y ⟶ X) (y : Y) (U : X.Opens) : gs r y U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

theorem lin_noTraitZero {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (c : Fin n → Γ(T'.left, ⊤)) : GlobalTheory.LN.Lin G L N h (fun _ => noTraitZero _) c (noTraitZero _) := by
  intro z J _
  refine (noTrait_gs_zero _ _ _).trans (Finset.sum_eq_zero fun i _ => ?_).symm
  exact (congrArg _ (noTrait_gs_zero _ _ _)).trans (mul_zero _)

theorem noTrait_exists_gl_det_eq {R : Type*} [CommRing R] {n : ℕ} (hn : 1 ≤ n) (u : Rˣ) :
    ∃ M : GL (Fin n) R, Matrix.GeneralLinearGroup.det M = u := by
  have hd : (Matrix.diagonal (Function.update (fun _ : Fin n => (1 : R)) ⟨0, hn⟩ u.val)).det = u.val := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mk'' _ (by rw [hd]; exact u.isUnit), Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact hd

theorem hasFrames_rank_of_isEmpty (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ)
    (hn : 1 ≤ n') (hZ : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z))
    (h : HasFrames G L N A n r s) : HasFrames G L N A n' r s := by
  obtain ⟨th, b, h₁, -⟩ := h
  refine ⟨th, fun _ _ => noTraitZero _, fun i j => ?_, fun i W _ _ _ hW χ _ => ((hZ W hW).false (χ ≫ (A.U i).ι)).elim⟩
  obtain ⟨c, M, h₂, -, h₃⟩ := h₁ i j
  obtain ⟨M', hM⟩ := noTrait_exists_gl_det_eq hn (Matrix.GeneralLinearGroup.det M)
  exact ⟨c, M', h₂, fun k => ⟨noTraitZero _, lin_noTraitZero G L N _ _, lin_noTraitZero G L N _ _⟩, by rw [hM]; exact h₃⟩

end GlobalTheory.ModelSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomDescendsToFgIntermediateField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem hom_descends_to_fg_intermediateField : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (A B : Over (Sp K)) (f : (Over.pullback (spMap (algebraMap K C))).obj A ⟶ (Over.pullback (spMap (algebraMap K C))).obj B), LocallyOfFiniteType A.hom → QuasiCompact A.hom → IsSeparated A.hom → LocallyOfFiniteType B.hom → ∃ (L : IntermediateField K C) (f₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ B.left), L.FG ∧ f₀ ≫ B.hom = pullback.fst _ _ ≫ A.hom ∧ ∀ i : pullback A.hom (spMap (algebraMap K C)) ⟶ pullback A.hom (spMap (algebraMap K L)), i ≫ pullback.fst _ _ = pullback.fst _ _ → i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (algebraMap L C) → i ≫ f₀ = f.left ≫ pullback.fst _ _ := by
  intro K C _ _ _ A B f _ _ _ _
  have hw : f.left ≫ pullback.snd B.hom (spMap (algebraMap K C)) =
      pullback.snd A.hom (spMap (algebraMap K C)) := by
    simpa using Over.w f
  have hφ : (f.left ≫ pullback.fst _ _) ≫ B.hom = pullback.fst _ _ ≫ A.hom := by
    rw [Category.assoc, pullback.condition, reassoc_of% hw, pullback.condition]
  obtain ⟨R, ψ, hR, hψ, hRψ⟩ := Spread.exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) hφ
  obtain ⟨t, rfl⟩ := hR
  let L : IntermediateField K C := IntermediateField.adjoin K (t : Set C)
  have hle : Algebra.adjoin K (t : Set C) ≤ L.toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin K _
  refine ⟨L, Spread.bcMap A.hom (Subalgebra.inclusion hle) ≫ ψ, ⟨t, rfl⟩, ?_, ?_⟩
  · rw [Category.assoc, hψ, Spread.bcMap_fst_assoc]
  · intro i h₁ h₂
    rw [Spread.eq_bcMap A.hom L.val h₁ h₂, ← Category.assoc,
      Spread.bcMap_comp_of_eq A.hom _ _ (Algebra.adjoin K (t : Set C)).val fun _ ↦ rfl, hRψ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfCommonGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isAbelianScheme_of_common_generic_fibre
    {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B G : Over (Sp V)) [GrpObj B] [GrpObj G] (hB : IsAbelianScheme B) (hG : IsSemiAbelian G)
    (hext : ∀ f : (Over.pullback (spMap (algebraMap V K))).obj B ⟶ (Over.pullback (spMap (algebraMap V K))).obj G,
      IsMonHom f → ∃ F : B ⟶ G, (Over.pullback (spMap (algebraMap V K))).map F = f)
    (A : Over (Sp K)) [GrpObj A] {φ₁ : A.left ⟶ B.left} {φ₂ : A.left ⟶ G.left}
    (h₁ : IsGrpPullback A B (spMap (algebraMap V K)) φ₁) (h₂ : IsGrpPullback A G (spMap (algebraMap V K)) φ₂) :
    IsAbelianScheme G := by
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback B (spMap (algebraMap V K))) h₁
  obtain ⟨e', he', -⟩ := grpPullback_iso h₂ (isGrpPullback_pullback G (spMap (algebraMap V K)))
  obtain ⟨F, hF⟩ := hext (e.hom ≫ e'.hom) inferInstance
  refine isAbelianScheme_of_generically_surjective V K B G hB hG F ?_
  rintro x ⟨k, hk⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk.symm
  have hsq : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G.hom (spMap (algebraMap V K)) =
      pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left := by
    simp
    exact pullback.lift_fst _ _ _
  rw [hF] at hsq
  have hid : (e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Iso.trans_hom, Iso.inv_hom_id, Over.id_left]
  refine ⟨pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z), ?_⟩
  calc F.left (pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z))
      = ((e ≪≫ e').inv.left ≫ pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left) z := rfl
    _ = ((e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left ≫ pullback.fst G.hom (spMap (algebraMap V K))) z := by rw [hsq]
    _ = pullback.fst G.hom (spMap (algebraMap V K)) z := by rw [← Category.assoc, hid, Category.id_comp]
    _ = x := hz

theorem goodRedExt_of_isDiscreteValuationRing :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K], Y.GoodRedExt V K := by
  intro hext E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ b y hy hex
  obtain ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, h𝒜, -, -, hp1, hp2, -⟩ := hex
  obtain ⟨y', t, m, hy's, hy'j, hab⟩ := GlobalTheory.model_point_extends E H D l Xo c O β Y V K b y hy
  refine ⟨y', hy's, hy'j, hab ?_⟩
  have hm := m.cart
  have hc := IsGrpPullback.comp hp2 Y.m.cart
  have hw : (φ₂ ≫ Y.m.cm.F) ≫ Y.t.G.hom = (A.hom ≫ spMap (algebraMap V K)) ≫ y' := by
    rw [hc.1.w, Category.assoc, hy'j]; rfl
  have h2 : IsGrpPullback A t.G (spMap (algebraMap V K)) (hm.1.lift _ _ hw) :=
    IsGrpPullback.cancel hm (hc.congr (by rw [hy'j]; rfl) (hm.1.lift_fst _ _ hw).symm) (hm.1.lift_snd _ _ hw)
  exact isAbelianScheme_of_common_generic_fibre 𝒜 t.G h𝒜 t.semi
    (fun f hf => (hext V K 𝒜 t.G (isSemiAbelian_of_isAbelianScheme 𝒜 h𝒜) t.semi f hf).exists.imp fun _ h => h.2)
    A hp1 h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforward
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.ModelSum

noncomputable section

namespace GlobalTheory.ModelSum.UnionAmple

variable {Z Z' : Scheme.{0}}

theorem gs_eq_stalkMap (r : Z' ⟶ Z) (z : Z') (U : Z.Opens) (h : r z ∈ U) (a : Γ(Z, U)) :
    gs r z U a = (r.stalkMap z).hom (gs (𝟙 Z) (r z) U a) := by
  rw [gs_eq r z U h, gs_eq (𝟙 Z) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h a).symm

theorem gs_id_of_gs (f : Z' ⟶ Z) [IsOpenImmersion f] (y : Z') {U : Z.Opens} (h : f y ∈ U) {a b : Γ(Z, U)}
    (e : gs f y U a = gs f y U b) : gs (𝟙 Z) (f y) U a = gs (𝟙 Z) (f y) U b := by
  rw [gs_eq_stalkMap f y U h, gs_eq_stalkMap f y U h] at e
  exact (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).1 e

theorem gm_id_of_gm (f : Z' ⟶ Z) [IsOpenImmersion f] (y : Z') {U : Z.Opens} (h : f y ∈ U) {a b : Γ(Z, U)ˣ}
    (e : gm f y U a = gm f y U b) : gm (𝟙 Z) (f y) U a = gm (𝟙 Z) (f y) U b := by
  apply Units.ext
  rw [← gs_unit (𝟙 Z) (f y) U h, ← gs_unit (𝟙 Z) (f y) U h]
  apply gs_id_of_gs f y h
  rw [gs_unit f y U h, gs_unit f y U h, e]

theorem gs_push (f : Z' ⟶ Z) [IsOpenImmersion f] (y : Z') {U : Z'.Opens} (h : y ∈ U) (a : Γ(Z', U)) :
    gs f y (f ''ᵁ U) ((f.appIso U).inv.hom a) = gs (𝟙 Z') y U a := by
  have h' : f y ∈ f ''ᵁ U := ⟨y, h, rfl⟩
  have e : (f.app (f ''ᵁ U)).hom ((f.appIso U).inv.hom a) =
      (Z'.presheaf.map (homOfLE (f.preimage_image_eq U).le).op).hom a :=
    congrArg (fun q => q.hom a) (f.appIso_inv_app U)
  rw [← gs_res (𝟙 Z') y (f.preimage_image_eq U).le h' a, ← e, gs_pull (𝟙 Z') f y (f ''ᵁ U) h', Category.id_comp]

structure Part (f : Z' ⟶ Z) (A : LB Z') (C : LB Z) (e : A.ι → C.ι) : Prop where
  inj : Function.Injective e
  mem : ∀ i y, f y ∈ C.U (e i) ↔ y ∈ A.U i
  sub : ∀ i x, x ∈ C.U (e i) → x ∈ Set.range f
  surj : ∀ p y, f y ∈ C.U p → ∃ i, e i = p
  g : ∀ i j y, y ∈ A.U i → y ∈ A.U j →
    gm f y (C.U (e i) ⊓ C.U (e j)) (C.g (e i) (e j)) = gm (𝟙 Z') y (A.U i ⊓ A.U j) (A.g i j)

theorem gm_pushLB (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') (i j : A.ι) (y : Z') (hi : y ∈ A.U i) (hj : y ∈ A.U j) :
    gm f y (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j) ((pushLB f A).g i j) = gm (𝟙 Z') y (A.U i ⊓ A.U j) (A.g i j) := by
  have hm : f y ∈ f ''ᵁ A.U i ⊓ f ''ᵁ A.U j := ⟨⟨y, hi, rfl⟩, ⟨y, hj, rfl⟩⟩
  have hm' : y ∈ A.U i ⊓ A.U j := ⟨hi, hj⟩
  refine (gm_res f y _ hm _).trans (Units.ext ?_)
  exact (gs_unit f y _ (image_inf_le f _ _ hm) _).symm.trans ((gs_push f y hm' _).trans (gs_unit _ y _ hm' _))

theorem part_left (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') (B : LB Z) (hB : ∀ p y, f y ∉ B.U p) :
    Part f A (sumLB (pushLB f A) B) Sum.inl where
  inj := Sum.inl_injective
  mem := fun i y => f.apply_mem_image_iff
  sub := fun i x ⟨y, _, hy⟩ => ⟨y, hy⟩
  surj := fun p y hp => by
    rcases p with i | p
    · exact ⟨i, rfl⟩
    · exact (hB p y hp).elim
  g := gm_pushLB f A

theorem part_right (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') (B : LB Z) (hB : ∀ p y, f y ∉ B.U p) :
    Part f A (sumLB B (pushLB f A)) Sum.inr where
  inj := Sum.inr_injective
  mem := fun i y => f.apply_mem_image_iff
  sub := fun i x ⟨y, _, hy⟩ => ⟨y, hy⟩
  surj := fun p y hp => by
    rcases p with p | i
    · exact (hB p y hp).elim
    · exact ⟨i, rfl⟩
  g := gm_pushLB f A

variable {f : Z' ⟶ Z} {A : LB Z'} {C : LB Z} {e : A.ι → C.ι}

theorem Part.cocycle (h : Part f A C e) (hA : A.IsLB) (y : Z') {p q r : C.ι} (hp : f y ∈ C.U p) (hq : f y ∈ C.U q)
    (hr : f y ∈ C.U r) : gm f y _ (C.g p q) * gm f y _ (C.g q r) = gm f y _ (C.g p r) := by
  obtain ⟨i, rfl⟩ := h.surj p y hp
  obtain ⟨j, rfl⟩ := h.surj q y hq
  obtain ⟨k, rfl⟩ := h.surj r y hr
  rw [h.mem] at hp hq hr
  rw [h.g _ _ _ hp hq, h.g _ _ _ hq hr, h.g _ _ _ hp hr]
  exact gm_cocycle hA (𝟙 Z') y hp hq hr

theorem mem_wchart {X : Scheme.{0}} (L : LB X) (J : Fin 1 → L.ι) (x : X) :
    x ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) J ↔ x ∈ L.U (J 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem gs_zero' {X Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) (U : X.Opens) : gs r z U 0 = 0 := by
  by_cases h : r z ∈ U
  · rw [gs_eq r z U h, map_zero, map_zero]
  · exact dif_neg h

theorem Part.exists_local [IsOpenImmersion f] (h : Part f A C e) {d : ℕ} (s : H0 A d) (J : Fin 1 → C.ι) :
    ∃ t : Γ(Z, LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J),
      (∀ i y, e i = J 0 → y ∈ A.U i → gs f y _ t = gs (𝟙 Z') y _ (s.f fun _ => i)) ∧
      ∀ x, x ∉ Set.range f → gs (𝟙 Z) x _ t = 0 := by
  by_cases hJ : ∃ i, e i = J 0
  · obtain ⟨i, hi⟩ := hJ
    have le : LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J ≤ f ''ᵁ LB.wchart A (fun _ : Fin 1 => 𝟙 Z') fun _ => i := by
      intro x hx
      have hx' := (mem_wchart C J x).1 hx
      rw [← hi] at hx'
      obtain ⟨y, rfl⟩ := h.sub i x hx'
      exact ⟨y, (mem_wchart A _ y).2 ((h.mem i y).1 hx'), rfl⟩
    refine ⟨(Z.presheaf.map (homOfLE le).op).hom ((f.appIso _).inv.hom (s.f fun _ => i)), fun i' y hi' hy => ?_,
      fun x hx => dif_neg fun hx' => hx ?_⟩
    · obtain rfl : i' = i := h.inj (hi'.trans hi.symm)
      have hm : f y ∈ LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J :=
        (mem_wchart C J _).2 (hi ▸ (h.mem i' y).2 hy)
      exact (gs_res f y le hm _).trans (gs_push f y ((mem_wchart A _ y).2 hy) _)
    · obtain ⟨y, -, hy⟩ := le hx'
      exact ⟨y, hy⟩
  · exact ⟨0, fun i y hi _ => (hJ ⟨i, hi⟩).elim, fun x _ => gs_zero' _ _ _⟩

theorem Part.exists_sec [IsOpenImmersion f] (h : Part f A C e) {d : ℕ} (s : H0 A d) :
    ∃ t : H0 C d, nonzeroLocus t = f ''ᵁ nonzeroLocus s := by
  choose t ht h0 using h.exists_local s
  refine ⟨⟨t, fun J J' => fn_ext fun x hx => ?_⟩, ?_⟩
  · by_cases hf : x ∈ Set.range f
    · obtain ⟨y, rfl⟩ := hf
      apply gs_id_of_gs f y hx
      have h1 := (mem_wchart C J _).1 hx.1
      have h2 := (mem_wchart C J' _).1 hx.2
      obtain ⟨i, hi⟩ := h.surj _ y h1
      obtain ⟨i', hi'⟩ := h.surj _ y h2
      have k1 : y ∈ A.U i := (h.mem i y).1 (hi ▸ h1)
      have k2 : y ∈ A.U i' := (h.mem i' y).1 (hi' ▸ h2)
      have w1 := (mem_wchart A (fun _ => i) y).2 k1
      have w2 := (mem_wchart A (fun _ => i') y).2 k2
      have hm : (𝟙 Z' : Z' ⟶ Z') y ∈ LB.wchart A (fun _ : Fin 1 => 𝟙 Z') (fun _ => i) ⊓
        LB.wchart A (fun _ : Fin 1 => 𝟙 Z') (fun _ => i') := ⟨w1, w2⟩
      have c := congrArg (gs (𝟙 Z') y _) (s.compat (fun _ => i) (fun _ => i'))
      have c' := (gs_res (𝟙 Z') y inf_le_left hm _).symm.trans (c.trans ((gs_mul _ y _ hm _ _).trans
        (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans
          (congrArg Units.val (gm_linComb A _ _ (𝟙 Z') y _ _ w1 w2))) (gs_res (𝟙 Z') y inf_le_right hm _))))
      refine ((gs_res f y inf_le_left hx _).trans (ht J i y hi k1)).trans (c'.trans (Eq.symm ?_))
      refine (gs_mul f y _ hx _ _).trans (congrArg₂ (· * ·) ((gs_unit f y _ hx _).trans
        (congrArg Units.val ((gm_linComb C _ _ f y J J' hx.1 hx.2).trans ?_)))
        ((gs_res f y inf_le_right hx _).trans (ht J' i' y hi' k2)))
      refine Finset.prod_congr rfl fun k _ => congrArg (· ^ (d : ℤ)) ?_
      obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [Category.comp_id, Category.comp_id, ← hi, ← hi']
      exact h.g i i' y k1 k2
    · refine ((gs_res _ x inf_le_left hx _).trans (h0 J x hf)).trans (Eq.symm ?_)
      refine (gs_mul _ x _ hx _ _).trans ?_
      exact mul_eq_zero_of_right _ ((gs_res _ x inf_le_right hx _).trans (h0 J' x hf))
  · have key : ∀ (J : Fin 1 → C.ι) (y : Z'), f y ∈ LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J →
        (f y ∈ Z.basicOpen (t J) ↔ IsUnit (gs f y _ (t J))) := fun J y hy => by
      rw [gs_eq_stalkMap f y _ hy, isUnit_map_iff, gs_eq (𝟙 Z) (f y) _ hy]
      exact Z.mem_basicOpen _ _ hy
    have key' : ∀ (j : Fin 1 → A.ι) (y : Z') (hy : y ∈ LB.wchart A (fun _ : Fin 1 => 𝟙 Z') j),
        (y ∈ Z'.basicOpen (s.f j) ↔ IsUnit (gs (𝟙 Z') y _ (s.f j))) := fun j y hy => by
      exact (Z'.mem_basicOpen _ _ hy).trans (iff_of_eq (congrArg IsUnit (gs_eq (𝟙 Z') y _ hy (s.f j)).symm))
    ext x
    constructor
    · intro hx
      obtain ⟨J, hJ⟩ := Opens.mem_iSup.1 hx
      have hw : x ∈ LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J := Z.basicOpen_le _ hJ
      by_cases hf : x ∈ Set.range f
      · obtain ⟨y, rfl⟩ := hf
        have h1 := (mem_wchart C J _).1 hw
        obtain ⟨i, hi⟩ := h.surj _ y h1
        have k1 : y ∈ A.U i := (h.mem i y).1 (hi ▸ h1)
        have u := (key J y hw).1 hJ
        rw [ht J i y hi k1] at u
        exact ⟨y, Opens.mem_iSup.2 ⟨fun _ => i, (key' _ y ((mem_wchart A _ y).2 k1)).2 u⟩, rfl⟩
      · have u : IsUnit (gs (𝟙 Z) x _ (t J)) := by
          rw [gs_eq (𝟙 Z) x _ hw]
          exact (Z.mem_basicOpen _ _ hw).1 hJ
        rw [h0 J x hf] at u
        exact (not_isUnit_zero u).elim
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hy
      obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
      have hw : y ∈ LB.wchart A (fun _ : Fin 1 => 𝟙 Z') (fun _ => i) := Z'.basicOpen_le _ hj
      have k1 : y ∈ A.U i := (mem_wchart A _ y).1 hw
      have u := (key' _ y hw).1 hj
      rw [← ht (fun _ => e i) i y rfl k1] at u
      exact Opens.mem_iSup.2 ⟨fun _ => e i, (key _ y ((mem_wchart C _ _).2 ((h.mem i y).2 k1))).2 u⟩

theorem Part.ample_at [IsOpenImmersion f] (h : Part f A C e) (ha : AmpleFam A) (y : Z') :
    ∃ (d : ℕ) (s : H0 C d), 1 ≤ d ∧ f y ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨d, s, hd, hy, haf⟩ := ha y
  obtain ⟨t, ht⟩ := h.exists_sec s
  refine ⟨d, t, hd, ?_, ?_⟩
  · rw [ht]; exact ⟨y, hy, rfl⟩
  · rw [ht]; exact haf.image_of_isOpenImmersion f

theorem sumLB_isLB_ampleFam : ∀ (Z Z₁ Z₂ : Scheme.{0}) (f₁ : Z₁ ⟶ Z) (f₂ : Z₂ ⟶ Z) [IsOpenImmersion f₁]
    [IsOpenImmersion f₂] (A₁ : LB Z₁) (A₂ : LB Z₂), IsCompl (Set.range f₁) (Set.range f₂) → A₁.IsLB → A₂.IsLB →
    AmpleFam A₁ → AmpleFam A₂ →
    (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)).IsLB ∧ AmpleFam (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)) := by
  intro Z Z₁ Z₂ f₁ f₂ _ _ A₁ A₂ hc h₁ h₂ a₁ a₂
  have dj : ∀ y₁ y₂, f₁ y₁ ≠ f₂ y₂ := fun y₁ y₂ e =>
    Set.disjoint_left.1 hc.disjoint ⟨y₁, rfl⟩ ⟨y₂, e.symm⟩
  have cov : ∀ x : Z, (∃ y, f₁ y = x) ∨ ∃ y, f₂ y = x := fun x =>
    show x ∈ Set.range f₁ ⊔ Set.range f₂ from hc.sup_eq_top.ge trivial
  have P₁ := part_left f₁ A₁ (pushLB f₂ A₂) fun p y ⟨y', _, e⟩ => dj y y' e.symm
  have P₂ := part_right f₂ A₂ (pushLB f₁ A₁) fun p y ⟨y', _, e⟩ => dj y' y e
  set C := sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)
  have co : ∀ (x : Z) (p q r : C.ι), x ∈ C.U p → x ∈ C.U q → x ∈ C.U r →
      gm (𝟙 Z) x _ (C.g p q) * gm (𝟙 Z) x _ (C.g q r) = gm (𝟙 Z) x _ (C.g p r) := by
    intro x p q r hp hq hr
    have hm : x ∈ C.U p ⊓ C.U q ⊓ C.U r := ⟨⟨hp, hq⟩, hr⟩
    have l1 : C.U p ⊓ C.U q ⊓ C.U r ≤ C.U p ⊓ C.U q := inf_le_left
    have l2 : C.U p ⊓ C.U q ⊓ C.U r ≤ C.U q ⊓ C.U r := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have l3 : C.U p ⊓ C.U q ⊓ C.U r ≤ C.U p ⊓ C.U r := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    rw [← gm_res (𝟙 Z) x l1 hm, ← gm_res (𝟙 Z) x l2 hm, ← gm_res (𝟙 Z) x l3 hm, ← map_mul]
    rcases cov x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · apply gm_id_of_gm f₁ y hm
      rw [map_mul, gm_res _ y l1 hm, gm_res _ y l2 hm, gm_res _ y l3 hm]
      exact P₁.cocycle h₁ y hp hq hr
    · apply gm_id_of_gm f₂ y hm
      rw [map_mul, gm_res _ y l1 hm, gm_res _ y l2 hm, gm_res _ y l3 hm]
      exact P₂.cocycle h₂ y hp hq hr
  refine ⟨⟨top_le_iff.1 fun x _ => ?_, fun p => unit_ext fun x hx => ?_, fun p q r => unit_ext fun x hx => ?_⟩,
    fun x => ?_⟩
  · rcases cov x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨i, hi⟩ := exists_chart h₁ y
      exact Opens.mem_iSup.2 ⟨_, (P₁.mem i y).2 hi⟩
    · obtain ⟨i, hi⟩ := exists_chart h₂ y
      exact Opens.mem_iSup.2 ⟨_, (P₂.mem i y).2 hi⟩
  · rw [gm_res _ x _ hx, map_one]
    exact mul_eq_left.1 (co x p p p hx hx hx)
  · rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    exact co x p q r hx.1.1 hx.1.2 hx.2
  · rcases cov x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact P₁.ample_at a₁ y
    · exact P₂.ample_at a₂ y

end GlobalTheory.ModelSum.UnionAmple

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOpenSetOfTTEqBot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory

theorem isOpen_setOf_TT_eq_bot : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (M : GlobalTheory.ZH.RatModel o Ω) (I : Type) (d : I → Ω) (e : ℕ), M.HasDiv S.th → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (S.TT M z = ⊥ ↔ ∃ k, d k ≠ 0 ∧ S.th x₀ ^ e / d k ∈ M.O z)) → IsOpen {z : M.Z | S.TT M z = ⊥} := by
  intro o Ω _ _ _ S M I d e hdiv h
  haveI : NeZero (S.r * S.N) :=
    ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨x₀, hx₀⟩ := hdiv z
  obtain ⟨k, hk, hreg⟩ := (h z x₀ hx₀).1 hz
  refine ⟨{w | M.Div S.th x₀ w} ∩ {w | S.th x₀ ^ e / d k ∈ M.O w}, ?_,
    (M.isOpen_setOf_div S.th x₀).inter (M.isOpen_setOf_mem_O _), hx₀, hreg⟩
  rintro w ⟨hw1, hw2⟩
  exact (h w x₀ hw1).2 ⟨k, hk, hw2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverFiniteGroupQuotientStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.isProjOver_finite_group_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (s' : X' ⟶ Sp R), IsProjOver (π ≫ s') → IsProjOver s' := by
  first | exact @GlobalTheory.isProjOver_quotient | exact GlobalTheory.isProjOver_quotient | (intros; apply GlobalTheory.isProjOver_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRepStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → IsProjOver Z.hom ∧ IsProper Z.hom ∧ Out.RelAmple Z M := by
  first | exact @GlobalTheory.ZM.projRep_projective_ample | exact GlobalTheory.ZM.projRep_projective_ample | (intros; apply GlobalTheory.ZM.projRep_projective_ample <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_comp_of_isFinite_noetherianBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) (s : Y ⟶ Sp R), IsFinite f → IsQProjOver s → IsQProjOver (f ≫ s) := by
  first | exact @GlobalTheory.isQProjOver_comp_of_isFinite_noetherian | exact GlobalTheory.isQProjOver_comp_of_isFinite_noetherian | (intros; apply GlobalTheory.isQProjOver_comp_of_isFinite_noetherian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_target_of_isGaloisCover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  first | exact @GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover | exact GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover | (intros; apply GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover <;> assumption)
end

