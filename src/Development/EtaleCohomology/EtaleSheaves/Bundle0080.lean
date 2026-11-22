import Development.EtaleCohomology.EtaleSheaves.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0028
import Development.EtaleCohomology.EtaleSheaves.Bundle0077
import Development.EtaleCohomology.EtaleSheaves.Bundle0075
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.EtaleCohomology.EtaleSheaves.PropertyDescent.LeafPropsDescendOf
import Development.EtaleCohomology.TateTwists.Bundle0032

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf GlobalTheory.GlueModels

namespace LateralTheory.E.LeafGlueTwoPf

def LeafPushoutFP : Prop := ∀ {DW DU DV S : Scheme.{0}} (φU : DW ⟶ DU) (φV : DW ⟶ DV) [IsOpenImmersion φU]
    [IsOpenImmersion φV] (qU : DU ⟶ S) (qV : DV ⟶ S) (h : φU ≫ qU = φV ≫ qV), IsAffine S →
    FP qU → FP qV → FP (φU ≫ qU) → FP (pushout.desc qU qV h)

set_option backward.isDefEq.respectTransparency false in
theorem LeafGlueTwo_of (hF : LeafPushoutFP) : LeafGlueTwo := by
  intro k _ Ω _ _ X f U V R hUV ⟨DU, DV, DW, qU, qV, qW, vU, vV, vW, φU, φV, hqU, hqV, hqW, hφU, hφV, eU, eV,
    pU, pV, pW, cU, cV⟩
  have hc : ∀ x : X, x ∈ Set.range U.ι ∨ x ∈ Set.range V.ι := by
    intro x
    have hx : x ∈ (U ⊔ V : X.Opens) := by rw [hUV]; trivial
    rcases hx with hx | hx
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (by simpa using hx)
  have hsq : IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι := isPullback_opens_inf U V
  have hab : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ vU ≫ pushout.inl φU φV =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ vV ≫ pushout.inr φU φV := by
    rw [← Category.assoc, ← Category.assoc, ← cU, ← cV, Category.assoc, Category.assoc, pushout.condition]
  obtain ⟨v, h1, h2⟩ := exists_glue hsq hc _ _ hab
  have hh : φU ≫ qU = φV ≫ qV := eU.trans eV.symm
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV

  have HV : IsPullback vW (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) φV vV := by
    refine IsPullback.of_bot ?_ cV pV
    rw [← Category.assoc, Scheme.homOfLE_ι, eV]; exact pW
  have HU : IsPullback vW (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) φU vU := by
    refine IsPullback.of_bot ?_ cU pU
    rw [← Category.assoc, Scheme.homOfLE_ι, eU]; exact pW
  have e1 (x : U.toScheme) : v (U.ι x) = pushout.inl φU φV (vU x) := congrArg (fun g => g x) h1
  have e2 (x : V.toScheme) : v (V.ι x) = pushout.inr φU φV (vV x) := congrArg (fun g => g x) h2
  refine ⟨pushout φU φV, pushout.desc qU qV hh, v, hF φU φV qU qV hh inferInstance hqU hqV (eU ▸ hqW), ?_⟩
  refine isPullback_of_two (pushout_cover φU φV) (u' := U.ι) (v' := V.ι) (aU := vU) (aV := vV) ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback HV w x hw
        refine ⟨X.homOfLE inf_le_left z, ?_⟩
        exact congrArg (fun g => g z) hsq.w
    · rintro ⟨y, rfl⟩
      exact ⟨vU y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback HU w x hw
        refine ⟨X.homOfLE inf_le_right z, ?_⟩
        exact (congrArg (fun g => g z) hsq.w).symm
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨vV y, (e2 y).symm⟩
  · simpa only [pushout.inl_desc] using pU
  · simpa only [pushout.inr_desc] using pV

end LateralTheory.E.LeafGlueTwoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPreTensLocInjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafPreTensLocInjPf
open LateralTheory.E.LeafTensMonoPf LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem sec_sgl_zero (F : Shv R) {s : ℤ} (hs : s ≠ 0) {U : Scheme.{0}} (a : Sec ((sgl F).X s) U) : a = 0 := by
  have hZ : IsZero ((sgl F).X s) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hs
  have h1 : (𝟙 ((sgl F).X s)) = 0 := hZ.eq_of_src _ _
  have h2 : Sec.map (𝟙 ((sgl F).X s)) a = a := rfl
  rw [← h2, h1]
  rfl

theorem tens_zero_left (F : Shv R) {J : Cx R} {s t : ℤ} (hs : s ≠ 0) {U : Scheme.{0}}
    (z : Sec ((sgl F).X s) U ⊗[ULift.{1} R] Sec (J.X t) U) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a b => rw [sec_sgl_zero F hs a, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

abbrev p0 (w : ℤ) : {p : ℤ × ℤ // p.1 + p.2 = w} := ⟨(0, w), by simp⟩

theorem tens_single (F : Shv R) {J : Cx R} {U : Scheme.{0}} {w : ℤ} (x : Tens (sgl F) J U w) :
    x = DirectSum.of _ (p0 w) (x (p0 w)) := by
  classical
  ext p
  by_cases hp : p = p0 w
  · subst hp; simp
  · rw [DirectSum.of_eq_of_ne _ _ _ hp]
    have : p.1.1 ≠ 0 := by
      intro h; apply hp; apply Subtype.ext; ext
      · exact h
      · simp; have := p.2; omega
    exact tens_zero_left F this _

theorem tens_res_of {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p t) =
      DirectSum.of _ p (TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom t) := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  unfold Tens.res
  rw [DirectSum.lmap_lof]
  rfl

theorem lift_of {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.of _ p t) = TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2) t := by
  classical
  unfold Pair.lift
  exact DirectSum.toModule_lof (ULift.{1} R)
    (M := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t

end

section
variable {R : Type} [CommRing R]
theorem tens_res_comp {I J : Cx R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : ℤ) (z : Tens I J U w) :
    Tens.res (k ≫ g) w z = Tens.res k w (Tens.res g w z) := by
  classical
  have : (Tens.res (I := I) (J := J) (k ≫ g) w) = (Tens.res k w).comp (Tens.res g w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Tens.res]
  exact LinearMap.congr_fun this z
end

theorem LeafPreTensLocInj_of (hS : LeafTw0LocSplit) : LeafPreTensLocInj := by
  intro q _ i T τ hτ U w x hx
  classical
  obtain ⟨S, hS0⟩ := TensorProduct.exists_finset (x (p0 w))
  set a : Fin S.card → Sec ((sgl (tw q 0)).X 0) U := fun k => (S.equivFin.symm k).1.1 with ha
  set b : Fin S.card → Sec ((res _ (tw q i)).X w) U := fun k => (S.equivFin.symm k).1.2 with hb
  have hxp : x (p0 w) = ∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k := by
    rw [hS0, ← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp S.equivFin.symm (fun i : S => i.1.1 ⊗ₜ[ULift.{1} (ZMod q)] i.1.2)).symm
  have hx' : x = DirectSum.of _ (p0 w) (∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k) := by
    rw [← hxp]; exact tens_single _ x
  set y : Tens (res _ (tw q 0)) (res _ (tw q i)) U w :=
    DirectSum.of _ (p0 w) (∑ k, Sec.map ((resAug (tw q 0)).f 0) (a k) ⊗ₜ[ULift.{1} (ZMod q)] b k) with hydef
  have hy : τ.lift U w y = 0 := by
    rw [← hx, hx', hydef, lift_of, lift_of]
    simp [pre]
  refine loc_trans (hτ.2 U w y hy) ?_
  intro V g hg
  refine loc_trans (hS q V S.card (fun k => Sec.res g (a k))) ?_
  rintro W k ⟨e, c, hac, he⟩
  suffices h : Tens.res (k ≫ g) w x = 0 from
    ⟨⊤, GrothendieckTopology.top_mem _ W, fun W' k' _ => by dsimp only; rw [Category.assoc, tens_res_comp, h, map_zero]⟩
  set bb : Sec ((res _ (tw q i)).X w) W := ∑ j, c j • Sec.res (k ≫ g) (b j) with hbb
  have hres : Tens.res (k ≫ g) w x = DirectSum.of _ (p0 w) (e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by
    rw [hx', tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (a j) = c j • e
    rw [res_comp]; exact hac j
  have hy0 : Tens.res (k ≫ g) w y =
      DirectSum.of _ (p0 w) (Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by
    rw [hydef, tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (Sec.map ((resAug (tw q 0)).f 0) (a j)) = c j • Sec.map ((resAug (tw q 0)).f 0) e
    rw [res_map, res_comp, hac j]
    exact map_smul (((resAug (tw q 0)).f 0).hom.app (op W)).hom (c j) e
  have hg0 : Tens.res (k ≫ g) w y = 0 := by rw [tens_res_comp, hg, map_zero]
  have ht : Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb = 0 :=
    DirectSum.of_injective (p0 w) (hy0.symm.trans (hg0.trans (map_zero _).symm))
  rw [hres]
  rcases he with he | ⟨r, hr⟩
  · rw [he, TensorProduct.zero_tmul, map_zero]
  · have hbb0 : bb = 0 := by
      have := congrArg (fun z => TensorProduct.lid (ULift.{1} (ZMod q)) _ (TensorProduct.map r LinearMap.id z)) ht
      simpa [hr] using this
    rw [hbb0, TensorProduct.tmul_zero, map_zero]

end LateralTheory.E.LeafPreTensLocInjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSHNbSysOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf LateralTheory.E.StrictHenselianNeighbourhood

namespace LateralTheory.E.EtaleNeighbourhoodSystem

section
variable {S : Scheme.{0}} {Ω : Type} [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)

abbrev Fb : S.Etale ⥤ Type := Scheme.Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))

lemma exists_affine (i : (Fb s).Elements) :
    ∃ j : (Fb s).Elements, IsAffine j.1.left ∧ Nonempty (j ⟶ i) := by
  rcases i with ⟨X, x⟩
  cases X with | _ Y f
  obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
  dsimp at y hy
  obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec R ⟶ Y)
      (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
    obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (x := y.base default) (U := ⊤) (by simp)
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  refine ⟨⟨(Scheme.AffineEtale.Spec S).obj (Scheme.AffineEtale.mk (j ≫ f)), Over.homMk y'⟩, ?_,
    ⟨⟨MorphismProperty.Over.homMk j rfl trivial, by cat_disch⟩⟩⟩
  change IsAffine (Spec R)
  infer_instance

lemma exists_small : ∃ (Q : Set (Fb s).Elements), Small.{0} Q ∧ (∀ j ∈ Q, IsAffine j.1.left) ∧
    ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i) := by
  haveI : InitiallySmall.{0} (Fb s).Elements := (Scheme.pointSmallEtale s).initiallySmall
  obtain ⟨Q0, hQ0, h0⟩ := InitiallySmall.exists_small_weakly_initial_set.{0} (Fb s).Elements
  choose g hg hg' using exists_affine s
  refine ⟨g '' Q0, ?_, ?_, ?_⟩
  · haveI := hQ0; infer_instance
  · rintro _ ⟨i, -, rfl⟩; exact hg i
  · intro i
    obtain ⟨k, hk, ⟨f⟩⟩ := h0 i
    exact ⟨g k, ⟨k, hk, rfl⟩, ⟨(hg' k).some ≫ f⟩⟩

variable (Q : Set (Fb s).Elements) [Small.{0} Q]

def ι : Shrink.{0} Q → (Fb s).Elements := fun q => ((equivShrink Q).symm q).1
lemma ι_mem (q : Shrink.{0} Q) : ι s Q q ∈ Q := ((equivShrink Q).symm q).2

abbrev Jc := InducedCategory (Fb s).Elements (ι s Q)

lemma exists_of_wi (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) (d : (Fb s).Elements) :
    ∃ c : Jc s Q, Nonempty ((ι s Q c) ⟶ d) := by
  obtain ⟨j, hj, ⟨f⟩⟩ := hwi d
  exact ⟨equivShrink Q ⟨j, hj⟩, ⟨eqToHom (by simp [ι]) ≫ f⟩⟩

lemma cof (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) : IsCofiltered (Jc s Q) := by
  have h := exists_of_wi s Q hwi
  obtain ⟨d⟩ := IsCofiltered.nonempty (C := (Fb s).Elements)
  exact
  { cone_objs := fun a b => by
      obtain ⟨c, ⟨hc⟩⟩ := h (IsCofiltered.min (ι s Q a) (ι s Q b))
      exact ⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.minToLeft _ _),
        InducedCategory.homMk (hc ≫ IsCofiltered.minToRight _ _), trivial⟩
    cone_maps := fun a b f g => by
      obtain ⟨c, ⟨hc⟩⟩ := h (IsCofiltered.eq f.hom g.hom)
      refine ⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.eqHom f.hom g.hom), ?_⟩
      apply InducedCategory.hom_ext
      show (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ f.hom = (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ g.hom
      rw [Category.assoc, Category.assoc, IsCofiltered.eq_condition]
    nonempty := ⟨(h d).choose⟩ }

def G : Jc s Q ⥤ Scheme.{0} :=
  inducedFunctor (ι s Q) ⋙ CategoryOfElements.π (Fb s) ⋙ Scheme.Etale.forget S ⋙ Over.forget S

def D : (Jc s Q)ᵒᵖ ⥤ CommRingCat.{0} := (G s Q).op ⋙ Scheme.Γ

end

section Sys
variable {B : Scheme.{0}} {U : B.Etale} {Ω : Type} [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) (Q : Set (Fb s).Elements) [Small.{0} Q]

def pt (j : Jc s Q) : Spec (CommRingCat.of Ω) ⟶ (G s Q).obj j := (ι s Q j).2.left

lemma pt_w (j : Jc s Q) : pt s Q j ≫ (ι s Q j).1.hom = s := Over.w (ι s Q j).2

lemma G_w {j k : Jc s Q} (m : k ⟶ j) : (G s Q).map m ≫ (ι s Q j).1.hom = (ι s Q k).1.hom :=
  MorphismProperty.Over.w m.hom.1

lemma pt_map {j k : Jc s Q} (m : k ⟶ j) : pt s Q k ≫ (G s Q).map m = pt s Q j :=
  congrArg CommaMorphism.left m.hom.2

def V (j : (Jc s Q)ᵒᵖ) : B.Etale :=
  MorphismProperty.Over.mk ⊤ ((ι s Q j.unop).1.hom ≫ U.hom)
    (by have := (ι s Q j.unop).1.prop; have := U.prop; exact Etale.etale_comp _ _)

def a (j : (Jc s Q)ᵒᵖ) : V s Q j ⟶ U :=
  MorphismProperty.Over.homMk (ι s Q j.unop).1.hom rfl trivial

variable (haff : ∀ j ∈ Q, IsAffine j.1.left)
include haff

lemma aff (j : Jc s Q) : IsAffine ((G s Q).obj j) := haff _ (ι_mem s Q j)

def e (j : (Jc s Q)ᵒᵖ) : Sp ((D s Q).obj j) ⟶ (G s Q).obj j.unop :=
  haveI := aff s Q haff j.unop; ((G s Q).obj j.unop).isoSpec.inv

lemma e_iso (j : (Jc s Q)ᵒᵖ) : IsIso (e s Q haff j) := by unfold e; exact Iso.isIso_inv _

def l (j : (Jc s Q)ᵒᵖ) : Spec (CommRingCat.of Ω) ⟶ Sp ((D s Q).obj j) :=
  haveI := aff s Q haff j.unop; pt s Q j.unop ≫ ((G s Q).obj j.unop).isoSpec.hom

lemma l_e (j : (Jc s Q)ᵒᵖ) : l s Q haff j ≫ e s Q haff j = pt s Q j.unop := by
  unfold l e
  exact (Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))

lemma nat {j k : (Jc s Q)ᵒᵖ} (f : j ⟶ k) :
    Spec.map ((D s Q).map f) ≫ e s Q haff j = e s Q haff k ≫ (G s Q).map f.unop := by
  haveI := aff s Q haff j.unop; haveI := aff s Q haff k.unop
  exact Scheme.isoSpec_inv_naturality ((G s Q).map f.unop)

def t (j0 : (Jc s Q)ᵒᵖ) : Sp (colimit.cocone (D s Q)).pt ⟶ U.left :=
  Spec.map ((colimit.cocone (D s Q)).ι.app j0) ≫ e s Q haff j0 ≫ (ι s Q j0.unop).1.hom

lemma main (x : U.left) (hx : s default = x) (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (_ : IsColimit c) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t := by
  haveI := cof s Q hwi
  obtain ⟨j0⟩ := IsFiltered.nonempty (C := (Jc s Q)ᵒᵖ)
  have hcomp0 : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k),
      Spec.map ((D s Q).map f) ≫ e s Q haff j ≫ (a s Q j).left = e s Q haff k ≫ (a s Q k).left := by
    intro j k f
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (a s Q j).left) (nat s Q haff f)).trans
      ((Category.assoc _ _ _).trans (congrArg (e s Q haff k ≫ ·) (G_w s Q f.unop))))
  have key : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k),
      Spec.map ((colimit.cocone (D s Q)).ι.app j) ≫ e s Q haff j ≫ (a s Q j).left =
        Spec.map ((colimit.cocone (D s Q)).ι.app k) ≫ e s Q haff k ≫ (a s Q k).left := by
    intro j k f
    rw [← (colimit.cocone (D s Q)).w f, Spec.map_comp, Category.assoc, hcomp0 j k f]
  refine ⟨(Jc s Q)ᵒᵖ, inferInstance, inferInstance, D s Q, colimit.cocone _, colimit.isColimit _,
    V s Q, a s Q, l s Q haff, e s Q haff, t s Q haff j0, hx, e_iso s Q haff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    erw [reassoc_of% (l_e s Q haff j)]
    exact pt_w s Q j.unop
  · intro j k f
    have := hcomp0 j k f
    simp only [CommRingCat.ofHom_hom]
    exact this
  · intro j
    simp only [CommRingCat.ofHom_hom]
    obtain ⟨k, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs j j0
    erw [key j k f, ← key j0 k g]
    rfl
  · intro j k f
    haveI := e_iso s Q haff j
    rw [← cancel_mono (e s Q haff j)]
    simp only [CommRingCat.ofHom_hom, Category.assoc]
    rw [nat, reassoc_of% (l_e s Q haff k), l_e, pt_map]
  · intro U' b l' hl'
    let X' : U.left.Etale := MorphismProperty.Over.mk ⊤ b.left inferInstance
    obtain ⟨c, ⟨hc⟩⟩ := exists_of_wi s Q hwi ⟨X', Over.homMk l' hl'⟩
    refine ⟨op c, hc.1.left, MorphismProperty.Over.w hc.1, ?_⟩
    erw [reassoc_of% (l_e s Q haff (op c))]
    exact congrArg CommaMorphism.left hc.2
  · intro U' b j g g' hg hg' heq
    erw [reassoc_of% (l_e s Q haff j), reassoc_of% (l_e s Q haff j)] at heq
    let X' : U.left.Etale := MorphismProperty.Over.mk ⊤ b.left inferInstance
    have hy : (pt s Q j.unop ≫ g) ≫ b.left = s := by
      exact (Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) hg).trans (pt_w s Q j.unop))
    let y : (Fb s).Elements := ⟨X', Over.homMk (pt s Q j.unop ≫ g) hy⟩
    let u : ι s Q j.unop ⟶ y := ⟨MorphismProperty.Over.homMk (B := X') g hg trivial,
      by apply Over.OverMorphism.ext; rfl⟩
    let u' : ι s Q j.unop ⟶ y := ⟨MorphismProperty.Over.homMk (B := X') g' hg' trivial,
      by apply Over.OverMorphism.ext; exact heq.symm⟩
    obtain ⟨c, ⟨hc⟩⟩ := exists_of_wi s Q hwi (IsCofiltered.eq u u')
    let m : c ⟶ j.unop := InducedCategory.homMk (hc ≫ IsCofiltered.eqHom u u')
    refine ⟨op c, m.op, ?_⟩
    have h0 : (hc ≫ IsCofiltered.eqHom u u') ≫ u = (hc ≫ IsCofiltered.eqHom u u') ≫ u' := by
      rw [Category.assoc, Category.assoc, IsCofiltered.eq_condition]
    have h1 := congrArg (fun z => z.1.left) h0
    simp only [CommRingCat.ofHom_hom]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) (nat s Q haff m.op)).trans ((Category.assoc _ _ _).trans
      ((congrArg (e s Q haff (op c) ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g') (nat s Q haff m.op)).symm.trans (Category.assoc _ _ _))))))

end Sys

theorem LeafSHNbSys_of : LeafSHNbSys := by
  intro B U x
  let Ω := SeparableClosure (U.left.residueField x)
  let s : Spec (CommRingCat.of Ω) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)) ≫ U.left.fromSpecResidueField x
  have hx : s default = x := by
    first | exact Scheme.fromSpecResidueField_apply x _ | (simp [s]; exact Scheme.fromSpecResidueField_apply x _)
  obtain ⟨Q, hQs, haff, hwi⟩ := exists_small s
  haveI := hQs
  exact ⟨Ω, inferInstance, inferInstance, s, main s Q haff x hx hwi⟩

end LateralTheory.E.EtaleNeighbourhoodSystem
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSHSievePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHSievePf

theorem LeafSHSieve_of : LateralTheory.E.LeafClosedSH0Pf.LeafSHSieve := by
  intro X _ hSH S hS
  obtain ⟨hHens, hSep⟩ := hSH
  let A : Type := Γ(X, ⊤)
  let K : Type := IsLocalRing.ResidueField A
  let π : A →+* K := IsLocalRing.residue A
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  let x : Spec (.of K) ⟶ X := Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber K).jointly_surjective _
    (Scheme.Cover.mem_grothendieckTopology 𝒰) x
  obtain ⟨Z, h, _, ⟨i⟩, rfl⟩ := hg
  have hy' : (y ≫ h) ≫ 𝒰.f i = Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv := by
    exact (Category.assoc _ _ _).trans hy
  obtain ⟨l, ⟨-, hl⟩, -⟩ := GlobalTheory.existsUnique_lift_of_etale_of_henselian (𝒰.f i) π
    IsLocalRing.residue_surjective (y ≫ h) X.isoSpec.inv hy'
  have hmem : S (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have := S.downward_closed hmem (X.isoSpec.hom ≫ l)
  have e : (X.isoSpec.hom ≫ l) ≫ 𝒰.f i = 𝟙 X := by rw [Category.assoc, hl, Iso.hom_inv_id]
  rwa [e] at this

end LateralTheory.E.LeafSHSievePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadProperPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafSpreadProperPf

def LeafSpreadSeparated : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsSeparated c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → IsSeparated q'

def LeafSpreadUnivClosed : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsProper c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → UniversallyClosed q'

end LateralTheory.E.LeafSpreadProperPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoGenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoGenPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => h V g⟩

theorem flatS_of_sec {R : Type} [CommRing R] (M : Shv R)
    (h : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} R) (Sec M U)) : FlatS M := by
  refine ⟨M.obj, 𝟙 _, ?_, ?_, ?_⟩
  · intro U y
    exact loc_top U _ (fun V g => ⟨Sec.res g y, rfl⟩)
  · intro U x hx
    have hx0 : x = 0 := hx
    subst hx0
    exact loc_top U _ (fun V g => map_zero _)
  · intro U _
    exact h U

theorem LeafTensQIsoGen_of : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := by
  intro R _ I I' J S T f hf hI hI' hJ hflat σ τ hσ hτ ι hι
  exact LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange R σ τ hσ hτ (fun t => flatS_of_sec _ (hflat t)) f ι
    (fun U s t w h a b => by rw [hι U s t w h a b]; rfl)

end LateralTheory.E.LeafTensQIsoGenPf
end
end

