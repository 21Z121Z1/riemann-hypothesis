import Development.EtaleCohomology.EtaleSheaves.Bundle0015
import Development.EtaleCohomology.EtaleSheaves.Bundle0008
import Development.EtaleCohomology.EtaleSheaves.Bundle0006
import Development.EtaleCohomology.EtaleSheaves.Bundle0007
import Development.EtaleCohomology.EtaleSheaves.Bundle0012

-- bundled from Development.EtaleCohomology.EtaleSheaves.AICOpenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial

namespace LateralTheory.E.AICOpenPf
open LateralTheory.E.t_E2Cut LateralTheory.E.SteinPf

theorem roots_in {A K : Type} [CommRing A] [IsDomain A] [CommRing K] [IsDomain K] (φ : A →+* K) (hA : AIC A) :
    ∀ n (p : A[X]), p.natDegree = n → p.Monic → ∀ β : K, (p.map φ).eval β = 0 → ∃ a, φ a = β := by
  intro n
  induction n with
  | zero =>
    intro p hd hm β hβ
    have : p = 1 := hm.natDegree_eq_zero.mp hd
    subst this; simp at hβ
  | succ n ih =>
    intro p hd hm β hβ
    obtain ⟨a, ha⟩ := hA p hm (by omega)
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqm : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hm)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hfac, Polynomial.map_mul, eval_mul, mul_eq_zero] at hβ
    rcases hβ with h | h
    · refine ⟨a, ?_⟩
      simp at h; rw [sub_eq_zero] at h; exact h.symm
    · exact ih _ hqd hqm β h

theorem gtf_res {Z : Scheme.{0}} [IsIntegral Z] {U W : Z.Opens} (i : U ⟶ W) [Nonempty U] [Nonempty W] (s : Γ(Z, W)) :
    Z.germToFunctionField U (Z.presheaf.map i.op s) = Z.germToFunctionField W s := by
  simp only [Scheme.germToFunctionField]
  rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res]

theorem gtf_res_hom {Z : Scheme.{0}} [IsIntegral Z] {U W : Z.Opens} (i : U ⟶ W) [Nonempty U] [Nonempty W] :
    (Z.germToFunctionField U).hom.comp (Z.presheaf.map i.op).hom = (Z.germToFunctionField W).hom := by
  ext s; exact gtf_res i s

theorem AICOpen_of : AICOpen := by
  intro Z hZ W hW p hm hd
  have : IsIntegral Z := hZ.1
  have : Nonempty W := ⟨⟨_, hW.some_mem⟩⟩
  have hcov : ∀ x : W, ∃ U : Z.Opens, IsAffineOpen U ∧ (x : Z) ∈ U ∧ U ≤ W := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.isOpen
    exact ⟨U, hU, hxU, hUW⟩
  choose U hUa hxU hUW using hcov
  have hne : ∀ x : W, Nonempty (U x) := fun x => ⟨⟨_, hxU x⟩⟩
  let ψ := Z.germToFunctionField W

  have hroot : ∀ x : W, ∃ β : Z.functionField, (p.map ψ.hom).eval β = 0 := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hZ.2 _ (hUa x) ⟨_, hxU x⟩
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    obtain ⟨r, hr⟩ := hA (p.map ρ) (hm.map ρ) (by rw [hm.natDegree_map]; exact hd)
    refine ⟨Z.germToFunctionField (U x) r, ?_⟩
    rw [← gtf_res_hom (homOfLE (hUW x)), ← Polynomial.map_map, Polynomial.eval_map_apply, hr, map_zero]
  obtain ⟨β, hβ⟩ := hroot ⟨_, hW.some_mem⟩
  have hsec : ∀ x : W, ∃ t : Γ(Z, U x), Z.germToFunctionField (U x) t = β := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hZ.2 _ (hUa x) ⟨_, hxU x⟩
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    exact roots_in (Z.germToFunctionField (U x)).hom hA _ (p.map ρ) rfl (hm.map ρ) β
      (by rw [Polynomial.map_map, gtf_res_hom]; exact hβ)
  choose sf hsf using hsec
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have := hne i; have := hne j
    have hij : ((U i ⊓ U j : Z.Opens) : Set Z).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨_, hxU i⟩ ⟨_, hxU j⟩
    have : Nonempty (U i ⊓ U j : Z.Opens) := ⟨⟨_, hij.some_mem⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.germToFunctionField _ (Z.presheaf.map _ (sf i)) = Z.germToFunctionField _ (Z.presheaf.map _ (sf j))
    rw [gtf_res, gtf_res, hsf, hsf]
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (U := U) (V := W) (iUV := fun x => homOfLE (hUW x))
    (hcover := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU _⟩) (sf := sf) (h := hcompat)
  have hsβ : ψ s = β := by
    have h0 := hs ⟨_, hW.some_mem⟩
    have := hne ⟨_, hW.some_mem⟩
    rw [← hsf ⟨_, hW.some_mem⟩, ← gtf_res (homOfLE (hUW ⟨_, hW.some_mem⟩)) s]
    exact congrArg _ h0
  obtain ⟨t, ht⟩ : ∃ t : Γ(Z, W), ψ t = β := ⟨s, hsβ⟩
  refine ⟨t, Z.germToFunctionField_injective W ?_⟩
  rw [map_zero]
  have key : ψ.hom (p.eval t) = (p.map ψ.hom).eval (ψ.hom t) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  change ψ.hom (p.eval t) = 0
  rw [key]; change (p.map ψ.hom).eval (ψ t) = 0
  rw [ht]; exact hβ

end LateralTheory.E.AICOpenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AffinePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.GlobalPf

namespace LateralTheory.E.AffinePf

theorem eqv_of_sq (R : Type) [CommRing R] (F : Shv R) {E₁ E₂ E₁' E₂' : Spc} (f : E₁ ⟶ E₂) (f' : E₁' ⟶ E₂')
    (a : E₁ ≅ E₁') (b : E₂ ≅ E₂') (h : f ≫ b.hom = a.hom ≫ f') (hf : Eqv R f' F) : Eqv R f F := fun n => by
  have hiso : ∀ {X Y : Spc} (e : X ≅ Y), Function.Bijective (pull R e.hom F n) := fun e => by
    refine ⟨Function.LeftInverse.injective (g := pull R e.inv F n) fun x => ?_,
      Function.RightInverse.surjective (g := pull R e.inv F n) fun x => ?_⟩
    · rw [← pull_comp, e.inv_hom_id, pull_id]
    · rw [← pull_comp, e.hom_inv_id, pull_id]
  have hf2 : f = a.hom ≫ f' ≫ b.inv := by rw [← Category.assoc, ← h]; simp
  have : ⇑(pull R f F n) = pull R a.hom F n ∘ pull R f' F n ∘ pull R b.inv F n := by
    funext x; rw [hf2]; simp only [Function.comp_apply]; rw [pull_comp, pull_comp]
  rw [this]
  exact (hiso a).comp ((hf n).comp (hiso b.symm))

theorem ι_comp_eq {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens) (hV : IsAffineOpen V) :
    V.ι ≫ p = hV.isoSpec.hom ≫ Spec.map (gam p V) := by
  have h1 : Spec.map (gam p V) = hV.fromSpec ≫ p := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top (Spec T)) hV (by simp)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
    rw [gam, Spec.map_comp]
    exact this
  rw [h1, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

theorem Affine_of : Affine := by
  intro q i T K k X p V hV hb
  have hpo := IsPushout.of_hasPushout k (gam p V)
  have hre := hb _ _ _ hpo
  have hS := isPullback_SpecMap_of_isPushout _ _ _ _ hpo.flip
  have h1 := (isPullback_morphismRestrict (pullback.fst p (Spec.map k)) V).paste_vert
    (IsPullback.of_hasPullback p (Spec.map k))
  have h2 : IsPullback hV.isoSpec.hom (V.ι ≫ p) (Spec.map (gam p V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [ι_comp_eq p V hV, Category.comp_id]⟩
  have h3 := h1.paste_horiz h2
  rw [Category.comp_id] at h3
  refine eqv_of_sq _ _ _ (sch.map (Spec.map (pushout.inr k (gam p V))))
    (sch.mapIso (h3.isoIsPullback _ _ hS)) (sch.mapIso hV.isoSpec) ?_ hre
  simp only [Functor.mapIso_hom, ← Functor.map_comp, IsPullback.isoIsPullback_hom_fst]

end LateralTheory.E.AffinePf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AicschOfImm
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CovPf

theorem aic_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (h : AIC A) : AIC B := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map (e.symm : B →+* A)) (hp.map _) (by
    rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  rw [Polynomial.eval_map] at ha
  have h2 := congrArg (e : A →+* B) ha
  rw [Polynomial.hom_eval₂, map_zero] at h2
  have h3 : ((e : A →+* B).comp (e.symm : B →+* A)) = RingHom.id B := by ext x; simp
  rw [h3] at h2
  exact h2

theorem aicsch_of_imm {W Z : Scheme.{0}} (i : W ⟶ Z) [IsOpenImmersion i] [Nonempty W] (hZ : AICSch Z) :
    AICSch W := by
  have : IsIntegral Z := hZ.1
  refine ⟨isIntegral_of_isOpenImmersion i, fun V hV hne => ?_⟩
  have h1 := hZ.2 (i ''ᵁ V) (hV.image_of_isOpenImmersion i) (by
    obtain ⟨x, hx⟩ := hne; exact ⟨i.base x, x, hx, rfl⟩)
  exact aic_equiv (i.appIso V).commRingCatIsoToRingEquiv h1

theorem unit_of_hom {W Z : Scheme.{0}} (i : W ⟶ Z) (q : ℕ) (hq : IsUnit (q : Γ(Z, ⊤))) :
    IsUnit (q : Γ(W, ⊤)) := by
  have := hq.map (i.appTop).hom
  simpa using this

def R (P : Scheme.{0} → Prop) {Z : Scheme.{0}} (s : Set Z) : Prop :=
  ∀ (W : Scheme.{0}) (i : W ⟶ Z) [IsOpenImmersion i], Set.range i = s → Nonempty W → P W

def StepP (q : ℕ) (P : Scheme.{0} → Prop) : Prop :=
  ∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
    Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
    P U → P V → (Nonempty ↥(pullback f g : Scheme.{0}) → P (pullback f g)) → P X

theorem R_empty (P : Scheme.{0} → Prop) {Z : Scheme.{0}} : R P (∅ : Set Z) := by
  intro W i _ hr hW
  obtain ⟨w⟩ := hW
  have : i.base w ∈ Set.range i := ⟨w, rfl⟩
  rw [hr] at this; exact this.elim

theorem R_aff (q : ℕ) (P : Scheme.{0} → Prop) (haff : ∀ Z : Scheme.{0}, IsAffine Z → AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z)
    {Z : Scheme.{0}} (hZ : AICSch Z) (hq : IsUnit (q : Γ(Z, ⊤))) (A : Z.Opens) (hA : IsAffineOpen A) :
    R P (A : Set Z) := by
  intro W i _ hr hW
  have e : Set.range i = Set.range A.ι := by rw [hr]; simp
  have hWa : IsAffine W := (IsAffine.iff_of_isIso (IsOpenImmersion.isoOfRangeEq i A.ι e).hom).mpr hA
  exact haff W hWa (aicsch_of_imm i hZ) (unit_of_hom i q hq)

theorem R_step (q : ℕ) (P : Scheme.{0} → Prop) (hstep : StepP q P) {Z : Scheme.{0}} (hZ : AICSch Z)
    (hq : IsUnit (q : Γ(Z, ⊤))) {s t : Set Z} (hs : IsOpen s) (ht : IsOpen t)
    (Rs : R P s) (Rt : R P t) (Rst : R P (s ∩ t)) : R P (s ∪ t) := by
  intro W i _ hr hW
  rcases s.eq_empty_or_nonempty with hs0 | ⟨x, hx⟩
  · subst hs0; exact Rt W i (by simpa using hr) hW
  rcases t.eq_empty_or_nonempty with ht0 | ⟨y, hy⟩
  · subst ht0; exact Rs W i (by simpa using hr) hW
  have subs : s ⊆ Set.range i := hr ▸ Set.subset_union_left
  have subt : t ⊆ Set.range i := hr ▸ Set.subset_union_right
  let U' : W.Opens := i ⁻¹ᵁ ⟨s, hs⟩
  let V' : W.Opens := i ⁻¹ᵁ ⟨t, ht⟩
  have rU : Set.range (U'.ι ≫ i) = s := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset subs
  have rV : Set.range (V'.ι ≫ i) = t := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset subt
  obtain ⟨w, hw⟩ := subs hx
  obtain ⟨v, hv⟩ := subt hy
  have neU : Nonempty U'.toScheme := ⟨⟨w, show i.base w ∈ s from hw ▸ hx⟩⟩
  have neV : Nonempty V'.toScheme := ⟨⟨v, show i.base v ∈ t from hv ▸ hy⟩⟩
  have hZW : AICSch W := aicsch_of_imm i hZ
  refine hstep U'.ι V'.ι ?_ hZW (aicsch_of_imm U'.ι hZW) (aicsch_of_imm V'.ι hZW) (unit_of_hom i q hq)
    (Rs _ (U'.ι ≫ i) rU neU) (Rt _ (V'.ι ≫ i) rV neV) (fun hne => Rst _ (pullback.fst U'.ι V'.ι ≫ U'.ι ≫ i) ?_ hne)
  · ext w'
    simp only [Scheme.Opens.range_ι, Set.mem_union, Set.mem_univ, iff_true]
    have : i.base w' ∈ s ∪ t := hr ▸ ⟨w', rfl⟩
    exact this
  · rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset (Set.inter_subset_left.trans subs)

section Topo
variable {Z : Scheme.{0}} (Q : Set Z → Prop) (hE : Q ∅) (hB : ∀ A : Z.Opens, IsAffineOpen A → Q A)
  (hS : ∀ {s t : Set Z}, IsOpen s → IsOpen t → Q s → Q t → Q (s ∩ t) → Q (s ∪ t))
include hE hB hS

theorem stage1 (A : Z.Opens) (hA : IsAffineOpen A) {ι : Type} (t : Finset ι) :
    ∀ f : ι → Γ(Z, A), Q (⋃ i ∈ t, (Z.basicOpen (f i) : Set Z)) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro f; simpa using hE
  | insert a t ha ih =>
    intro f
    rw [Finset.set_biUnion_insert]
    have hI : (Z.basicOpen (f a) : Set Z) ∩ ⋃ i ∈ t, (Z.basicOpen (f i) : Set Z)
        = ⋃ i ∈ t, (Z.basicOpen (f a * f i) : Set Z) := by
      simp [Scheme.basicOpen_mul, Set.inter_iUnion₂]
    refine hS (Z.basicOpen (f a)).isOpen (isOpen_biUnion fun i _ => (Z.basicOpen (f i)).isOpen)
      (hB _ (hA.basicOpen _)) (ih f) ?_
    rw [hI]; exact ih _

theorem stage1' (A : Z.Opens) (hA : IsAffineOpen A) (S : Set Z) (hSo : IsOpen S) (hSc : IsCompact S)
    (hSA : S ⊆ A) : Q S := by
  have hch : ∀ x : S, ∃ f : Γ(Z, A), Z.basicOpen f ≤ ⟨S, hSo⟩ ∧ (x : Z) ∈ Z.basicOpen f :=
    fun x => hA.exists_basicOpen_le (V := ⟨S, hSo⟩) ⟨x.1, x.2⟩ (hSA x.2)
  choose f hf1 hf2 using hch
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun x : S => (Z.basicOpen (f x) : Set Z))
    (fun x => (Z.basicOpen _).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hf2 _⟩)
  have : S = ⋃ i ∈ t, (Z.basicOpen (f i) : Set Z) :=
    subset_antisymm ht (Set.iUnion₂_subset fun i _ => hf1 i)
  rw [this]; exact stage1 Q hE hB hS A hA t f

theorem stage2 [QuasiSeparatedSpace Z] (t : Finset Z.affineOpens) :
    Q (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hE
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert]
    have hTo : IsOpen (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := isOpen_biUnion fun i _ => (i : Z.Opens).isOpen
    have hTc : IsCompact (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := t.isCompact_biUnion fun i _ => i.2.isCompact
    refine hS (a : Z.Opens).isOpen hTo (hB _ a.2) ih ?_
    exact stage1' Q hE hB hS a a.2 _ ((a : Z.Opens).isOpen.inter hTo)
      (QuasiSeparatedSpace.inter_isCompact _ _ (a : Z.Opens).isOpen a.2.isCompact hTo hTc) Set.inter_subset_left

theorem stage3 [CompactSpace Z] [QuasiSeparatedSpace Z] : Q Set.univ := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : Z.affineOpens => ((U : Z.Opens) : Set Z))
    (fun U => (U : Z.Opens).isOpen) (fun x _ => by
      have : x ∈ (⨆ i : Z.affineOpens, (i : Z.Opens)) := by rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this)
  have : (Set.univ : Set Z) = ⋃ i ∈ t, ((i : Z.Opens) : Set Z) := subset_antisymm ht (Set.subset_univ _)
  rw [this]; exact stage2 Q hE hB hS t

end Topo

theorem Cov_of : LateralTheory.E.AICAcycPf.Cov := by
  intro q P hiso haff hstep Z _ _ hZ hq
  have h := stage3 (R P (Z := Z)) (R_empty P) (fun A hA => R_aff q P haff hZ hq A hA)
    (fun hs ht Rs Rt Rst => R_step q P hstep hZ hq hs ht Rs Rt Rst)
  have : IsIntegral Z := hZ.1
  exact h Z (𝟙 Z) (by simp) inferInstance

end LateralTheory.E.CovPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.BuildCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.BuildCut

def ProdACF (W : Type) [CommRing W] : Prop :=
  AIC W ∧ ∀ a : W, ∃ e u : W, IsIdempotentElem e ∧ IsUnit u ∧ a = e * u

def Pts : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (W : Type) (_ : CommRing W) (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W ∧ Surjective w

def LimInt : Prop := ∀ {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D)
  (ι : ∀ j, D.obj j ⟶ Y), ClopenSys y D c ι → ∀ j, IsIntegralHom (c.π.app j ≫ ι j)

def Comp : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ w.normalization),
      ClopenSys y D c ι ∧ AICSch c.pt

theorem goal_of (hP : Pts) (hL : LimInt) (hC : Comp) : Build := by
  intro P _ _
  obtain ⟨W, _, w, hW, hs⟩ := hP (P := P)
  refine ⟨w.normalization, w.fromNormalization, inferInstance, ?_, fun y => ?_⟩
  · have h := hs
    rw [← w.toNormalization_fromNormalization] at h
    exact ⟨Function.Surjective.of_comp h.surj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hA⟩ := hC W w hW y
    refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, hA, fun j => ?_⟩
    have := hL y D c ι hc j
    infer_instance

end LateralTheory.E.BuildCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechFiltPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.CechFiltPf

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (Hrel R (disc.map (g.app (op (SimplexCategory.mk p)))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

def Filt : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (n : ℤ),
  (∀ p : ℕ, Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)) →
  Subsingleton (Hrel R g F n)

theorem CechFilt_of (hP : Piece) (hF : Filt) : LateralTheory.E.SSPf.CechFilt := by
  intro R _ F E₀ E g n h
  exact hF R F g n (fun p => hP R F g p n (h p))

universe u v

def FiltGen : Prop := ∀ {C : Type u} [Category.{v} C] [Abelian C] {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ),
  (∀ j, 0 < j → IsZero (K.X j)) → (∀ j, 0 < j → IsZero (L.X j)) → (∀ j, j < 0 → IsZero (I.X j)) →
  (∀ k ≤ 0, Subsingleton (CohomologyClass (mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n)) →
  Subsingleton (CohomologyClass (mappingCone φ) I n)

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (j : ℤ) (hj : 0 < j) : IsZero (((chains R).obj E).X j) := by
  unfold chains
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show -(i : ℤ) ≠ j
    omega)

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (j : ℤ) (hj : j < 0) : IsZero ((res R F).X j) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show (i : ℤ) ≠ j
    omega)

theorem Filt_of (hG : FiltGen.{2, 1}) : Filt := by
  intro R _ F E₀ E g n h
  apply hG ((chains R).map g) n (chains_isZero R E₀) (chains_isZero R E) (res_isZero R F)
  intro k hk
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
  exact h p

def DiscLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {P Q : PSh} (h : P ⟶ Q) (m : ℤ),
  Subsingleton (Hrel R (disc.map h) F m) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h))) F m)

def ShiftLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map
    ((free R).map (g.app (op (SimplexCategory.mk p)))))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

theorem Piece_of (hD : DiscLvl) (hS : ShiftLvl) : Piece := by
  intro R _ F E₀ E g p n h
  exact hS R F g p n (hD R F _ _ h)

theorem CechFilt_of_disc_shift_filtGen (hD : DiscLvl) (hS : ShiftLvl) (hG : FiltGen.{2, 1}) : LateralTheory.E.SSPf.CechFilt :=
  CechFilt_of (Piece_of hD hS) (Filt_of hG)

end LateralTheory.E.CechFiltPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChainsDiscCoprodPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ChainsDiscCoprodPf

variable (R : Type) [CommRing R]

theorem chains_disc_f {P Q : PSh} (f : P ⟶ Q) (n : ℕ) :
    ((chains R).map (disc.map f)).f (-(n : ℤ)) =
      (chainsXIso R (disc.obj P) n).hom ≫ (free R).map f ≫ (chainsXIso R (disc.obj Q) n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem isZero_chains_X (E : Spc) (i : ℤ) (hi : ∀ n : ℕ, -(n : ℤ) ≠ i) :
    IsZero (((chains R).obj E).X i) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat i (fun n => hi n)

theorem cofan_of_isos {C : Type*} [Category C] {ι : Type} {A A' : ι → C} {B B' : C}
    (a : ∀ j, A' j ≅ A j) (b : B' ≅ B) (f : ∀ j, A j ⟶ B) (f' : ∀ j, A' j ⟶ B')
    (hf : ∀ j, f' j = (a j).hom ≫ f j ≫ b.inv) (hc : IsColimit (Cofan.mk B f)) :
    Nonempty (IsColimit (Cofan.mk B' f')) := by
  refine ⟨Cofan.IsColimit.mk _ (fun s => b.hom ≫ hc.desc (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j)) ?_ ?_⟩
  · intro s j
    have := hc.fac (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j) ⟨j⟩
    simp only [Cofan.mk_ι_app] at this
    change f' j ≫ _ = _
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc, this, Iso.hom_inv_id_assoc]
  · intro s m hm
    rw [← Iso.inv_comp_eq]
    refine hc.uniq (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j) _ ?_
    rintro ⟨j⟩
    change f j ≫ b.inv ≫ m = (a j).inv ≫ s.inj j
    rw [← hm j]
    change f j ≫ b.inv ≫ m = (a j).inv ≫ f' j ≫ m
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc]

theorem cofan_of_zero {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type} {A : ι → C} {B : C}
    (hA : ∀ j, IsZero (A j)) (hB : IsZero B) (f : ∀ j, A j ⟶ B) :
    Nonempty (IsColimit (Cofan.mk B f)) :=
  ⟨Cofan.IsColimit.mk _ (fun _ => 0) (fun _ j => (hA j).eq_of_src _ _) (fun _ _ _ => hB.eq_of_src _ _)⟩

theorem degColimit {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q)
    (hc : IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) (i : ℤ) :
    Nonempty (IsColimit ((HomologicalComplex.eval _ _ i).mapCocone
      (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))) := by
  rw [(isColimitMapCoconeCofanMkEquiv _ _ _).nonempty_congr]
  by_cases h : 0 < i
  · have h' : ∀ n : ℕ, -(n : ℤ) ≠ i := fun n => by omega
    exact cofan_of_zero (fun j => isZero_chains_X R _ i h') (isZero_chains_X R _ i h') _
  · have hi : i = -(((-i).toNat : ℕ) : ℤ) := by omega
    rw [hi]
    generalize (-i).toNat = n
    exact cofan_of_isos (fun j => chainsXIso R (disc.obj (P j)) n) (chainsXIso R (disc.obj Q) n)
      (fun j => (free R).map (p j)) _ (fun j => chains_disc_f R (p j) n) hc

theorem ChainsDiscCoprod_of : LateralTheory.E.CoprodPf.ChainsDiscCoprod := by
  intro R _ ι P Q p ⟨hc⟩
  exact ⟨HomologicalComplex.isColimitOfEval _ _ (fun i => (degColimit R P Q p hc i).some)⟩

end LateralTheory.E.ChainsDiscCoprodPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartSurjCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.ChartSurjCut

def Root : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  AICSch Z → IsUnit (q : A) → Nonempty (Prim q Γ(Z, ⊤))

def LCIso : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Ht q (sch.obj X) 0 i,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      pull _ (sch.map f) (tw q i) 0 (e X s g) = e Y t (g.comap f.base.hom)

def LCSurj : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  ∀ g : LocallyConstant ↥(pullback (fibMap p ι₁) (fibMap p ι₂)) (ZMod q),
    ∃ (a : LocallyConstant ↥(fib (ι₁ ≫ p)) (ZMod q)) (b : LocallyConstant ↥(fib (ι₂ ≫ p)) (ZMod q)),
      g = a.comap (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base.hom -
        b.comap (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base.hom

theorem goal_of (hR : Root) (hL : LCIso) (hT : LCSurj) : ChartSurj := by
  unfold Root at hR
  unfold LCIso at hL
  unfold LCSurj at hT
  intro H q i A _ _ hSH hq Z U V p hp hZ ι₁ ι₂ h1 h2 hU hV hcov w
  obtain ⟨ζ⟩ := hR q A p hZ hq
  obtain ⟨e, he⟩ := hL H q i Z ζ
  have k1 : fibMap p ι₁ ≫ pullback.fst p (cpt A) = pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have k2 : fibMap p ι₂ ≫ pullback.fst p (cpt A) = pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have eq : pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ =
      pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by
    rw [← k2, ← k1, ← Category.assoc, ← pullback.condition, Category.assoc]
  obtain ⟨a, b, hab⟩ := hT q A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov
    ((e _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁)).symm w)
  refine ⟨e _ (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁) a, e _ (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂) b, ?_⟩
  rw [he _ _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂)) rfl, he _ _ (pullback.snd (fibMap p ι₁) (fibMap p ι₂)) eq,
    ← map_sub, ← hab, AddEquiv.apply_symm_apply]

end LateralTheory.E.ChartSurjCut
end
end

