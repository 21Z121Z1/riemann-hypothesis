import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0012

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PPullbackFaithful
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency.types false in

theorem pullback_map_injective_unit {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A : U.Modules}
    (φ₁ φ₂ : A ⟶ structureModule U)
    (h : (Scheme.Modules.pullback g).map φ₁ = (Scheme.Modules.pullback g).map φ₂) : φ₁ = φ₂ := by
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have key : ∀ φ : A ⟶ structureModule U,
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _)
        ((Scheme.Modules.pullback g).map φ ≫
          SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) =
      φ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    intro φ
    rw [Adjunction.homEquiv_naturality_left]
    congr 1
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have h2 : φ₁ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom =
      φ₂ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    rw [← key, ← key, h]
  ext W x
  have := congr((($h2).app W).hom x)
  exact hg W this

section Coordinates

variable {X : Scheme.{u}} {B : X.Modules} {n : ℕ} {s : Fin n → Γ(B, ⊤)}

variable (B s) in

def basisExpand (W : X.Opens) : (Fin n → Γ(X, W)) →ₗ[Γ(X, W)] Γ(B, W) :=
  Fintype.linearCombination Γ(X, W)
    (fun i => (B.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom (s i))

lemma basisExpand_apply (W : X.Opens) (r : Fin n → Γ(X, W)) :
    basisExpand B s W r = ∑ i, r i • (B.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom (s i) :=
  Fintype.linearCombination_apply _ _ _

lemma basisExpand_map {W W' : X.Opens} (i : W' ≤ W) (r : Fin n → Γ(X, W)) :
    (B.presheaf.map (homOfLE i).op).hom (basisExpand B s W r) =
      basisExpand B s W' (fun k => (X.presheaf.map (homOfLE i).op).hom (r k)) := by
  rw [basisExpand_apply, basisExpand_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Scheme.Modules.map_smul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

def basisEquiv (hs : IsBasisOn B ⊤ s) (W : X.Opens) :
    (Fin n → Γ(X, W)) ≃ₗ[Γ(X, W)] Γ(B, W) :=
  LinearEquiv.ofBijective (basisExpand B s W) (by
    have := hs W le_top
    convert this using 1
    funext r
    exact basisExpand_apply W r)

lemma basisEquiv_symm_map (hs : IsBasisOn B ⊤ s) {W W' : X.Opens} (i : W' ≤ W) (x : Γ(B, W))
    (k : Fin n) :
    (basisEquiv hs W').symm ((B.presheaf.map (homOfLE i).op).hom x) k =
      (X.presheaf.map (homOfLE i).op).hom ((basisEquiv hs W).symm x k) := by
  obtain ⟨r, rfl⟩ := (basisEquiv hs W).surjective x
  rw [LinearEquiv.symm_apply_apply]
  have : (B.presheaf.map (homOfLE i).op).hom (basisEquiv hs W r) =
      basisEquiv hs W' (fun k => (X.presheaf.map (homOfLE i).op).hom (r k)) :=
    basisExpand_map i r
  rw [this, LinearEquiv.symm_apply_apply]

def basisCoord (hs : IsBasisOn B ⊤ s) (j : Fin n) : B ⟶ structureModule X :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        ((LinearMap.proj j ∘ₗ (basisEquiv hs W.unop).symm.toLinearMap).toAddMonoidHom)
      naturality := fun W W' f => by
        ext x
        exact basisEquiv_symm_map hs (leOfHom f.unop) x j }
    (fun W r x =>
      (LinearMap.proj j ∘ₗ (basisEquiv hs W.unop).symm.toLinearMap).map_smul r x)⟩

theorem eq_of_basisCoord (hs : IsBasisOn B ⊤ s) {A : X.Modules} (ψ₁ ψ₂ : A ⟶ B)
    (h : ∀ j, ψ₁ ≫ basisCoord hs j = ψ₂ ≫ basisCoord hs j) : ψ₁ = ψ₂ := by
  ext W x
  apply (basisEquiv hs W).symm.injective
  funext j
  exact congr((($(h j)).app W).hom x)

end Coordinates

theorem pullback_faithful_of_basis {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A B : U.Modules} {n : ℕ}
    {s : Fin n → Γ(B, ⊤)} (hs : IsBasisOn B ⊤ s) (ψ₁ ψ₂ : A ⟶ B)
    (h : (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂) : ψ₁ = ψ₂ :=
  eq_of_basisCoord hs ψ₁ ψ₂ fun j => pullback_map_injective_unit g hg _ _
    (by rw [Functor.map_comp, Functor.map_comp, h])

set_option backward.isDefEq.respectTransparency.types false in

theorem restrict_map_eq_of_pullback {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A B : U.Modules} (V : U.Opens) {n : ℕ}
    {s : Fin n → Γ(B, V)} (hs : IsBasisOn B V s) (ψ₁ ψ₂ : A ⟶ B)
    (h : (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂) :
    (Scheme.Modules.restrictFunctor V.ι).map ψ₁ = (Scheme.Modules.restrictFunctor V.ι).map ψ₂ := by
  have hs' := (hs.restrict V.ι_image_top.le).restrictImage V.ι
  have hg' : ∀ W, Function.Injective ((g ∣_ V).app W) := by
    intro W
    rw [morphismRestrict_app]
    exact (ConcreteCategory.bijective_of_isIso
      (T.presheaf.map (eqToHom (image_morphismRestrict_preimage g V W)).op)).1.comp (hg _)
  let E : Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback (g ∣_ V) ≅
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback (g ⁻¹ᵁ V).ι :=
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι) _ ≪≫
      Scheme.Modules.pullbackComp _ _ ≪≫
        Scheme.Modules.pullbackCongr (morphismRestrict_ι g V) ≪≫
          (Scheme.Modules.pullbackComp _ _).symm
  apply pullback_faithful_of_basis (g ∣_ V) hg' hs'
  refine (NatIso.naturality_2 E ψ₁).symm.trans (Eq.trans ?_ (NatIso.naturality_2 E ψ₂))
  simp only [Functor.comp_map, h]

theorem PullbackFaithful.proof : PullbackFaithful.Statement := by
  intro T U g hg A B hB ψ₁ ψ₂ h
  choose V hVa hxV n s hs using hB
  have loc : ∀ x : U, (Scheme.Modules.restrictFunctor (V x).ι).map ψ₁ =
      (Scheme.Modules.restrictFunctor (V x).ι).map ψ₂ :=
    fun x => restrict_map_eq_of_pullback g hg (V x) (hs x) ψ₁ ψ₂ h
  ext W a
  let F : TopCat.Sheaf Ab U := ⟨B.presheaf, B.isSheaf⟩
  refine F.eq_of_locally_eq' (fun x : W => (V x).ι ''ᵁ ((V x).ι ⁻¹ᵁ W)) W
    (fun x => homOfLE ((V x.1).ι.image_preimage_le W)) ?_ _ _ fun x => ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, ⟨y, hxV y⟩, hy, rfl⟩
  · change (B.presheaf.map _).hom ((ψ₁.app W).hom a) = (B.presheaf.map _).hom ((ψ₂.app W).hom a)
    rw [← app_map_apply, ← app_map_apply]
    exact congr((($(loc x.1)).app ((V x.1).ι ⁻¹ᵁ W)).hom _)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

section Trans

variable {S T Y Z : Scheme.{0}}

lemma pullbackCompIso_trans {g₁ : S ⟶ T} {g₂ : T ⟶ Y} {h : Y ⟶ Z} {k₂ : T ⟶ Z} {k : S ⟶ Z}
    {g : S ⟶ Y} (e₂ : g₂ ≫ h = k₂) (e₁ : g₁ ≫ k₂ = k) (eg : g₁ ≫ g₂ = g) (e : g ≫ h = k)
    (M : Z.Modules) :
    (pullbackCompIso e₁ (Iso.refl _)).hom ≫
      (Scheme.Modules.pullback g₁).map
        (pullbackCompIso e₂ (Iso.refl ((Scheme.Modules.pullback h).obj M))).hom ≫
        (Scheme.Modules.pullbackComp g₁ g₂).hom.app _ ≫ (Scheme.Modules.pullbackCongr eg).hom.app _ =
      (pullbackCompIso e (Iso.refl _)).hom := by
  subst e₂ e₁ eg
  have H := congrArg (fun φ => φ.app M) (Scheme.Modules.pseudofunctor_associativity g₁ g₂ h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at H
  have H' : (Scheme.Modules.pullbackComp g₁ (g₂ ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback g₁).map ((Scheme.Modules.pullbackComp g₂ h).inv.app M) ≫
        (Scheme.Modules.pullbackComp g₁ g₂).hom.app _ =
      eqToHom (by simp) ≫ (Scheme.Modules.pullbackComp (g₁ ≫ g₂) h).inv.app M := by
    rw [← reassoc_of% H]
    simp
  simp only [pullbackCompIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Functor.mapIso_refl, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc, eqToIso.inv,
    eqToHom_app]
  simpa using H'

lemma pullbackHomAlong_trans {g₁ : S ⟶ T} {g₂ : T ⟶ Y} {h : Y ⟶ Z} {k₂ : T ⟶ Z} {k : S ⟶ Z}
    {g : S ⟶ Y} (e₂ : g₂ ≫ h = k₂) (e₁ : g₁ ≫ k₂ = k) (eg : g₁ ≫ g₂ = g) (e : g ≫ h = k)
    {F G : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G) :
    pullbackHomAlong e₁ (pullbackHomAlong e₂ ψ) = pullbackHomAlong e ψ := by
  have hF := pullbackCompIso_trans e₂ e₁ eg e F
  have hG := pullbackCompIso_trans e₂ e₁ eg e G
  subst eg
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] at hF hG
  have hG' : (pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback h).obj G))).inv =
      (Scheme.Modules.pullbackComp g₁ g₂).inv.app _ ≫
        (Scheme.Modules.pullback g₁).map (pullbackCompIso e₂ (Iso.refl _)).inv ≫
          (pullbackCompIso e₁ (Iso.refl _)).inv := by
    apply Iso.inv_ext
    rw [← hG]
    simp [← Functor.map_comp_assoc]
  unfold pullbackHomAlong
  rw [← hF, hG']
  have nat : (Scheme.Modules.pullbackComp g₁ g₂).hom.app _ ≫ (Scheme.Modules.pullback (g₁ ≫ g₂)).map ψ ≫
      (Scheme.Modules.pullbackComp g₁ g₂).inv.app _ =
      (Scheme.Modules.pullback g₁).map ((Scheme.Modules.pullback g₂).map ψ) := by
    rw [← (Scheme.Modules.pullbackComp g₁ g₂).hom.naturality_assoc ψ]
    simp
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nat]

end Trans

lemma invOpen_le_of_dvd {X : Scheme.{0}} (f : X ⟶ SpecZ) {m k : ℤ} (h : m ∣ k) :
    invOpen f k ≤ invOpen f m := by
  obtain ⟨c, rfl⟩ := h
  exact invOpen_mul_le_left f m c

theorem SpreadHom.proof (h₁ : SpreadHomNbhd.Statement) (h₂ : InvOpenInsideRat.Statement) :
    SpreadHom.Statement := by
  intro X f _ _ a ha F G hF hG φ
  obtain ⟨W, hWa, hW, ψ, hψ⟩ := h₁ X f a ha F G hF hG φ
  obtain ⟨m, hm, hmW⟩ := h₂ X f W hW
  refine ⟨m, hm, fun n hn hmn => ?_⟩
  have hle : invOpen f ((a : ℤ) * (n : ℤ)) ≤ W :=
    (invOpen_le_of_dvd f (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hmn) _)).trans hmW
  refine ⟨pullbackHomAlong (X.homOfLE_homOfLE hle hWa) ψ, ?_⟩
  rw [pullbackHomAlong_trans _ _ ?_ (toOpen_homOfLE f ℚ W hW
    (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) hWa)]
  · exact hψ
  · rw [← cancel_mono W.ι]
    simp [Scheme.homOfLE_ι]

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHomNbhd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

lemma opensRange_homOfLE_invOpen {X : Scheme.{0}} (f : X ⟶ SpecZ) {a k : ℤ}
    (h : invOpen f k ≤ invOpen f a) :
    (X.homOfLE h).opensRange = invOpen ((invOpen f a).ι ≫ f) k := by
  rw [Scheme.opensRange_homOfLE]
  rfl

theorem SpreadHomNbhd.proof (h₁ : DescendHom.Statement) (h₂ : GenericPullInj.Statement)
    (h₃ : SpreadHomSections.Statement) : SpreadHomNbhd.Statement := by
  intro X f _ _ a ha F G hF hG φ
  obtain ⟨m₁, hm₁, H₁⟩ := h₂ X f a ha G hG
  obtain ⟨m₂, hm₂, H₂⟩ := h₃ X f a ha F G hF hG φ
  have hn : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
  have hWa : invOpen f ((a : ℤ) * ((m₁ * m₂ : ℕ) : ℤ)) ≤ invOpen f a := invOpen_mul_le_left f a _
  have hW := range_baseChangeMap_subset f ℚ ((a : ℤ) * ((m₁ * m₂ : ℕ) : ℤ))
    (isUnit_intCast_rat _ (by positivity))
  have hR := opensRange_homOfLE_invOpen f hWa
  refine ⟨_, hWa, hW, h₁ _ _ _ (X.homOfLE hWa) (toOpen f ℚ _ hW) _
    (toOpen_homOfLE f ℚ _ hW (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) hWa) F G φ
    (fun V hV => H₁ _ hn (dvd_mul_right _ _) V (hR ▸ hV))
    (fun V hV => H₂ _ hn (dvd_mul_left _ _) V (hR ▸ hV))⟩

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadIsoLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadIsoLoc.proof (h₁ : SpreadHomLoc.Statement) (h₂ : SpreadHomInjLoc.Statement) :
    SpreadIsoLoc.Statement := by
  intro X f _ _ p U F G hF hG β
  obtain ⟨m₁, hm₁, hp₁, H₁⟩ := h₁ X f p U F G hF hG β.hom
  obtain ⟨m₂, hm₂, hp₂, H₂⟩ := h₁ X f p U G F hG hF β.inv
  obtain ⟨m₃, hm₃, hp₃, I₃⟩ := h₂ X f p U F F hF hF
  obtain ⟨m₄, hm₄, hp₄, I₄⟩ := h₂ X f p U G G hG hG
  obtain ⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄ := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hn_def]; positivity
  have hpn : ¬ (p : ℕ) ∣ n := by
    rw [hn_def]
    simp only [Nat.Prime.dvd_mul p.2]
    tauto
  obtain ⟨ψ₁, e₁⟩ := H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring)) hpn
  obtain ⟨ψ₂, e₂⟩ := H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring)) hpn
  have k₁ : ψ₁ ≫ ψ₂ = 𝟙 _ := I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) hpn _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, ← pullbackHomAlong_comp,
      Iso.hom_inv_id, pullbackHomAlong_id])
  have k₂ : ψ₂ ≫ ψ₁ = 𝟙 _ := I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) hpn _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, ← pullbackHomAlong_comp,
      Iso.inv_hom_id, pullbackHomAlong_id])
  refine ⟨n, hn, hpn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩
  rw [pullbackIsoAlong_hom, pullbackIsoAlong_hom]
  exact e₁

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

theorem isVectorBundle_freeModule (h : FreeSheafBasis.Statement.{u}) (Y : Scheme.{u}) (n : ℕ) :
    IsVectorBundle (freeModule Y n) := by
  intro y
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨V, hV, hyV, n, _, (h Y n).restrict le_top⟩

theorem isPreimmersion_baseChangeMap {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) :
    IsPreimmersion (baseChangeMap f (ZLoc p)) := by
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZLoc p)))) := by
    have h := IsPreimmersion.of_isLocalization (R := ℤ) (S := ZLoc p)
      (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
    convert h using 3
    exact RingHom.ext_int _ _
  infer_instance

theorem SpreadLocal.proof (h₁ : FreeSheafBasis.Statement.{0}) (h₂ : BasisIsoFree.Statement.{0}) :
    SpreadLocal.Statement := by
  intro X f p E hE x
  obtain ⟨U, -, hxU, n, s, hs⟩ := hE x
  have := isPreimmersion_baseChangeMap f p
  obtain ⟨W, hWo, hW⟩ := (baseChangeMap f (ZLoc p)).isEmbedding.isInducing.isOpen_iff.mp U.2
  let W' : X.Opens := ⟨W, hWo⟩
  have hWU : baseChangeMap f (ZLoc p) ⁻¹ᵁ W' = U := Opens.ext hW
  refine ⟨W', hWU ▸ hxU, ?_⟩
  let V := baseChangeMap f (ZLoc p) ⁻¹ᵁ W'
  have hle : V.ι ''ᵁ ⊤ ≤ U := by simp [V, hWU]
  obtain ⟨eF⟩ := h₂ _ (E.restrict V.ι) n _ ((hs.restrict hle).restrictImage V.ι)
  let φ := (baseChangeMap f (ZLoc p) ∣_ W').toRingCatSheafHom
  have : (SheafOfModules.pushforward φ).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap f (ZLoc p) ∣_ W')).isRightAdjoint
  exact ⟨_, isVectorBundle_freeModule h₁ _ n,
    ⟨SheafOfModules.pullbackObjFreeIso φ (ULift.{0} (Fin n)) ≪≫ eF.symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app E⟩⟩

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsIsoGlueTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def IsoGlueTwo.Statement : Prop :=
  ∀ (Y : Scheme.{0}) (P₁ P₂ P P₁₂ : Y.Opens) (h₁ : P₁ ≤ P) (h₂ : P₂ ≤ P), P ≤ P₁ ⊔ P₂ →
    ∀ (k₁ : P₁₂ ≤ P₁) (k₂ : P₁₂ ≤ P₂), P₁ ⊓ P₂ ≤ P₁₂ →
    ∀ (A B : (P : Scheme.{0}).Modules)
      (φ₁ : (Scheme.Modules.pullback (Y.homOfLE h₁)).obj A ≅ (Scheme.Modules.pullback (Y.homOfLE h₁)).obj B)
      (φ₂ : (Scheme.Modules.pullback (Y.homOfLE h₂)).obj A ≅ (Scheme.Modules.pullback (Y.homOfLE h₂)).obj B),
    pullbackIsoAlong (Y.homOfLE_homOfLE k₁ h₁) φ₁ = pullbackIsoAlong (Y.homOfLE_homOfLE k₂ h₂) φ₂ →
    ∃ φ : A ≅ B, (Scheme.Modules.pullback (Y.homOfLE h₁)).mapIso φ = φ₁ ∧
      (Scheme.Modules.pullback (Y.homOfLE h₂)).mapIso φ = φ₂

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadGlue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

@[simp]
lemma pullbackIsoAlong_refl {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) (F : Z.Modules) :
    pullbackIsoAlong e (Iso.refl ((Scheme.Modules.pullback h).obj F)) = Iso.refl _ := by
  ext1
  simp [pullbackIsoAlong]

def restrictSpread (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    {V W : X.Opens} (h : V ≤ W) {E' : (W : Scheme.{0}).Modules}
    (α : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj E' ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj E) :
    (Scheme.Modules.pullback (baseChangeMap f R ∣_ V)).obj
        ((Scheme.Modules.pullback (X.homOfLE h)).obj E') ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ V).ι).obj E :=
  (Scheme.Modules.pullbackComp (baseChangeMap f R ∣_ V) (X.homOfLE h)).app E' ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_homOfLE (baseChangeMap f R) V W h)).app E' ≪≫
    ((Scheme.Modules.pullbackComp (Scheme.homOfLE _ ((baseChangeMap f R).preimage_mono h))
      (baseChangeMap f R ∣_ W)).app E').symm ≪≫
    (Scheme.Modules.pullback (Scheme.homOfLE _ ((baseChangeMap f R).preimage_mono h))).mapIso α ≪≫
    (Scheme.Modules.pullbackComp (Scheme.homOfLE _ ((baseChangeMap f R).preimage_mono h))
      (baseChangeMap f R ⁻¹ᵁ W).ι).app E ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι _ ((baseChangeMap f R).preimage_mono h))).app E

def overlapIso (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    {W₁ W₂ : X.Opens} {E₁ : (W₁ : Scheme.{0}).Modules} {E₂ : (W₂ : Scheme.{0}).Modules}
    (α₁ : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W₁)).obj E₁ ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W₁).ι).obj E)
    (α₂ : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W₂)).obj E₂ ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W₂).ι).obj E) :
    (Scheme.Modules.pullback (baseChangeMap f R ∣_ (W₁ ⊓ W₂))).obj
        ((Scheme.Modules.pullback (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁))).obj E₁) ≅
      (Scheme.Modules.pullback (baseChangeMap f R ∣_ (W₁ ⊓ W₂))).obj
        ((Scheme.Modules.pullback (X.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂))).obj E₂) :=
  restrictSpread f R E inf_le_left α₁ ≪≫ (restrictSpread f R E inf_le_right α₂).symm

def SpreadGlue.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    (W₁ W₂ : X.Opens) (E₁ : (W₁ : Scheme.{0}).Modules) (E₂ : (W₂ : Scheme.{0}).Modules),
    IsVectorBundle E₁ → IsVectorBundle E₂ →
    ∀ (α₁ : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W₁)).obj E₁ ≅
        (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W₁).ι).obj E)
      (α₂ : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W₂)).obj E₂ ≅
        (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W₂).ι).obj E)
      (V : X.Opens), Set.range (baseChangeMap f R) ⊆ Set.range V.ι →
    ∀ θ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ W₂))).obj
        ((Scheme.Modules.pullback (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁))).obj E₁) ≅
      (Scheme.Modules.pullback (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ W₂))).obj
        ((Scheme.Modules.pullback (X.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂))).obj E₂),
    pullbackIsoAlong (rfl : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) ≫
        X.homOfLE (inf_le_left : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ W₂) = _) θ =
      pullbackIsoAlong (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂)
        inf_le_left).symm (overlapIso f R E α₁ α₂) →
    SpreadsOn f R E ((W₁ ⊔ W₂) ⊓ V)

def structureSpreadIso (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens) :
    (Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj (structureModule (W : Scheme.{0})) ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj (structureModule (baseChange f R)) :=
  pullbackStructureIso _ ≪≫ (pullbackStructureIso _).symm

end

end GroundTheory.Heights₂.Heights.Model
end

