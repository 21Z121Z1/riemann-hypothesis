import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.GlueCoherence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

set_option linter.unusedSimpArgs false

universe u

variable {T' T Y Z : Scheme.{u}}

lemma pullbackCompIso_trans_right {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k) {E : Z.Modules}
    {F F' : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) (δ : F ≅ F') :
    pullbackCompIso e (γ ≪≫ δ) = pullbackCompIso e γ ≪≫ (Scheme.Modules.pullback g).mapIso δ := by
  ext1
  simp [pullbackCompIso]

lemma pullbackCompIso_eq_refl_trans {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e γ = pullbackCompIso e (Iso.refl _) ≪≫ (Scheme.Modules.pullback g).mapIso γ := by
  rw [← pullbackCompIso_trans_right, Iso.refl_trans]

lemma pullbackCompIso_comp (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k') (e' : g' ≫ h = k')
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e' γ = pullbackCompIso ek (pullbackCompIso e γ) ≪≫
      (Scheme.Modules.pullbackComp t g).app F ≪≫ (Scheme.Modules.pullbackCongr eg).app F := by
  subst eg ek e
  ext1
  have assoc := congr_arg (fun φ => φ.app E)
    (Scheme.Modules.pseudofunctor_associativity t g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at assoc
  have nat := (Scheme.Modules.pullbackComp t g).hom.naturality γ.hom
  simp only [Functor.comp_map] at nat
  simp only [pullbackCompIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc, Category.id_comp, eqToIso.inv, eqToIso.hom, eqToHom_app,
    eqToHom_refl, Category.comp_id, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc]
  simp only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [nat]
  have assoc' : (Scheme.Modules.pullbackComp t (g ≫ h)).inv.app E ≫
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullbackComp g h).inv.app E) ≫
        (Scheme.Modules.pullbackComp t g).hom.app ((Scheme.Modules.pullback h).obj E) =
      eqToHom (by rw [Category.assoc]) ≫ (Scheme.Modules.pullbackComp (t ≫ g) h).inv.app E := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp (t ≫ g) h).hom.app E)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact assoc
  slice_rhs 2 3 => erw [Category.id_comp]
  slice_rhs 1 3 => rw [assoc']
  simp only [Category.assoc]

lemma pullbackComp_trans_congr (t : T' ⟶ T) {g : T ⟶ Y} {g' : T' ⟶ Y} (eg : t ≫ g = g')
    (F : Y.Modules) :
    (Scheme.Modules.pullbackComp t g).app F ≪≫ (Scheme.Modules.pullbackCongr eg).app F =
      (pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F))).symm := by
  subst eg
  ext1
  simp [pullbackCompIso, Scheme.Modules.pullbackCongr]

lemma pullbackCompIso_comp' (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k') (e' : g' ≫ h = k')
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e' γ = pullbackCompIso ek (Iso.refl _) ≪≫
      (Scheme.Modules.pullback t).mapIso (pullbackCompIso e γ) ≪≫
      (pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F))).symm := by
  rw [pullbackCompIso_comp t e eg ek e' γ, pullbackComp_trans_congr,
    pullbackCompIso_eq_refl_trans ek (pullbackCompIso e γ), Iso.trans_assoc]

lemma mapIso_pullbackCompIso_refl (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k')
    (e' : g' ≫ h = k') (E : Z.Modules) :
    (Scheme.Modules.pullback t).mapIso (pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback h).obj E))) =
      (pullbackCompIso ek (Iso.refl _)).symm ≪≫ pullbackCompIso e' (Iso.refl _) ≪≫
        pullbackCompIso eg (Iso.refl _) := by
  rw [pullbackCompIso_comp' t e eg ek e']
  ext1
  simp

lemma pullbackCompIso_refl_naturality (t : T' ⟶ T) {g : T ⟶ Y} {g' : T' ⟶ Y} (eg : t ≫ g = g')
    {F F' : Y.Modules} (δ : F ≅ F') :
    pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F)) ≪≫
        (Scheme.Modules.pullback t).mapIso ((Scheme.Modules.pullback g).mapIso δ) =
      (Scheme.Modules.pullback g').mapIso δ ≪≫ pullbackCompIso eg (Iso.refl _) := by
  rw [← pullbackCompIso_eq_refl_trans]
  subst eg
  ext1
  have nat := (Scheme.Modules.pullbackComp t g).inv.naturality δ.hom
  simp only [Functor.comp_map] at nat
  simp [pullbackCompIso, Scheme.Modules.pullbackCongr, nat]

lemma mapIso_pullbackIsoAlong {W' W O O' : Scheme.{0}} (u : W' ⟶ W) {t : W ⟶ O'} {h : O' ⟶ O}
    {k : W ⟶ O} (ek : t ≫ h = k) {t' : W' ⟶ O'} {k' : W' ⟶ O} (ee : t' ≫ h = k')
    (ut : u ≫ t = t') (uk : u ≫ k = k') {A B : O.Modules}
    (ψ : (Scheme.Modules.pullback h).obj A ≅ (Scheme.Modules.pullback h).obj B) :
    (Scheme.Modules.pullback u).mapIso (pullbackIsoAlong ek ψ) =
      (pullbackCompIso uk (Iso.refl ((Scheme.Modules.pullback k).obj A))).symm ≪≫
        pullbackIsoAlong ee ψ ≪≫ pullbackCompIso uk (Iso.refl _) := by
  have hA := mapIso_pullbackCompIso_refl u ek ut uk ee A
  have hB := mapIso_pullbackCompIso_refl u ek ut uk ee B
  have nat := pullbackCompIso_refl_naturality u ut ψ
  simp only [pullbackIsoAlong, Functor.mapIso_trans, Functor.mapIso_symm, hA, hB]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  congr 2
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, nat]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

def starIso {W U V O' O N : Scheme.{0}} {t : W ⟶ O'} {h : O' ⟶ O} {k : W ⟶ O} (ek : t ≫ h = k)
    {ρ : O ⟶ N} {τ : O ⟶ V} {jU : W ⟶ U} {ρU : U ⟶ N} {jV : W ⟶ V} (e7 : k ≫ ρ = jU ≫ ρU)
    (e8 : k ≫ τ = jV) {E' : N.Modules} {E₀ : V.Modules}
    (ψ : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback ρ).obj E') ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback τ).obj E₀)) :
    (Scheme.Modules.pullback jU).obj ((Scheme.Modules.pullback ρU).obj E') ≅
      (Scheme.Modules.pullback jV).obj E₀ :=
  (pullbackCompIso (rfl : jU ≫ ρU = jU ≫ ρU) (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫
    pullbackCompIso e7 (Iso.refl _) ≪≫ pullbackIsoAlong ek ψ ≪≫
    (pullbackCompIso e8 (Iso.refl ((Scheme.Modules.pullback τ).obj E₀))).symm

theorem glue_compat_chase {X XQ Xp V U W Oa Oam ON : Scheme.{0}}
    {ιV : V ⟶ X} {ιU : U ⟶ X} {ιW : W ⟶ X} {jV : W ⟶ V} {jU : W ⟶ U}
    {bQ : XQ ⟶ X} {bp : Xp ⟶ X} {rQp : XQ ⟶ Xp} {c0 : XQ ⟶ V} {rU : Xp ⟶ U}
    {ρU : U ⟶ ON} {rN : Xp ⟶ ON} {ρa : Oa ⟶ ON} {τa : Oa ⟶ V} {cA : XQ ⟶ Oa}
    {h : Oam ⟶ Oa} {cA' : XQ ⟶ Oam} {t : W ⟶ Oam} {k : W ⟶ Oa} {q : XQ ⟶ W}
    (hV : jV ≫ ιV = ιW) (hU : jU ≫ ιU = ιW) (h0 : c0 ≫ ιV = bQ) (hp : rQp ≫ bp = bQ)
    (hrU : rU ≫ ιU = bp) (h5 : rU ≫ ρU = rN) (e1 : cA ≫ ρa = rQp ≫ rN) (e2 : cA ≫ τa = c0)
    (ee : cA' ≫ h = cA) (ek : t ≫ h = k) (e7 : k ≫ ρa = jU ≫ ρU) (e8 : k ≫ τa = jV)
    (qV : q ≫ jV = c0) (qU : q ≫ jU = rQp ≫ rU) (qt : q ≫ t = cA') (qW : q ≫ ιW = bQ)
    {E : X.Modules} {E₀ : V.Modules} {Ep : Xp.Modules} {E' : ON.Modules}
    (e₀ : (Scheme.Modules.pullback ιV).obj E ≅ E₀)
    (eU : (Scheme.Modules.pullback ιU).obj E ≅ (Scheme.Modules.pullback ρU).obj E')
    (σ : (Scheme.Modules.pullback rN).obj E' ≅ Ep)
    (β : (Scheme.Modules.pullback rQp).obj Ep ≅ (Scheme.Modules.pullback c0).obj E₀)
    (ψ : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback ρa).obj E') ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback τa).obj E₀))
    (hψ : pullbackIsoAlong ee ψ =
      (pullbackCompIso e1 (Iso.refl ((Scheme.Modules.pullback ρa).obj E'))).symm ≪≫
        pullbackCompIso (rfl : rQp ≫ rN = rQp ≫ rN) σ ≪≫ β ≪≫
        pullbackCompIso e2 (Iso.refl ((Scheme.Modules.pullback τa).obj E₀)))
    (hglue : pullbackCompIso hV e₀ = pullbackCompIso hU eU ≪≫ starIso ek e7 e8 ψ) :
    pullbackCompIso h0 e₀ =
      pullbackCompIso hp (pullbackCompIso hrU eU ≪≫
        ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ)) ≪≫ β := by
  have e'' : (rQp ≫ rU) ≫ ιU = bQ := by rw [Category.assoc, hrU, hp]
  have qk : q ≫ k = cA := by rw [← ek, ← Category.assoc, qt, ee]
  have ekk : q ≫ jU ≫ ρU = rQp ≫ rN := by rw [← Category.assoc, qU, Category.assoc, h5]
  have e6 : (rQp ≫ rU) ≫ ρU = rQp ≫ rN := by rw [Category.assoc, h5]
  have hL : pullbackCompIso h0 e₀ = pullbackCompIso e'' eU ≪≫
      (pullbackCompIso qU (Iso.refl _) ≪≫ (Scheme.Modules.pullback q).mapIso (starIso ek e7 e8 ψ) ≪≫
        (pullbackCompIso qV (Iso.refl ((Scheme.Modules.pullback jV).obj E₀))).symm) := by
    rw [pullbackCompIso_comp' q hV qV qW h0 e₀, hglue, Functor.mapIso_trans,
      pullbackCompIso_comp' q hU qU qW e'' eU]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  have hR : pullbackCompIso hp (pullbackCompIso hrU eU ≪≫
        ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ)) ≪≫ β =
      pullbackCompIso e'' eU ≪≫ (pullbackCompIso (rfl : rQp ≫ rU = rQp ≫ rU) (Iso.refl _) ≪≫
        (Scheme.Modules.pullback rQp).mapIso
          ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ) ≪≫ β) := by
    rw [pullbackCompIso_trans_right, pullbackCompIso_comp' rQp hrU rfl hp e'' eU,
      pullbackCompIso_eq_refl_trans hp (pullbackCompIso hrU eU)]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [hL, hR]
  congr 1
  simp only [starIso, Functor.mapIso_trans, Functor.mapIso_symm]
  rw [mapIso_pullbackIsoAlong q ek ee qt qk ψ, hψ, mapIso_pullbackCompIso_refl q e7 qk ekk e1 E',
    mapIso_pullbackCompIso_refl q e8 qk qV e2 E₀,
    mapIso_pullbackCompIso_refl q (rfl : jU ≫ ρU = jU ≫ ρU) qU ekk e6 E',
    mapIso_pullbackCompIso_refl rQp h5 rfl rfl e6 E',
    pullbackCompIso_eq_refl_trans (rfl : rQp ≫ rN = rQp ≫ rN) σ]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id_assoc, Iso.trans_refl, Iso.self_symm_id, Iso.symm_self_id]

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem KrullAkizuki.equiv :
    GroundTheory.Heights₂.Heights.Model.KrullAkizuki.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.KrullAkizuki.Statement := by
  constructor
  · rintro ⟨h₁, h₂⟩ R K L _ _ _ _ _ _ _ _ _ _ _ hR
    exact ⟨h₁ R hR K L, h₂ R hR K⟩
  · intro h
    refine ⟨fun R _ _ _ hR K _ _ _ L _ _ _ _ _ S => (h R K L hR).1 S, ?_⟩
    intro R _ _ _ hR K _ _ _
    exact (h R K K hR).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem LatticesAgree.equiv :
    GroundTheory.Heights₂.Heights.Model.LatticesAgree.Statement ↔ LatticesAgree.Statement := by
  constructor
  · intro h A K V _ _ _ _ _ _ _ _ _ _ _ _ M N hMf hMp hNf hNp hMs hNs hloc
    refine h A K V M N hMf hMp hNf hNp hMs hNs fun p hp => ?_
    exact SetLike.coe_injective (hloc p.asIdeal p.isPrime hp)
  · intro h A _ _ _ _ K _ _ _ V _ _ _ _ _ M N hMf hMp hNf hNp hMs hNs hloc
    refine h A K V M N hMf hMp hNf hNp hMs hNs fun p hp hh => ?_
    have e := hloc ⟨p, hp⟩ hh
    exact congrArg (fun P : Submodule A V => (P : Set V)) e

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsVectorBundleIffModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits

noncomputable section

theorem isVectorBundle_iff_model {X : Scheme.{0}} (E : X.Modules) :
    GroundTheory.Heights₂.Heights.Model.IsVectorBundle E ↔ IsVectorBundle E := Iff.rfl

theorem genTo_eq_baseChangeMap (X : Scheme.{0}) :
    genTo X = GroundTheory.Heights₂.Heights.Model.baseChangeMap (toSpecZ X) ℚ := rfl

theorem pbSection_eq_pullSection {A B : Scheme.{0}} (f : A ⟶ B) (M : B.Modules) (t : Γ(M, ⊤)) :
    pbSection f M t = GroundTheory.Heights₂.Heights.Model.pullSection f M t := rfl

theorem ClearDenominators.equiv :
    GroundTheory.Heights₂.Heights.Model.ClearDenominators.Statement ↔ ClearDenominators.Statement := by
  constructor
  · intro h X _ _ hf L hL s
    exact h X (toSpecZ X) L hL s
  · intro h X f _ _ _ L hL s
    obtain rfl : f = toSpecZ X := specZ_hom_ext _ _
    exact h X inferInstance L hL s

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.NonemptyPullbackIsoIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

theorem nonempty_pullback_iso_iff {W X : Scheme.{u}} (q : W ⟶ X) (U : X.Opens)
    (a : W ⟶ U.toScheme) (ha : a ≫ U.ι = q) (E' : U.toScheme.Modules) (E : W.Modules) :
    Nonempty ((Scheme.Modules.pullback a).obj E' ≅ E) ↔
      Nonempty ((Scheme.Modules.pullback (q ∣_ U)).obj E' ≅
        (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj E) := by
  have h1 : (q ⁻¹ᵁ U).ι ≫ a = q ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, ha, morphismRestrict_ι]
  have hrange : Set.range (𝟙 W : W ⟶ W) ⊆ Set.range (q ⁻¹ᵁ U).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : U.ι (a w) ∈ Set.range U.ι := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.comp_apply, ha] at hw
    exact hw
  let s : W ⟶ (q ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (q ⁻¹ᵁ U).ι (𝟙 W) hrange
  have hs : s ≫ (q ⁻¹ᵁ U).ι = 𝟙 W := IsOpenImmersion.lift_fac _ _ _
  have h2 : s ≫ q ∣_ U = a := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hs,
      Category.id_comp, ha]
  constructor
  · rintro ⟨γ⟩
    exact ⟨GroundTheory.Heights₂.Heights.Model.pullbackCompIso h1 γ⟩
  · rintro ⟨δ⟩
    exact ⟨GroundTheory.Heights₂.Heights.Model.pullbackCompIso h2 δ ≪≫
      (GroundTheory.Heights₂.Heights.Model.pullbackCompIso hs (Iso.refl _)).symm ≪≫
        (Scheme.Modules.pullbackId W).app E⟩

def SpreadBundle.Along (X : Scheme.{0}) (p : Nat.Primes)
    (g : Spec (.of (ZLoc p)) ⟶ Spec (.of ℤ)) : Prop :=
  ∀ E : (pullback (toSpecZ X) g).Modules, IsVectorBundle E →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ m' : ℕ, m ∣ m' → ¬ (p : ℕ) ∣ m' →
      ∃ E' : (invOpen X m').toScheme.Modules, IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (pullback.fst (toSpecZ X) g ∣_ invOpen X m')).obj E' ≅
          (Scheme.Modules.pullback (pullback.fst (toSpecZ X) g ⁻¹ᵁ invOpen X m').ι).obj E)

theorem SpreadBundle.along_congr (X : Scheme.{0}) (p : Nat.Primes)
    {g g' : Spec (.of (ZLoc p)) ⟶ Spec (.of ℤ)} (h : g = g') :
    SpreadBundle.Along X p g ↔ SpreadBundle.Along X p g' := by
  subst h
  rfl

theorem SpreadBundle.model_iff_along (X : Scheme.{0}) (p : Nat.Primes) :
    (∀ E : (GroundTheory.Heights₂.Heights.Model.baseChange (toSpecZ X) (ZLoc p)).Modules,
      GroundTheory.Heights₂.Heights.Model.IsVectorBundle E →
      ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, m ∣ n → ∀ hn : ¬ ((p : ℕ) : ℤ) ∣ (n : ℤ),
        ∃ E' : (GroundTheory.Heights₂.Heights.Model.invOpen (toSpecZ X) n : Scheme.{0}).Modules,
          GroundTheory.Heights₂.Heights.Model.IsVectorBundle E' ∧
          Nonempty ((Scheme.Modules.pullback (GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X)
            (ZLoc p) n (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_zLoc p n hn))).obj E' ≅ E)) ↔
      SpreadBundle.Along X p (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZLoc p)))) := by
  refine forall_congr' fun E => imp_congr_right fun _ => exists_congr fun m =>
    and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun n =>
      imp_congr_right fun _ => ?_
  have hdvd : ¬ ((p : ℕ) : ℤ) ∣ (n : ℤ) ↔ ¬ (p : ℕ) ∣ n := by
    rw [Int.natCast_dvd_natCast]
  constructor
  · intro h hn
    obtain ⟨E', hE', hiso⟩ := h (hdvd.2 hn)
    exact ⟨E', hE', (nonempty_pullback_iso_iff _ _ _
      (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι _ _ _ _) E' E).1 hiso⟩
  · intro h hn
    obtain ⟨E', hE', hiso⟩ := h (hdvd.1 hn)
    exact ⟨E', hE', (nonempty_pullback_iso_iff _ _ _
      (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι _ _ _ _) E' E).2 hiso⟩

theorem SpreadBundle.equiv :
    GroundTheory.Heights₂.Heights.Model.SpreadBundle.Statement ↔ SpreadBundle.Statement := by
  constructor
  · intro h X hX p
    obtain ⟨h1, h2⟩ := hX
    exact (SpreadBundle.along_congr X p (specZ_hom_ext _ _)).1
      ((SpreadBundle.model_iff_along X p).1 (h X (toSpecZ X) p))
  · intro h X f _ _ p
    obtain rfl := specZ_hom_ext f (toSpecZ X)
    exact (SpreadBundle.model_iff_along X p).2
      ((SpreadBundle.along_congr X p (specZ_hom_ext _ _)).2 (h X ⟨‹_›, ‹_›⟩ p))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PAwayHeightOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

noncomputable section

theorem mem_away_of_heightOne (hHOI : HeightOneIntersection.Statement)
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (Ω : Type) [Field Ω] [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω))
    (h : A) (hh : h ≠ 0) (a : Ω)
    (hs : ∃ s : A, s ≠ 0 ∧ ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n * s) * a = algebraMap A Ω g)
    (hP : ∀ P : Ideal A, P.IsPrime → P.height = 1 → h ∉ P →
      ∃ t : A, t ∉ P ∧ ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n * t) * a = algebraMap A Ω g) :
    ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n) * a = algebraMap A Ω g := by
  let K := FractionRing A
  let φ : K →+* Ω := IsFractionRing.lift hinj
  have hφ : ∀ y : A, φ (algebraMap A K y) = algebraMap A Ω y := fun y =>
    IsFractionRing.lift_algebraMap hinj y
  have hφinj : Function.Injective φ := φ.injective
  obtain ⟨s, hs0, n, g, hg⟩ := hs
  have hns : h ^ n * s ≠ 0 := mul_ne_zero (pow_ne_zero _ hh) hs0
  have hnsΩ : algebraMap A Ω (h ^ n * s) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A Ω)]
    exact fun e => hns (hinj e)
  let k : K := algebraMap A K g / algebraMap A K (h ^ n * s)
  have hk : φ k = a := by
    simp only [k, map_div₀, hφ]
    rw [← hg, mul_div_cancel_left₀ _ hnsΩ]

  have back : ∀ y z : A, algebraMap A Ω y * a = algebraMap A Ω z →
      algebraMap A K y * k = algebraMap A K z := by
    intro y z e
    apply hφinj
    rw [map_mul, hk, hφ, hφ, e]
  have hS : Submonoid.powers h ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hh
  let A' : Subalgebra A K := Localization.subalgebra.ofField K (Submonoid.powers h) hS
  have : IsLocalization (Submonoid.powers h) A' :=
    Localization.subalgebra.isLocalization_ofField K (Submonoid.powers h) hS
  have : IsNoetherianRing A' :=
    IsLocalization.isNoetherianRing (Submonoid.powers h) A' inferInstance
  have : IsIntegrallyClosed A' :=
    isIntegrallyClosed_of_isLocalization A' (Submonoid.powers h) hS
  have key := hHOI A' K
  have hkmem : k ∈ Subalgebra.toSubmodule (⊥ : Subalgebra A' K) := by
    rw [key, Submodule.mem_iInf]
    intro P
    rw [Submodule.mem_iInf]
    intro hP1
    let Q : Ideal A := P.asIdeal.comap (algebraMap A A')
    have : Q.IsPrime := Ideal.comap_isPrime _ _
    have hQ1 : Q.height = 1 := by
      rw [← hP1]
      exact IsLocalization.height_under (Submonoid.powers h) P.asIdeal
    have hhQ : h ∉ Q := by
      intro hq
      have hu : IsUnit (algebraMap A A' h) :=
        IsLocalization.map_units A' (⟨h, Submonoid.mem_powers h⟩ : Submonoid.powers h)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)
    obtain ⟨t, htQ, m, z, hz⟩ := hP Q inferInstance hQ1 hhQ
    refine ⟨algebraMap A A' (h ^ m * t), ?_, ?_⟩
    · intro hmem
      have hmem' : h ^ m * t ∈ Q := hmem
      rcases (inferInstance : Q.IsPrime).mem_or_mem hmem' with h1 | h1
      · exact hhQ ((inferInstance : Q.IsPrime).mem_of_pow_mem _ h1)
      · exact htQ h1
    · rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot]
      refine ⟨algebraMap A A' z, ?_⟩
      rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      exact (back _ _ hz).symm
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hkmem
  obtain ⟨y, hy⟩ := hkmem
  obtain ⟨b, u, hu, hyb⟩ : ∃ (b u : A) (_ : u ∈ Submonoid.powers h),
      (y : K) = algebraMap A K b * (algebraMap A K u)⁻¹ := y.2
  obtain ⟨m, rfl⟩ := hu
  have hu0 : algebraMap A K (h ^ m) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A K)]
    exact fun e => pow_ne_zero m hh (IsFractionRing.injective A K e)
  have hyk : (y : K) = k := hy
  refine ⟨m, b, ?_⟩
  have e1 : algebraMap A K (h ^ m) * k = algebraMap A K b := by
    rw [← hyk, hyb, mul_comm, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  have e2 := congrArg φ e1
  rwa [map_mul, hk, hφ, hφ] at e2

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open IsLocalRing

theorem BlowUpChart.proof : BlowUpChart.Statement := by
  intro A _ _ _ _ K _ _ _ n x hx ⟨j, hj⟩
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A K)
  set f := (algebraMap A K).codRestrict V.toSubring hV with hf
  have : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun k => V.valuation (algebraMap A K (x k))
  have hinj := IsFractionRing.injective A K
  have hxi : x i ≠ 0 := by
    intro h0
    apply hj
    have h1 := hi j
    rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (by rw [h1, map_zero])
  have hvi : 0 < V.valuation (algebraMap A K (x i)) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact fun h => hxi (hinj (by rw [h, map_zero]))
  have hle : ∀ y ∈ blowUpChart K x i, y ∈ V := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hvi]
      exact hi k
    | algebraMap r => exact hV r
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
  let φ : blowUpChart K x i →+* V :=
    { toFun := fun y => ⟨y.1, hle y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ a : A, φ (algebraMap A (blowUpChart K x i) a) = f a := fun _ => rfl
  have hxm : x i ∈ maximalIdeal A := hx ▸ Ideal.subset_span ⟨i, rfl⟩
  have hnu : ¬ IsUnit (f (x i)) := by
    rw [isUnit_map_iff f]
    exact hxm
  refine ⟨i, hxi, fun hu => hnu (hφ (x i) ▸ hu.map φ), (maximalIdeal V).comap φ,
    Ideal.comap_isPrime _ _, ?_, ?_⟩
  · rw [Ideal.mem_comap, hφ]
    exact hnu
  · ext a
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ, mem_maximalIdeal, mem_nonunits_iff,
      mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff f]

end GroundTheory.Heights₂.Heights.Model
end

