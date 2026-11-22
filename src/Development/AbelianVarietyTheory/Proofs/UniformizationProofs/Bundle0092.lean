import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageEqOneIffTorusPoint
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

section Kernel

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' : Over S'} [GrpObj B] [GrpObj G']
  {X : Type} [AddCommGroup X]

theorem TQ.mono_i_left (Q : TQ G' X) : Mono Q.i.left := by
  have : Mono Q.i := ⟨fun _ _ h => Q.isKernel.hom_ext h (toUnit_unique _ _)⟩
  infer_instance

theorem TQ.image_eq_one_iff (Q : TQ G' X) {β : Q.B.left ⟶ B.left} (hB : IsGrpPullback Q.B B f β)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f) :
    xe ≫ Q.q.left ≫ β = r ≫ (1 : T ⟶ B).left ↔ ∃ τ : Z ⟶ (splitTorus S' X).left, τ ≫ Q.i.left = xe := by
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
  have e₁ : (eB (xe' ≫ Q.q)).left = xe ≫ Q.q.left ≫ β := (heB _).trans (Category.assoc _ _ _)
  have e₂ : (eB 1).left = r ≫ (1 : T ⟶ B).left := by
    rw [map_one, ← MonObj.comp_one R]; rfl
  rw [← e₁, ← e₂]
  constructor
  · intro h
    have h₁ : xe' ≫ Q.q = toUnit _ ≫ η[Q.B] := eB.injective (Over.OverMorphism.ext h)
    exact ⟨(Q.isKernel.lift _ _ h₁).left, congrArg (fun z => z.left) (Q.isKernel.lift_fst _ _ h₁)⟩
  · rintro ⟨τ, hτ⟩
    let τ' : Over.mk (xe ≫ G'.hom) ⟶ splitTorus S' X := Over.homMk τ (by
      rw [← hτ, ← Over.w Q.i]; exact (Category.assoc _ _ _).symm)
    have h₁ : τ' ≫ Q.i = xe' := Over.OverMorphism.ext hτ
    have h₂ : xe' ≫ Q.q = 1 := by
      rw [← h₁, Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (τ' ≫ toUnit _)]
    rw [h₂]

end Kernel

section Scal

variable {A C : Type} [CommRing A] [CommRing C] {Y Y' : Scheme.{0}}

noncomputable def scalRingHom (p : Y ⟶ Spec (CommRingCat.of A)) : A →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom

theorem scalRingHom_apply (p : Y ⟶ Spec (CommRingCat.of A)) (a : A) : scalRingHom p a = scal p a := rfl

theorem scalRingHom_specMap (p : Y ⟶ Spec (CommRingCat.of C)) (φ : A →+* C) :
    scalRingHom (p ≫ Spec.map (CommRingCat.ofHom φ)) = (scalRingHom p).comp φ :=
  congrArg CommRingCat.Hom.hom (SplitTorusPoints.ΓSpecIso_inv_comp_specMap p (CommRingCat.ofHom φ))

theorem exists_factor_quotient (r : Y ⟶ Spec (CommRingCat.of C)) (J : Ideal C)
    (h : J ≤ RingHom.ker (scalRingHom r)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ J)), r' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = r := by
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (scalRingHom r) fun _ ha => RingHom.mem_ker.1 (h ha))), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  apply ext_to_Spec
  refine (SplitTorusPoints.ΓSpecIso_inv_comp_specMap _ _).trans ?_
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem exists_factor_thick (φ : A →+* C) (I : Ideal A) (e : ℕ) (r : Y ⟶ Spec (CommRingCat.of C))
    (p : Y ⟶ Spec (CommRingCat.of (A ⧸ I ^ (e + 1))))
    (h : p ≫ thick A I e = r ≫ Spec.map (CommRingCat.ofHom φ)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ I.map φ ^ (e + 1))), r' ≫ thick C (I.map φ) e = r := by
  refine exists_factor_quotient r _ ?_
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  have := congrArg (fun q => scalRingHom q a) h
  simp only [scalRingHom_specMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero] at this
  exact this.symm

theorem exists_torus_point {S : Scheme.{0}} {X : Type} [AddCommGroup X] (c : Multiplicative X →* Cˣ)
    (r : Y ⟶ Spec (CommRingCat.of C)) (p : Y ⟶ S) : ∃ τ : Y ⟶ (splitTorus S X).left, τ ≫ (splitTorus S X).hom = p ∧
      ∀ χ, τ.appTop.hom (charUnit S X χ).val = scal r (c (Multiplicative.ofAdd χ)).val := by
  obtain ⟨τ, hτ⟩ := (splitTorusPointsEquiv S X (Over.mk p)).surjective
    ((Units.map (scalRingHom r).toMonoidHom).comp c)
  refine ⟨τ.left, Over.w τ, fun χ => ?_⟩
  refine (splitTorusPointsEquiv_val S X _ τ χ).symm.trans ?_
  rw [hτ]; rfl

theorem exists_hom_of_thick {X : Type} [AddCommGroup X] (J : Ideal C) [IsAdicComplete J C] {S : ℕ → Scheme.{0}}
    (τ : ∀ e, Spec (CommRingCat.of (C ⧸ J ^ (e + 1))) ⟶ (splitTorus (S e) X).left)
    (h : ∀ e χ, (thickTrans C J e ≫ τ (e + 1)).appTop.hom (charUnit _ X χ).val =
      (τ e).appTop.hom (charUnit _ X χ).val) :
    ∃ c : Multiplicative X →* Cˣ, ∀ e χ,
      (τ e).appTop.hom (charUnit _ X χ).val = scal (thick C J e) (c (Multiplicative.ofAdd χ)).val := by
  let u := fun e => splitTorusPointsEquiv (S e) X (Over.mk (τ e ≫ (splitTorus (S e) X).hom)) (Over.homMk (τ e) rfl)
  have hu : ∀ e χ, (u e (Multiplicative.ofAdd χ)).val = (τ e).appTop.hom (charUnit _ X χ).val := fun e χ =>
    splitTorusPointsEquiv_val _ _ _ _ χ
  choose b hb using fun χ : X => CompletePoint.exists_fn_of_thick J (fun e => (τ e).appTop.hom (charUnit _ X χ).val)
    fun e => by rw [← h e χ, Scheme.Hom.comp_appTop]; rfl
  let b' : Multiplicative X →* Γ(Spec (CommRingCat.of C), ⊤) :=
    { toFun := fun χ => b χ.toAdd
      map_one' := CompletePoint.fn_eq_of_thick J fun e => by
        rw [hb, ← hu]; exact (congrArg Units.val (map_one (u e))).trans (map_one _).symm
      map_mul' := fun χ χ' => CompletePoint.fn_eq_of_thick J fun e => by
        rw [(thick C J e).appTop.hom.map_mul, hb, hb, hb, ← hu, ← hu, ← hu]
        exact congrArg Units.val (map_mul (u e) χ χ') }
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom.toMonoidHom.comp b').toHomUnits, fun e χ => ?_⟩
  rw [← hb]
  exact congrArg (thick C J e).appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) (b χ)).symm

end Scal

theorem image_eq_one_iff_torus_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ↔ ∃ c : Multiplicative s.X →* Wˣ, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ x
  let I := IsLocalRing.maximalIdeal V
  let φ := algebraMap V W
  have hx : x.left ≫ G.hom = Spec.map (CommRingCat.ofHom φ) := Over.w x
  have hF : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e := fun e => pullback.condition
  have mF : ∀ e, Mono (fstG I e G).left := fun e => pullback.fst_of_mono (f := G.hom) (g := thick V I e)
  have base : ∀ (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x.left →
      r ≫ Spec.map (CommRingCat.ofHom φ) = (xe ≫ (thickObj V I e G).hom) ≫ thick V I e := fun e Z r xe h => by
    rw [Category.assoc, ← hF, ← hx, ← Category.assoc, ← h]
    exact Category.assoc _ _ _
  have ker := fun (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left)
    (h : xe ≫ (fstG I e G).left = r ≫ x.left) =>
    (t.l e).Q.image_eq_one_iff (T := Over.mk (Spec.map (CommRingCat.ofHom φ))) (a.b_pb e).1 r xe (base e r xe h)
  constructor
  · intro H
    let J := I.map φ
    have hle : ∀ e : ℕ, I ^ (e + 1) ≤ (J ^ (e + 1)).comap φ := fun e => by
      rw [← Ideal.map_pow]; exact Ideal.le_comap_map
    have hp : ∀ e, (thick W J e ≫ x.left) ≫ G.hom =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ (hle e))) ≫ thick V I e := fun e => by
      rw [Category.assoc, hx, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
    obtain ⟨y, hy⟩ : ∃ y : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left,
        ∀ e, y e ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      ⟨fun e => pullback.lift _ _ (hp e), fun e => pullback.lift_fst _ _ _⟩
    choose τ hτ using fun e => (ker e _ _ (hy e)).1 (H e _ _ _ (hy e))
    obtain ⟨c, hc⟩ := exists_hom_of_thick J τ fun e χ => by
      obtain ⟨σ, -, h₁, h₂⟩ := t.tor e
      have := (t.l (e + 1)).Q.mono_i_left
      have := mF (e + 1)
      have h₃ : thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      have h₄ : thickTrans W J e ≫ y (e + 1) = y e ≫ thickMap V I e G := by
        refine (cancel_mono (fstG I (e + 1) G).left).1 ?_
        refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hy (e + 1))).trans ?_)
        refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₃)).symm
        rw [← Category.assoc, thickTrans_comp]
        exact (hy e).symm
      have h₅ : thickTrans W J e ≫ τ (e + 1) = τ e ≫ σ := by
        rw [← cancel_mono (t.l (e + 1)).Q.i.left, Category.assoc, hτ, h₄, Category.assoc, h₂, ← Category.assoc, hτ]
      rw [h₅, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h₁]
    refine ⟨c, fun e Z r τ' h₁ h₂ => ?_⟩
    obtain ⟨r', rfl⟩ := exists_factor_thick φ I e r _ ((Category.assoc _ _ _).trans h₁)
    have h₃ : τ' = r' ≫ τ e := by
      refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
      · rw [← cancel_mono (thick V I e), Category.assoc]
        refine h₁.trans ?_
        rw [Category.assoc, base e _ _ (hy e), ← hτ e, Category.assoc (τ e), Over.w]
        simp only [Category.assoc]
      · rw [h₂, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hc, scal, scal,
          Scheme.Hom.comp_appTop]
        rfl
    have h₄ : τ e ≫ (t.l e).Q.i.left ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I e G).left) (hτ e)).trans (hy e))
    rw [h₃]
    exact (Category.assoc _ _ _).trans ((congrArg (r' ≫ ·) h₄).trans (Category.assoc _ _ _).symm)
  · rintro ⟨c, hc⟩ e Z r xe h
    obtain ⟨τ, h₁, h₂⟩ := exists_torus_point c r (xe ≫ (thickObj V I e G).hom)
    have := mF e
    refine (ker e r xe h).2 ⟨τ, (cancel_mono (fstG I e G).left).1 ?_⟩
    refine (Category.assoc _ _ _).trans ((hc e Z r τ ?_ h₂).trans h.symm)
    rw [← Category.assoc, h₁]
    exact (base e r xe h).symm

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageOneMulInv
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj B] [GrpObj G']
  [GrpObj B'] {φ : G'.left ⟶ G.left} {β : B'.left ⟶ B.left}

theorem exists_imageHom (hG : IsGrpPullback G' G f φ) (hB : IsGrpPullback B' B f β) (q : G' ⟶ B') [IsMonHom q]
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (x₀ : T ⟶ G) (h₀ : xe ≫ φ = r ≫ x₀.left) :
    ∃ (Y : Over S) (R : Y ⟶ T) (Φ : (T ⟶ G) → (Y ⟶ B)), Φ 1 = 1 ∧ (∀ x y, Φ (x * y) = Φ x * Φ y) ∧
      (∀ x, Φ x⁻¹ = (Φ x)⁻¹) ∧
      (∀ x b, (∀ ye : Z ⟶ G'.left, ye ≫ φ = r ≫ x.left → ye ≫ q.left ≫ β = r ≫ b.left) → Φ x = R ≫ b) ∧
      ∀ b, Φ x₀ = R ≫ b → xe ≫ q.left ≫ β = r ≫ b.left := by
  have hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f := by
    rw [Category.assoc, ← hG.1.w, reassoc_of% h₀, Over.w]
  obtain ⟨eG, heG⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hG _ _ hc
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  refine ⟨_, R, fun x => eB (eG.symm (R ≫ x) ≫ q), ?_, fun x y => ?_, fun x => ?_, fun x b h => ?_,
    fun b h => ?_⟩
  · simp only [MonObj.comp_one, map_one, MonObj.one_comp]
  · simp only [MonObj.comp_mul, map_mul, MonObj.mul_comp]
  · simp only [GrpObj.comp_inv, map_inv, GrpObj.inv_comp]
  · apply Over.OverMorphism.ext
    refine (heB _).trans ((Category.assoc _ _ _).trans (h _ ?_))
    refine (heG _).symm.trans ?_
    rw [MulEquiv.apply_symm_apply]
    rfl
  · let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
    have h₁ : eG xe' = R ≫ x₀ := Over.OverMorphism.ext ((heG _).trans h₀)
    have h₂ : eB (xe' ≫ q) = R ≫ b := by
      rw [← h]
      beta_reduce
      rw [← h₁, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans ((heB (xe' ≫ q)).symm.trans (congrArg (fun z => z.left) h₂))

end

theorem image_one_mul_inv : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G)).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ∧ ((∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x * x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b * b').left) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x⁻¹).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b⁻¹).left)) := by
  intro V _ _ _ A G _ _ s t a W _ _ x x' b b'
  have hG := fun e => isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) e)
  have hB := fun e => (a.b_pb e).1
  have hq := fun e => (t.l e).Q.q_hom
  refine ⟨fun e Z r xe h => ?_, fun h₁ h₂ => ⟨fun e Z r xe h => ?_, fun e Z r xe h => ?_⟩⟩
  · obtain ⟨Y, R, Φ, e₁, -, -, -, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k 1 (by rw [e₁, MonObj.comp_one])
  · obtain ⟨Y, R, Φ, -, e₂, -, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₂, l x b (h₁ e Z r), l x' b' (h₂ e Z r), MonObj.comp_mul])
  · obtain ⟨Y, R, Φ, -, -, e₃, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₃, l x b (h₁ e Z r), GrpObj.comp_inv])

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionGeometricPointOfField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory

theorem card_torsion_geometricPoint_of_field :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (n : ℕ), (n : k) ≠ 0 → Nat.card {x : Over.mk t ⟶ B // x ^ n = 1} = n ^ (2 * g) := by
  intro H S B _ hB g hg k _ _ t n hn
  have hB' : IsAbelianScheme ((Over.pullback t).obj B) :=
    { comm := by have := hB.comm; infer_instance
      smooth := by have := hB.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hB.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by have := hB.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h := H k ((Over.pullback t).obj B) g n hB' hg' hn
  have hp := isGrpPullback_pullback B t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp k)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst B.hom t = y.left ≫ pullback.fst B.hom t := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp k))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Nat.card {x : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ t) ⟶ B // x ^ n = 1} = n ^ (2 * g) := by
    rw [← h]
    refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp k))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GoodReductionUnif

theorem exists_baseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (A : PolAV S') (eA : (Over.pullback f).obj P.A ≅ A.A), IsMonHom eA.hom ∧
      ∃ w : LB.Iso (A.L.pull eA.hom.left) (P.L.pull (pullback.fst P.A.hom f)), w.IsGen := by
  obtain ⟨A, g, hg, -, mul, t, ht⟩ := hB S S' f P
  let eA : (Over.pullback f).obj P.A ≅ A.A := Over.isoMk hg.isoPullback.symm hg.isoPullback_inv_snd
  have he : eA.hom.left ≫ g = pullback.fst P.A.hom f := hg.isoPullback_inv_fst
  refine ⟨A, eA, isMonHom_of_mul _ fun T x y => Over.OverMorphism.ext (hg.hom_ext ?_ ?_), ?_⟩
  · have tb : ∀ a : T ⟶ (Over.pullback f).obj P.A, toBase hg.w (a ≫ eA.hom) =
        toBase (A := P.A) (A' := (Over.pullback f).obj P.A) (g := pullback.fst P.A.hom f) pullback.condition a :=
      fun a => Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (a.left ≫ ·) he))
    have e : toBase hg.w ((x * y) ≫ eA.hom) = toBase hg.w ((x ≫ eA.hom) * (y ≫ eA.hom)) := by
      rw [mul, tb, tb, tb, toBase_mul_pullback]
    exact congrArg CommaMorphism.left e
  · exact (Over.w _).trans (Over.w _).symm
  · obtain ⟨t', ht', -⟩ := GenericSectionBasis.exists_inv_iso t ht
    have h₁ := (isGen_iff t').1 ht'
    have h₂ := (isGen_iff _).1 (pullIso_isGen A.isLB eA.hom.left)
    obtain ⟨w, Tw⟩ := Geo.Tor.exists_comp A.isLB t' (pullIso A.L eA.hom.left) h₁ h₂ P.isLB
      (pull_isLB A.isLB _)
    rw [← he]
    exact ⟨w, (isGen_iff w).2 (Tw.pgen_comp A.isLB h₁ h₂)⟩

theorem vals_change {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) (T : Over S) (z : T.left)
    {J' J : (T.left ⟶ G.left) → P.L.L.ι} (hJ' : Good P.L.L z J') (hJ : Good P.L.L z J)
    (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ)
    (a : ∀ x : T ⟶ G, W x = gm x.left z _ (P.L.L.g (J x.left) (J' x.left))) :
    (val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T.hom z J =
        W 1 * val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T.hom z J') ∧
      (∀ x : T ⟶ G, val P.sym x.left z J * W x = W x⁻¹ * val P.sym x.left z J') ∧
      ∀ x y u : T ⟶ G, cubV P.c z J x y u * W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u * cubV P.c z J' x y u := by
  obtain ⟨h₁, h₂, h₃⟩ := (IsCPMap.id P).vals T z J' J hJ' hJ W fun x => by
    rw [a, Category.comp_id, gw_idIso _ _ _ (hJ _) (hJ' _)]
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rwa [Category.comp_id] at h₁
  · have := h₂ x
    rwa [Category.comp_id] at this
  · have := h₃ x y u
    rwa [_root_.id, cubV_toBase_id] at this

theorem cub_transfer {A A' U : Type} [Monoid A] [Monoid A'] [Monoid U] (β : A →* A') (W : A → U) (W' : A' → U)
    (a : ∀ x, W x = W' (β x)) {x y u : A} {c₁ c₁' c₂ c₂' : U} (e₁ : c₁ = c₁') (e₂ : c₂ = c₂')
    (h : c₁' * W' (β x * β y) * W' (β x * β u) * W' (β y * β u) * W' 1 =
      W' (β x * β y * β u) * W' (β x) * W' (β y) * W' (β u) * c₂') :
    c₁ * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * c₂ := by
  simpa only [a, map_mul, map_one, e₁, e₂] using h

open SelfUnif in

def selfPreU (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) [Subsingleton D.X]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (eA : (Over.pullback (jK R)).obj D.P.A ≅ A.A)
    (hA : IsMonHom eA.hom) (w : LB.Iso (A.L.pull eA.hom.left) (D.P.L.pull (pullback.fst D.P.A.hom (jK R))))
    (hw : w.IsGen) : PreU I D A D.P.A where
  semi := isSemiAbelian_of_isAbelianScheme _ D.P.isAb
  gen := eA
  gen_hom := hA
  P := CP.ofDegPre hG D
  wA := w
  wA_gen := hw
  gt := selfGt I D
  gt_q e := by rw [selfGt_pG_left, selfGt_pG_left, UnifPullRig.thickMap_fstG]
  gt_t e χ := corr_of_val D.P.isLB fun y J hJ =>
    (val_pull hJ _ _ _).trans ((selfTorusExtensionCoord_values_eq_one I _ _ χ _ y hJ).trans (selfTorusExtensionCoord_values_eq_one I _ _ χ _ y hJ).symm)
  w := selfW I D
  w_gen := selfW_gen I D
  w_vals e T z JG J hJG hJ W hW := by
    let β := toBaseHom (toBase_mul_pullback D.P.A (thick R I e)) T
    have hβ : ∀ x : T ⟶ thickObj R I e D.P.A, (Over.map (thick R I e)).map x ≫ fstG I e D.P.A = β x :=
      fun x => Over.OverMorphism.ext rfl
    obtain ⟨W', hW'⟩ : ∃ W' : (Over.mk (T.hom ≫ thick R I e) ⟶ D.P.A) → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W' x = gm x.left z _ (D.P.L.g (J x.left) (JG x.left)) := ⟨_, fun _ => rfl⟩
    obtain ⟨h₁, h₂, h₃⟩ := vals_change (CP.ofDegPre hG D) (Over.mk (T.hom ≫ thick R I e)) z hJG hJ W' hW'
    have p : ∀ x : T ⟶ thickObj R I e D.P.A, x.left ≫ (selfGt I D e).pG.left = (β x).left :=
      fun x => congrArg (x.left ≫ ·) (selfGt_pG_left I D e)
    have a : ∀ x : T ⟶ thickObj R I e D.P.A, W x = W' (β x) := fun x => by
      refine (hW x).trans ((congrArg (fun q => gw (selfW I D e) x.left z (J q) (fun _ => JG (β x).left)) (p x)).trans ?_)
      exact (selfW_ident I D e _ x.left z _ _ (hJ (β x).left) (hJG (β x).left)).trans (hW' (β x)).symm
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · rw [a, β.map_one]
      exact h₁
    · rw [a, a, β.map_inv]
      exact (congrArg (fun q => val D.sym q z J * _) (p x)).trans (h₂ (β x))
    · have c₁ : @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
          ((Over.map (thick R I e)).map x ≫ (selfGt I D e).pG) ((Over.map (thick R I e)).map y ≫ (selfGt I D e).pG)
          ((Over.map (thick R I e)).map u ≫ (selfGt I D e).pG)) =
          cubV (CP.ofDegPre hG D).c (T := Over.mk (T.hom ≫ thick R I e)) z J (β x) (β y) (β u) := by
        rw [selfGt_pG, hβ, hβ, hβ]; rfl
      have c₂ : @id (T.left.presheaf.stalk z)ˣ (cubV (CP.ofDegPre hG D).c (T := (Over.map (thick R I e)).obj T) z JG
          ((Over.map (thick R I e)).map x ≫ fstG I e D.P.A) ((Over.map (thick R I e)).map y ≫ fstG I e D.P.A)
          ((Over.map (thick R I e)).map u ≫ fstG I e D.P.A)) =
          cubV (CP.ofDegPre hG D).c (T := Over.mk (T.hom ≫ thick R I e)) z JG (β x) (β y) (β u) := by
        rw [hβ, hβ, hβ]; rfl
      exact cub_transfer β W W' a c₁ c₂ (h₃ (β x) (β y) (β u))
  w_compat e Z x z j k hj hk := by
    have hj' : (x ≫ (fstG I e D.P.A).left) z ∈ D.P.L.U j :=
      (congrArg (fun q => q (x z) ∈ _) (selfGt_pG_left I D e)).mp hj
    have t : (x ≫ thickMap R I e D.P.A) ≫ (fstG I (e + 1) D.P.A).left = x ≫ (fstG I e D.P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (x ≫ ·) (UnifPullRig.thickMap_fstG I e D.P.A))
    have a := selfW_ident I D e _ x z _ _ hj' hk
    have b := selfW_ident I D (e + 1) _ (x ≫ thickMap R I e _) z _ _
      ((congrArg (fun q => q z ∈ _) t).mpr hj') ((congrArg (fun q => q z ∈ _) t).mpr hk)
    exact (b.trans (congrArg (fun q => gm q z _ (D.P.L.g j k)) t)).trans a.symm

theorem main : Laws → Laws2 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ P : PolAV (Spec (CommRingCat.of V)), ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (D : DegData V (IsLocalRing.maximalIdeal V)), Nonempty (Unif (IsLocalRing.maximalIdeal V) D A P.A) ∧ Nonempty (PreU (IsLocalRing.maximalIdeal V) D.toPre A P.A)) := by
  intro hL _ V _ _ _ hV P
  obtain ⟨h₁, h₂, -⟩ := hV
  have : IsNoetherianRing V := inferInstance
  obtain ⟨A, eA, hA, w, hw⟩ := exists_baseChange hL.polBaseChange (jK V) P
  obtain ⟨D, rfl, hX, hU⟩ := exists_unif_abelianScheme hL.globalFns hL.secBaseChange hL.cube V
    (IsLocalRing.maximalIdeal V) P A eA hA ⟨w, hw⟩
  exact ⟨A, D, hU, ⟨selfPreU hL.globalFns _ D.toPre A eA hA w hw⟩⟩

end GlobalTheory.GoodReductionUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCoverOfIsProjByOfInfinite
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineCover

theorem exists_cover_of_isProjBy_of_infinite (K : Type) [Field K] [Infinite K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ) (hf : SmoothOfRelativeDimension g f) (hp : IsProjBy f) :
    ∃ D : Fin (g + 1) → X.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨H, hH, m, s, hc, hs⟩ := hp
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := ⟨by
    have e : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hc]
      rfl
    rw [e]
    exact isCompact_iUnion fun i => (hs i).1.isCompact⟩
  have : IsNoetherian X := ⟨⟩
  obtain ⟨D, hD, h⟩ := exists_affine_le_coheight (X := X) (fun F hF =>
    exists_isAffineOpen_of_finite (cst f ⊤) hH s hc (fun i => (hs i).1) F hF) (g + 1)
  refine ⟨D, hD, top_le_iff.1 fun x _ => not_not.1 fun hx => ?_⟩
  have := (h x hx).trans (coheight_le_of_smooth f hf x)
  exact Nat.not_succ_le_self _ (by exact_mod_cast this)

theorem exists_cover_of_isProjBy :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → IsProjBy f → ∃ D : Fin (g + 1) → X.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ :=
  fun K _ _ X _ f g hf hp => exists_cover_of_isProjBy_of_infinite K X f g hf hp

end GlobalTheory.AffineCover
end

