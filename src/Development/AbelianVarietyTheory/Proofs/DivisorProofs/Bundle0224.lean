import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0161
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFunctorLocalRepresentingDataOfRestrict
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem ker_comap_eq_ker_iff {X X' V V' : Scheme.{0}} (m : X' ⟶ X) (v : V ⟶ X) [IsClosedImmersion v]
    (v' : V' ⟶ X') [IsClosedImmersion v'] :
    v.ker.comap m = v'.ker ↔ ∃ w : V' ⟶ V, IsPullback v' w m v := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [comap_eq_ker_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ inv v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso (inv v.toImage)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso v.toImage) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]

variable {S Z : Scheme.{0}} (z : Z ⟶ S) (W : S.Opens)

lemma isPullback_restrict {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    IsPullback (pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι) (pullback.snd (z ∣_ W) b) z (b ≫ W.ι) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback (z ∣_ W) b) (isPullback_morphismRestrict z W).flip

def restrictIso {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) : pullback (z ∣_ W) b ≅ pullback z (b ≫ W.ι) :=
  (isPullback_restrict z W b).isoPullback

@[reassoc (attr := simp)]
lemma restrictIso_hom_fst {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.fst z (b ≫ W.ι) = pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι :=
  (isPullback_restrict z W b).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma restrictIso_hom_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.snd z (b ≫ W.ι) = pullback.snd (z ∣_ W) b :=
  (isPullback_restrict z W b).isoPullback_hom_snd

@[reassoc (attr := simp)]
lemma restrictIso_inv_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).inv ≫ pullback.snd (z ∣_ W) b = pullback.snd z (b ≫ W.ι) := by
  rw [Iso.inv_comp_eq, restrictIso_hom_snd]

lemma restrictIso_natural {Y H : Scheme.{0}} (b : Y ⟶ W.toScheme) (h : H ⟶ W.toScheme) (c : Y ⟶ H)
    (hc : c ≫ h = b) (w : c ≫ h ≫ W.ι = b ≫ W.ι) :
    pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp) (by rw [Category.comp_id, hc]) ≫
      (restrictIso z W h).hom = (restrictIso z W b).hom ≫ bc z c (h ≫ W.ι) (b ≫ W.ι) w := by
  apply pullback.hom_ext
  · simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_fst_assoc, restrictIso_hom_fst]
  · simp only [bc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_snd_assoc, restrictIso_hom_snd]

theorem isHilbRep_restrict_local : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (W : S.Opens),
    GlobalTheory.HilbertSch.IsHilbRep (z ∣_ W) r → ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x := by
  intro S Z z r W hR
  obtain ⟨H, h, U, u, hprop, hcl, hfin, hflat, hrk, huniv⟩ := hR
  haveI := hcl
  have hv : IsFinFlatRk ((u ≫ (restrictIso z W h).hom) ≫ pullback.snd z (h ≫ W.ι)) r := by
    rw [Category.assoc, restrictIso_hom_snd]
    exact ⟨hfin, hflat, hrk⟩
  set y := mkPt (h ≫ W.ι) (u ≫ (restrictIso z W h).hom) hv with hy
  refine ⟨H, y, h, hprop, rfl, ?_⟩
  intro Y x b hx
  obtain ⟨g, J⟩ := x
  change g = b ≫ W.ι at hx
  subst hx
  set v' := J.1.subschemeι ≫ (restrictIso z W b).inv with hv'
  have e : v' ≫ pullback.snd (z ∣_ W) b = J.1.subschemeι ≫ pullback.snd z (b ≫ W.ι) := by
    rw [hv', Category.assoc, restrictIso_inv_snd]
  have key : ∀ c : Y ⟶ H, HPt.map c y = ⟨b ≫ W.ι, J⟩ ↔ ∃ hf : c ≫ h = b, ∃ w : J.1.subscheme ⟶ U,
      IsPullback v' w (pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp)
        (by rw [Category.comp_id, hf])) u := by
    intro c
    constructor
    · intro hc
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := congrArg Sigma.fst hc
      have hf : c ≫ h = b := by
        rw [← cancel_mono W.ι, Category.assoc]
        exact h1
      refine ⟨hf, ?_⟩
      rw [HPt.map_eq_mk_iff c y h1] at hc
      have hc' : (u ≫ (restrictIso z W h).hom).ker.comap (bc z c (h ≫ W.ι) (b ≫ W.ι) h1) =
          J.1.subschemeι.ker := hc.trans (Scheme.IdealSheafData.ker_subschemeι _).symm
      obtain ⟨w, hw⟩ := (ker_comap_eq_ker_iff _ _ _).1 hc'
      refine ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b).symm (Iso.refl _) (restrictIso z W h).symm
        ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · simp only [Iso.symm_hom]
        rw [Iso.comp_inv_eq, Category.assoc, restrictIso_natural z W b h c hf h1, Iso.inv_hom_id_assoc]
      · simp
    · rintro ⟨hf, w, hw⟩
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := by rw [← Category.assoc, hf]
      rw [HPt.map_eq_mk_iff c y h1]
      refine (?_ : _ = J.1.subschemeι.ker).trans (Scheme.IdealSheafData.ker_subschemeι _)
      refine (ker_comap_eq_ker_iff _ (u ≫ (restrictIso z W h).hom) _).2 ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b) (Iso.refl _) (restrictIso z W h) ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · exact restrictIso_natural z W b h c hf h1
      · simp
  have hJ := J.2
  rw [← e] at hJ
  obtain ⟨f, hfP, huniq⟩ := huniv Y b _ v' inferInstance hJ.1 hJ.2.1 hJ.2.2
  exact ⟨f, (key f).2 hfP, fun c hc => huniq c ((key c).1 hc)⟩

end GlobalTheory.HilbGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointGlueOpenCover
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

section
variable {S Z : Scheme.{0}} (z : Z ⟶ S)

theorem bc_fst {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.fst z g = pullback.fst z k := by
  simp only [bc, pullback.map, pullback.lift_fst, Category.comp_id]

theorem bc_snd {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.snd z g = pullback.snd z k ≫ c := by
  simp only [bc, pullback.map, pullback.lift_snd]

end

theorem isFinFlatRk_of_cover {V Y : Scheme.{0}} (g : V ⟶ Y) (𝒰 : Y.OpenCover) (r : ℕ)
    (h : ∀ i, ∃ (Q : Scheme.{0}) (p : Q ⟶ V) (q : Q ⟶ 𝒰.X i), IsPullback p q g (𝒰.f i) ∧ IsFinFlatRk q r) :
    IsFinFlatRk g r := by
  choose Q p q hP hq using h
  have i1 : IsZariskiLocalAtTarget @IsFinite.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have i2 : IsZariskiLocalAtTarget @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  have hq' : ∀ i, IsFinFlatRk (pullback.snd g (𝒰.f i)) r := fun i => by
    rw [← (hP i).isoPullback_inv_snd]
    exact (hq i).iso_comp _
  have hF : IsFinite g := IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) 𝒰 fun i => (hq' i).1
  have hL : Flat g := IsZariskiLocalAtTarget.of_openCover (P := @Flat) 𝒰 fun i => (hq' i).2.1
  refine ⟨hF, hL, fun y => ?_⟩
  obtain ⟨i, y', rfl⟩ := 𝒰.exists_eq y
  rw [← Scheme.Hom.finrank_of_isPullback (p i) (q i) g (𝒰.f i) (hP i) y', (hq i).2.2]

theorem HPt.exists_glue : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x : ∀ i, GlobalTheory.HilbGlue.HPt z r (𝒰.X i)), (∀ i j (R : Scheme.{0}) (b : R ⟶ 𝒰.X i) (c : R ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → GlobalTheory.HilbGlue.HPt.map b (x i) = GlobalTheory.HilbGlue.HPt.map c (x j)) → ∃ y : GlobalTheory.HilbGlue.HPt z r Y, ∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) y = x i := by
  intro S Z z r Y 𝒰 x hx
  obtain ⟨f, hf⟩ : ∃ f : Y ⟶ S, ∀ i, 𝒰.f i ≫ f = (x i).1 :=
    ⟨𝒰.glueMorphisms (fun i => (x i).1) fun i j =>
      congrArg Sigma.fst (hx i j _ _ _ pullback.condition), fun i => 𝒰.ι_glueMorphisms _ _ i⟩
  let e : ∀ i, pullback z (x i).1 ⟶ pullback z f := fun i => bc z (𝒰.f i) f (x i).1 (hf i)
  have hP : ∀ i, IsPullback (e i) (pullback.snd z (x i).1) (pullback.snd z f) (𝒰.f i) :=
    fun i => isPullback_bc z _ _ _ (hf i)
  have he : ∀ i, IsOpenImmersion (e i) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i).flip inferInstance
  have hcov : ∀ p : ↥(pullback z f), ∃ i, p ∈ Set.range (e i) := by
    intro p
    obtain ⟨i, y', hy'⟩ := 𝒰.exists_eq (pullback.snd z f p)
    obtain ⟨q, hq⟩ : p ∈ Set.range (pullback.fst (pullback.snd z f) (𝒰.f i)) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨y', hy'⟩
    refine ⟨i, (hP i).isoPullback.inv q, ?_⟩
    rw [← hq, ← Scheme.Hom.comp_apply, (hP i).isoPullback_inv_fst]
  have fi : ∀ i, e i ≫ pullback.fst z f = pullback.fst z (x i).1 := fun i => by
    simp only [e, bc, pullback.map, pullback.lift_fst, Category.comp_id]
  have hK : ∀ i j (Q : Scheme.{0}) (a : Q ⟶ pullback z (x i).1) (b : Q ⟶ pullback z (x j).1),
      a ≫ e i = b ≫ e j → (x i).2.1.comap a = (x j).2.1.comap b := by
    intro i j Q a b hab
    have hbc : (a ≫ pullback.snd z (x i).1) ≫ 𝒰.f i = (b ≫ pullback.snd z (x j).1) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← (hP i).w, ← (hP j).w, reassoc_of% hab]
    have H := hx i j Q _ _ hbc
    have w : (a ≫ pullback.snd z (x i).1) ≫ (x i).1 = (b ≫ pullback.snd z (x j).1) ≫ (x j).1 :=
      congrArg Sigma.fst H
    have H' := (HPt.map_eq_mk_iff _ (x i) w ((x j).2.pull _ rfl)).1 H
    have hs : (a ≫ pullback.fst z (x i).1) ≫ z = 𝟙 Q ≫ (b ≫ pullback.snd z (x j).1) ≫ (x j).1 := by
      rw [Category.id_comp, ← w, Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨s, hs1, hs2⟩ : ∃ s : Q ⟶ pullback z ((b ≫ pullback.snd z (x j).1) ≫ (x j).1),
        s ≫ pullback.fst _ _ = a ≫ pullback.fst z (x i).1 ∧ s ≫ pullback.snd _ _ = 𝟙 Q :=
      ⟨pullback.lift _ _ hs, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hfst : a ≫ pullback.fst z (x i).1 = b ≫ pullback.fst z (x j).1 := by
      rw [← fi i, ← fi j, reassoc_of% hab]
    have ha : a = s ≫ bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have hb : b = s ≫ bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1, hfst]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have e1 : (x i).2.1.comap a = ((x i).2.1.comap (bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← ha]
    have e2 : (x j).2.1.comap b = ((x j).2.1.comap (bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← hb]
    rw [e1, e2, H']
    rfl
  obtain ⟨I, hI⟩ := GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions GlobalTheory.T.exists_idealSheafData_of_compatible_ideals (ι := 𝒰.I₀) (fun i : 𝒰.I₀ => pullback z (x i).1) e he hcov (fun i : 𝒰.I₀ => (x i).2.1) hK
  have hfr : IsFinFlatRk (I.subschemeι ≫ pullback.snd z f) r := by
    refine isFinFlatRk_of_cover _ 𝒰 r fun i => ⟨(I.comap (e i)).subscheme, _, _,
      (isPullback_comap I (e i)).flip.paste_vert (hP i), ?_⟩
    have := (x i).2.2
    rw [← hI i] at this
    exact this
  refine ⟨⟨f, I, hfr⟩, fun i => ?_⟩
  exact (HPt.map_eq_mk_iff (𝒰.f i) ⟨f, I, hfr⟩ (hf i) (x i).2).2 (hI i)

end GlobalTheory.HilbGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealKilledByRingMapsWithPropertyLeKerApp
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem fromSpec_Sp_eq (R' : Type) [CommRing R'] {W : (Sp R').Opens} (hW : IsAffineOpen W) :
    hW.fromSpec = spMap ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
      (Sp R').presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (𝟙 (Sp R')) (isAffineOpen_top (Sp R')) hW le_top
  rw [Category.comp_id, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h]
  simp [spMap, Scheme.Hom.appLE]

theorem killIdeal_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
    P R' x → P R'' (spMap g ≫ x)) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), P R' x →
    ∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom := by
  intro S P hP R' _ x hx V hV a ha
  rw [RingHom.mem_ker]
  apply (Sp R').IsSheaf.section_ext
  intro p hp
  obtain ⟨W, hWa, hpW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R').isBasis_affineOpens) hp
  refine ⟨W, hWle, hpW, ?_⟩
  have hW : IsAffineOpen W := hWa
  have e : hW.fromSpec ≫ x = spMap (x.appLE V W hWle).hom ≫ hV.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec x hV hW hWle]; rfl
  have hy : ptQ P V hV _ (x.appLE V W hWle).hom := by
    show P _ (spMap (x.appLE V W hWle).hom ≫ hV.fromSpec)
    rw [← e, fromSpec_Sp_eq]
    exact hP _ _ _ x hx
  have h0 := ha _ _ hy
  rw [map_zero]
  simpa [Scheme.Hom.appLE] using h0

end GlobalTheory.PtClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealRepresentsOfAwayCover
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem exists_pow_mul_eq_zero_of_represents_away {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop}
    (hbc : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
      Q R' f → Q R'' (g.comp f))
    (a : A) {Ja : Ideal (Localization.Away a)}
    (hJa : Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) Ja)
    {R' : Type} [CommRing R'] (f : A →+* R') (hf : Q R' f) (x : A)
    (hx : algebraMap A (Localization.Away a) x ∈ Ja) : ∃ m : ℕ, f a ^ m * f x = 0 := by
  have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
      (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
  have h1 : Q _ ((algebraMap R' (Localization.Away (f a))).comp f) :=
    hbc _ _ (algebraMap R' (Localization.Away (f a))) f hf
  rw [← e] at h1
  have h2 := (hJa _ (Localization.awayMap f a)).1 h1 hx
  rw [RingHom.mem_ker, ← RingHom.comp_apply, e, RingHom.comp_apply,
    IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))] at h2
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := h2
  exact ⟨m, hm⟩

theorem represents_of_away_cover : ∀ (A : Type) [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
    Q R' f → Q R'' (g.comp f)) →
  (∀ (R' : Type) [CommRing R'] (f : A →+* R') (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
    (∀ r ∈ t, Q (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) → Q R' f) →
  ∀ (s : Finset A), Ideal.span (s : Set A) = ⊤ →
  (∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
    Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) J) →
  ∃ J : Ideal A, Represents Q J := by
  classical
  intro A _ Q hbc hloc s hs hJ
  choose! J' hJ' using hJ
  refine ⟨⨅ a ∈ s, (J' a).comap (algebraMap A (Localization.Away a)),
    fun R' _ f ↦ ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩⟩
  · intro x hx
    simp only [Submodule.mem_iInf, Ideal.mem_comap] at hx
    rw [RingHom.mem_ker]
    have hspan : Ideal.span ((f : A → R') '' (s : Set A)) = ⊤ := by
      rw [← Ideal.map_span, hs, Ideal.map_top]
    have := Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule R' R') _ hspan (f x) ?_
    · simpa using this
    rintro ⟨_, b, hb, rfl⟩
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc b (hJ' b hb) f hf x (hx b hb)
    exact ⟨m, by simpa [smul_eq_mul] using hm⟩
  · apply hloc R' f (s.image f)
    · rw [Finset.coe_image, ← Ideal.map_span, hs, Ideal.map_top]
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hr
    have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
        (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
    rw [← e]
    refine ((hJ' a ha) _ (Localization.awayMap f a)).2 ?_
    intro j hj
    obtain ⟨⟨y, _, n, rfl⟩, hy⟩ := IsLocalization.surj (Submonoid.powers a) j
    simp only at hy
    have hyJ : algebraMap A (Localization.Away a) y ∈ J' a := hy ▸ Ideal.mul_mem_right _ _ hj
    have hb : ∀ b ∈ s, ∃ m : ℕ, algebraMap A (Localization.Away b) (a ^ m * y) ∈ J' b := by
      intro b hbs
      let p : A →+* (Localization.Away b ⧸ J' b) :=
        (Ideal.Quotient.mk (J' b)).comp (algebraMap A (Localization.Away b))
      have hp : Q _ p := ((hJ' b hbs) _ (Ideal.Quotient.mk (J' b))).2 (by rw [Ideal.mk_ker])
      obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc a (hJ' a ha) p hp y hyJ
      refine ⟨m, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [p] using hm
    choose! m hm using hb
    have hM : a ^ (s.sup m) * y ∈ ⨅ b ∈ s, (J' b).comap (algebraMap A (Localization.Away b)) := by
      simp only [Submodule.mem_iInf, Ideal.mem_comap]
      intro b hbs
      have : a ^ (s.sup m) * y = a ^ (s.sup m - m b) * (a ^ m b * y) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hbs)]
      rw [this, map_mul]
      exact Ideal.mul_mem_left _ _ (hm b hbs)
    have h0 := hf hM
    rw [RingHom.mem_ker, map_mul, map_pow] at h0
    rw [RingHom.mem_ker]
    have hu : IsUnit (Localization.awayMap f a (algebraMap A _ (a ^ n))) := by
      rw [← RingHom.comp_apply, e, RingHom.comp_apply, map_pow]
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f a)) (f a)).pow n
    have h3 : Localization.awayMap f a j * Localization.awayMap f a (algebraMap A _ (a ^ n)) = 0 := by
      rw [← map_mul, hy, ← RingHom.comp_apply, e, RingHom.comp_apply,
        IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))]
      exact ⟨⟨_, s.sup m, rfl⟩, h0⟩
    exact (hu.mul_left_eq_zero).1 h3

end GlobalTheory.PtClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleIsDomainIsIntegrallyClosed
section
open IsLocalRing

namespace GlobalTheory

namespace IndEtaleNormal

open Polynomial

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]

lemma exists_mem_of_finset (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (T : Finset S) : ∃ i, ∀ t ∈ T, t ∈ Si i := by
  classical
  choose idx hidx using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (T.image idx)
  exact ⟨M, fun t ht => hmono (hM _ (Finset.mem_image_of_mem idx ht)) (hidx t)⟩

lemma isDomain [Nontrivial S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (hdom : ∀ i, IsDomain (Si i)) : IsDomain S := by
  classical
  have : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov {x, y}
    have hx : x ∈ Si i := hi x (by simp)
    have hy : y ∈ Si i := hi y (by simp)
    haveI := hdom i
    have h0 : (⟨x, hx⟩ : Si i) * ⟨y, hy⟩ = 0 := Subtype.ext (by simpa using hxy)
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  exact NoZeroDivisors.to_isDomain S

lemma isIntegrallyClosed [IsDomain S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i)
    (hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  obtain ⟨p, hpm, hp⟩ := hx
  obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov (insert a (insert b p.coeffs))
  haveI := (hic i).1
  haveI := (hic i).2
  have ha : a ∈ Si i := hi a (by simp)
  have hb' : b ∈ Si i := hi b (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set g : Si i →+* FractionRing S := (algebraMap S (FractionRing S)).comp (algebraMap (Si i) S)
    with hg_def
  have hg : Function.Injective g :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (Si i) →+* FractionRing S := IsFractionRing.lift hg
  have hφ : ∀ c : Si i, φ (algebraMap (Si i) (FractionRing (Si i)) c) = g c := fun c =>
    IsFractionRing.lift_algebraMap hg c
  have hlift : p ∈ Polynomial.lifts (algebraMap (Si i) S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨p.coeff n, hi _ (by simp [Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  set y : FractionRing (Si i) := algebraMap (Si i) (FractionRing (Si i)) ⟨a, ha⟩ /
    algebraMap (Si i) (FractionRing (Si i)) ⟨b, hb'⟩ with hy_def
  have hφy : φ y = algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b := by
    rw [hy_def, map_div₀, hφ, hφ]
    rfl
  have hyint : IsIntegral (Si i) y := by
    refine ⟨q, hqm, φ.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, hφy]
    have : φ.comp (algebraMap (Si i) (FractionRing (Si i))) = g :=
      RingHom.ext hφ
    rw [this, hg_def, ← Polynomial.eval₂_map, hq]
    exact hp
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (Si i))).mp (hic i).2 hyint
  refine ⟨(c : S), ?_⟩
  rw [← hφy, ← hc, hφ]
  rfl

end IndEtaleNormal

theorem indEtale_isDomain_isIntegrallyClosed :
    ∀ (R S : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Algebra R S]
      [Nontrivial S], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
        (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
        ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
          (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) →
      IsDomain S ∧ IsIntegrallyClosed S := by
  intro R S _ _ _ _ _ _ h
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := h
  have hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    obtain ⟨h1, h2⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R A q
    exact ⟨MulEquiv.isDomain (Localization.AtPrime q) e.symm.toMulEquiv,
      IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
  haveI := IndEtaleNormal.isDomain Si hmono hcov (fun i => (hic i).1)
  exact ⟨inferInstance, IndEtaleNormal.isIntegrallyClosed Si hmono hcov hic⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
section
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by
  first | exact @GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map | exact GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map | (intros; apply GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralComplexGaussianPosDefHermitianPartStatement
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ), (A + Aᴴ).PosDef → A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧ ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  first | exact @GlobalTheory.MatrixGaussian.integral_gaussian | exact GlobalTheory.MatrixGaussian.integral_gaussian | (intros; apply GlobalTheory.MatrixGaussian.integral_gaussian <;> assumption)
end

