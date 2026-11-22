import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationIffDualNumberPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.PtDual

variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]

def ev (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) : Γ(X, W) →+* R :=
  (v.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

theorem ev_fromSpec (v : Sp R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (ev v U h)) ≫ hU.fromSpec = v := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec v hU (isAffineOpen_top _) h
  rw [ev, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, this, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ev_ext {v v' : Sp R ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U)
    (e : ev v U h = ev v' U h') : v = v' := by
  rw [← ev_fromSpec v hU h, ← ev_fromSpec v' hU h', e]

theorem exists_ev {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) →+* R) :
    ∃ (v : Sp R ⟶ X) (h : ⊤ ≤ v ⁻¹ᵁ U), ev v U h = φ := by
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_top
  refine ⟨_, h, ?_⟩
  have := ev_fromSpec _ hU h
  rw [cancel_mono] at this
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem ev_res (v : Sp R ⟶ X) {W W' : X.Opens} (e : W' ≤ W) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v ⁻¹ᵁ W') (f : Γ(X, W)) :
    ev v W' h' (resG X e f) = ev v W h f := by
  have : X.presheaf.map (homOfLE e).op ≫ v.appLE W' ⊤ h' = v.appLE W ⊤ h := Scheme.Hom.map_appLE ..
  unfold ev
  rw [← this]
  rfl

theorem ev_comp (φ : R →+* S) (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ W)
    (f : Γ(X, W)) : ev (spMap φ ≫ v) W h' f = φ (ev v W h f) := by
  have h1 : v.appLE W ⊤ h ≫ (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ ≫ v).appLE W ⊤ h' :=
    Scheme.Hom.appLE_comp_appLE ..
  have h2 : (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg _ ((Sp S).presheaf.map_id _)).trans (Category.comp_id _)
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  unfold ev
  rw [← h1, h2, Category.assoc]
  erw [h3]
  rfl

abbrev pt0 : Sp ℂ ⟶ Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

theorem le_preimage_iff (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ W ↔ ⊤ ≤ (pt0 ≫ v) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  refine ⟨fun h p _ => h (Set.mem_univ _), fun h p _ => ?_⟩
  have hs : Function.Surjective (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hp : (p : PrimeSpectrum (DualNumber ℂ)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    have hx' : x.fst = 0 := hx
    refine (p : PrimeSpectrum (DualNumber ℂ)).isPrime.mem_of_pow_mem 2 ?_
    have : x ^ 2 = 0 := by
      ext <;> simp [pow_two, hx']
    rw [this]
    exact zero_mem _
  obtain ⟨q, rfl⟩ := hp
  exact h (Set.mem_univ q)

theorem fst_ev {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W)
    (f : Γ(X, W)) : (ev v W h f).fst = valAt' y W f := by
  subst hv
  have h' := (le_preimage_iff v W).1 h
  rw [valAt'_eq_valAtHom _ h']
  exact (ev_comp _ v W h h' f).symm

def derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ W) :
    Γ(X, W) →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (valAt' y W f) + TrivSqZeroExt.inr (δ W f)
  map_one' := by
    have := hδ.mul W h 1 1
    rw [_root_.mul_one, valAt'_one y h, _root_.one_mul, left_eq_add] at this
    ext <;> simp [valAt'_one y h, this]
  map_mul' a b := by
    ext
    · simp [valAt'_mul]
    · simp [hδ.mul W h, mul_comm]
  map_zero' := by
    have := hδ.add W h 0 0
    rw [add_zero, left_eq_add] at this
    ext <;> simp [valAt'_zero, this]
  map_add' a b := by
    ext
    · simp [valAt'_add]
    · simp [hδ.add W h]

theorem fst_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).fst = valAt' y W f := by
  simp [derHom]

theorem snd_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).snd = δ W f := by
  simp [derHom]

theorem derHom_res {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {W W' : X.Opens} (e : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : derHom hδ W' h' (resG X e f) = derHom hδ W h f := by
  ext
  · rw [fst_derHom, fst_derHom, valAt'_res y e f h']
  · rw [snd_derHom, snd_derHom, hδ.res W W' e h']

theorem exists_affine (y : Sp ℂ ⟶ X) : ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ y ⁻¹ᵁ U := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  exact ⟨U, hU, (top_le_preimage_iff_mem y U).2 hy⟩

theorem ev_eq_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : pt0 ≫ v = y) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (e : ev v U h = derHom hδ U h') (W : X.Opens) (k : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : (ev v W k f).snd = δ W f := by
  have k' : ⊤ ≤ y ⁻¹ᵁ W := hv ▸ (le_preimage_iff v W).1 k
  obtain ⟨g, hg, hy⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (top_le_preimage_iff_mem y W).1 k'⟩
    ((top_le_preimage_iff_mem y U).1 h')
  have l' : ⊤ ≤ y ⁻¹ᵁ X.basicOpen g := (top_le_preimage_iff_mem y _).2 hy
  have l : ⊤ ≤ v ⁻¹ᵁ X.basicOpen g := (le_preimage_iff v _).2 (hv ▸ l')
  have := hU.isLocalization_basicOpen g
  have e' : ev v _ l = derHom hδ _ l' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
    refine (ev_res v (X.basicOpen_le g) h l a).trans ?_
    rw [e]
    exact (derHom_res hδ (X.basicOpen_le g) h' l' a).symm
  rw [← ev_res v hg k l, e', derHom_res hδ hg k' l', snd_derHom]

open Classical in
theorem exists_ptDer {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) :
    ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  have H : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ⊤ ≤ v ⁻¹ᵁ W := fun W h => (le_preimage_iff v _).2 (hv ▸ h)
  refine ⟨fun W f => if h : ⊤ ≤ v ⁻¹ᵁ W then (ev v W h f).snd else 0, ⟨?_, ?_, ?_⟩, fun W h f => ?_⟩
  · intro W h f f'
    simp only [dif_pos (H W h), map_add, TrivSqZeroExt.snd_add]
  · intro W h f f'
    simp only [dif_pos (H W h), map_mul, DualNumber.snd_mul, fst_ev hv]
    ring
  · intro W W' e h f
    have k := H W (top_le_preimage_mono y e h)
    simp only [dif_pos (H W' h), dif_pos k, ev_res v e k]
  · simp only [dif_pos h]

theorem existsUnique_point {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) :
    ∃! v : Sp (DualNumber ℂ) ⟶ X, pt0 ≫ v = y ∧
      ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  obtain ⟨U, hU, h'⟩ := exists_affine y
  obtain ⟨v, h, e⟩ := exists_ev hU (derHom hδ U h')
  have hv : pt0 ≫ v = y := by
    refine ev_ext hU ((le_preimage_iff v U).1 h) h' (RingHom.ext fun f => ?_)
    rw [ev_comp _ v U h, e]
    exact (fst_derHom hδ U h' f).trans (valAt'_eq_valAtHom y h' f)
  refine ⟨v, ⟨hv, ev_eq_derHom hδ hv hU h h' e⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  have k : ⊤ ≤ w ⁻¹ᵁ U := (le_preimage_iff w _).2 (hw ▸ h')
  refine ev_ext hU k h (RingHom.ext fun f => ?_)
  rw [e]
  ext
  · rw [fst_ev hw, fst_derHom]
  · rw [hw', snd_derHom]

end GlobalTheory.KS.PtDual

namespace GlobalTheory.KS

theorem ptDer_iff_dualPoint : ∀ (X : Scheme.{0}) (y : Sp ℂ ⟶ X), (∀ δ, PtDer y δ → ∃! v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y → ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f :=
  fun _ _ => ⟨fun _ hδ => PtDual.existsUnique_point hδ, fun _ hv => PtDual.exists_ptDer hv⟩

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsExtensionAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SectionsDescent

open GlobalTheory.FieldBaseChange

def rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem rs_rs {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (x : Γ(X, U)) :
    rs k (rs h x) = rs (k.trans h) x := by
  unfold rs
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem rs_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)) : rs h x = x := by
  show (X.presheaf.map (𝟙 _)).hom _ = _
  rw [CategoryTheory.Functor.map_id]; rfl

theorem pre_mono {X Y : Scheme.{0}} (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U :=
  fun _ hy => h hy

theorem app_rs {X Y : Scheme.{0}} (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (φ.app V).hom (rs h x) = rs (pre_mono φ h) ((φ.app U).hom x) :=
  congrArg (fun q => q.hom x) (φ.naturality (homOfLE h).op)

theorem appLE_eq {X Y : Scheme.{0}} (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (x : Γ(X, U)) :
    (φ.appLE U V h).hom x = rs h ((φ.app U).hom x) := rfl

theorem constFn_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn p U a = constHom p U a := rfl

theorem rs_constHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    rs h (constHom p U a) = constHom p V a := rs_rs le_top h _

theorem ext_cover {X : Scheme.{0}} {U : X.Opens} {J : Type} (V : J → X.Opens) (hV : ∀ i, V i ≤ U)
    (hc : U ≤ iSup V) {s t : Γ(X, U)} (h : ∀ i, rs (hV i) s = rs (hV i) t) : s = t :=
  X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hV i)) hc s t h

theorem le_iSup_affine {X : Scheme.{0}} (U : X.Opens) :
    U ≤ ⨆ V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U}, V.1 := fun x hx => by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVU⟩, hxV⟩

theorem ext_affine {X : Scheme.{0}} {U : X.Opens} {s t : Γ(X, U)}
    (h : ∀ (V : X.Opens) (_ : IsAffineOpen V) (hV : V ≤ U), rs hV s = rs hV t) : s = t :=
  ext_cover (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) (fun V => V.2.2) (le_iSup_affine U)
    fun V => h V.1 V.2.1 V.2.2

theorem glue_affine {X : Scheme.{0}} (U : X.Opens)
    (f : ∀ (V : X.Opens), IsAffineOpen V → V ≤ U → Γ(X, V))
    (hf : ∀ V W hV hW (hVU : V ≤ U) (h : W ≤ V), rs h (f V hV hVU) = f W hW (h.trans hVU)) :
    ∃ y : Γ(X, U), ∀ V hV (h : V ≤ U), rs h y = f V hV h := by
  obtain ⟨y, hy, -⟩ := X.sheaf.existsUnique_gluing'
    (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) U (fun V => homOfLE V.2.2) (le_iSup_affine U)
    (fun V => f V.1 V.2.1 V.2.2) (fun V V' => by
      refine ext_affine (X := X) (U := V.1 ⊓ V'.1) fun W hW h => ?_
      refine (rs_rs inf_le_left h _).trans (Eq.trans ?_ (rs_rs inf_le_right h _).symm)
      rw [hf _ _ _ hW, hf _ _ _ hW])
  exact ⟨y, fun V hV h => hy ⟨V, hV, h⟩⟩

section Field

variable {K F : Type} [Field K] [Field F] [Algebra K F] {Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F))))

theorem isExtension_affine {U : Y.Opens} (hU : IsAffineOpen U) :
    IsExtension (pullFn H.w (le_refl (p ⁻¹ᵁ U))) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (CommRingCat.ofHom (constHom π U)) (CommRingCat.ofHom (algebraMap K F)) (p.app U)
      (CommRingCat.ofHom (constHom π' (p ⁻¹ᵁ U))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of F)) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
  let : Algebra (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) := (p.app U).hom.toAlgebra
  let : Algebra K (FnOver π' (p ⁻¹ᵁ U)) := ((constHom π' (p ⁻¹ᵁ U)).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F (FnOver π' (p ⁻¹ᵁ U)) := .of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower K (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (congrArg (fun q => q.hom r) po'.w).symm
  have : Algebra.IsPushout K F (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    (CommRingCat.isPushout_iff_isPushout.mp po').symm
  exact isExtension_of_isPushout _ fun x => rs_self _ _

theorem coord_mul_rs {V W : Y.Opens} (hV : IsAffineOpen V) (h : W ≤ V) {ℓ : F →ₗ[K] K}
    {Λ : FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V} {Λ' : FnOver π' (p ⁻¹ᵁ W) →+ FnOver π W}
    (hΛ : IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ Λ) (hΛ' : IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ W))) ℓ Λ')
    (u : Γ(Y, W)) (x : Γ(Y', p ⁻¹ᵁ V)) :
    Λ' ((p.app W).hom u * rs (pre_mono p h) x) = u * rs h (Λ x) :=
  IsCoord.natural (isExtension_affine H hV).span hΛ hΛ'
    (LinearMap.mulLeft K (show FnOver π W from u) ∘ₗ resFn π h)
    (LinearMap.mulLeft F (show FnOver π' (p ⁻¹ᵁ W) from (p.app W).hom u) ∘ₗ
      resFn π' (pre_mono p h))
    (fun v => by
      show (p.app W).hom u * rs _ (rs _ ((p.app V).hom v)) = rs _ ((p.app W).hom (u * rs h v))
      rw [rs_self, rs_self, map_mul]
      exact congrArg _ (app_rs p h v).symm) x

theorem exists_coord {ℓ : F →ₗ[K] K}
    (Λ : ∀ V : Y.Opens, IsAffineOpen V → FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V)
    (hΛ : ∀ V hV, IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ (Λ V hV)) (U : Y.Opens) (x : Γ(Y', p ⁻¹ᵁ U)) :
    ∃ y : Γ(Y, U), ∀ V hV (h : V ≤ U), rs h y = Λ V hV (rs (pre_mono p h) x) :=
  glue_affine U _ fun V W hV hW hVU h => by
    have := coord_mul_rs H hV h (hΛ V hV) (hΛ W hW) 1 (rs (pre_mono p hVU) x)
    rw [map_one, _root_.one_mul, _root_.one_mul, rs_rs] at this
    exact this.symm

theorem pre_le_chart (M : LB Y) (p : Y' ⟶ Y) (j : PUnit → M.ι) : p ⁻¹ᵁ M.U (j PUnit.unit) ≤ (M.pull p).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

def loc {M : LB Y} (t : (M.pull p).Sec) (j : M.ι) : Γ(Y', p ⁻¹ᵁ M.U j) :=
  rs (pre_le_chart M p fun _ => j) (t.f fun _ => j)

theorem sec_compat {M : LB Y} (s : M.Sec) (i j : M.ι) {W : Y.Opens} (hi : W ≤ M.U i) (hj : W ≤ M.U j) :
    rs hi (s.f i) = rs (le_inf hi hj) (M.g i j : Γ(Y, M.U i ⊓ M.U j)) * rs hj (s.f j) := by
  have := congrArg (rs (le_inf hi hj)) (s.compat i j)
  rw [map_mul] at this
  exact (rs_rs inf_le_left _ _).symm.trans (this.trans (congrArg _ (rs_rs inf_le_right _ _)))

theorem loc_compat {M : LB Y} (t : (M.pull p).Sec) (i j : M.ι) {W : Y.Opens} (hi : W ≤ M.U i)
    (hj : W ≤ M.U j) :
    rs (pre_mono p hi) (loc t i) =
      (p.app W).hom (rs (le_inf hi hj) (M.g i j : Γ(Y, M.U i ⊓ M.U j))) * rs (pre_mono p hj) (loc t j) := by
  unfold loc
  rw [rs_rs, rs_rs, sec_compat t (fun _ => i) (fun _ => j) ((pre_mono p hi).trans (pre_le_chart M p fun _ => i))
    ((pre_mono p hj).trans (pre_le_chart M p fun _ => j)), app_rs]
  congr 1
  have e : ((M.pull p).g (fun _ => i) (fun _ => j) : Γ(Y', (M.pull p).U (fun _ => i) ⊓ (M.pull p).U fun _ => j)) =
      rs (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) (fun _ => i) PUnit.unit))
        (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) (fun _ => j) PUnit.unit)))
        ((p.app (M.U i ⊓ M.U j)).hom (M.g i j : Γ(Y, M.U i ⊓ M.U j))) := by
    have key : ∀ {G : Type} [CommGroup G] (u : G), ∏ _k : PUnit.{1}, u ^ (1 : ℤ) = u := fun u => by simp
    exact congrArg Units.val (key _)
  rw [e]
  exact rs_rs _ _ _

theorem exists_coord_sec {ℓ : F →ₗ[K] K}
    (Λ : ∀ V : Y.Opens, IsAffineOpen V → FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V)
    (hΛ : ∀ V hV, IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ (Λ V hV)) {M : LB Y} (t : (M.pull p).Sec) :
    ∃ s : M.Sec, ∀ j V hV (h : V ≤ M.U j), rs h (s.f j) = Λ V hV (rs (pre_mono p h) (loc t j)) := by
  choose y hy using fun j => exists_coord H Λ hΛ (M.U j) (loc t j)
  refine ⟨⟨y, fun i j => ext_affine fun W hW h => ?_⟩, hy⟩
  have hi : W ≤ M.U i := h.trans inf_le_left
  have hj : W ≤ M.U j := h.trans inf_le_right
  rw [map_mul]
  refine (rs_rs inf_le_left h _).trans (Eq.trans ?_ (congrArg _ (rs_rs inf_le_right h _).symm))
  have := coord_mul_rs H hW le_rfl (hΛ W hW) (hΛ W hW) (rs h (M.g i j : Γ(Y, M.U i ⊓ M.U j)))
    (rs (pre_mono p hj) (loc t j))
  rw [rs_self] at this
  rw [hy i W hW hi, hy j W hW hj, loc_compat t i j hi hj]
  exact this.trans (congrArg _ (rs_self _ _))

include H in
theorem exists_sum_sec [CompactSpace Y] {M : LB Y} (hM : M.IsLB) (t : (M.pull p).Sec) :
    ∃ (J : Type) (S : Finset J) (c : J → F) (s : J → M.Sec), ∀ j : M.ι,
      loc t j = ∑ a ∈ S, constHom π' _ (c a) * (p.app _).hom ((s a).f j) := by
  classical
  let b := Module.Basis.ofVectorSpace K F
  choose Λ hΛ using fun a V (hV : IsAffineOpen V) => (isExtension_affine H hV).coord (b.coord a)
  choose s hs using fun a => exists_coord_sec H (Λ a) (hΛ a) t
  choose S hS hS' using fun j V (hV : IsAffineOpen V) (h : V ≤ M.U j) =>
    exists_expansion b (isExtension_affine H hV).span (fun a => hΛ a V hV) (rs (pre_mono p h) (loc t j))
  have hc : ∀ y : Y, ∃ (j : M.ι) (V : Y.Opens), IsAffineOpen V ∧ V ≤ M.U j ∧ y ∈ V := fun y => by
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ y))
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine _ hj)
    exact ⟨j, V.1, V.2.1, V.2.2, hV⟩
  choose J V hV hVJ hy using hc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y : Y => (V y : Set Y)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  let S₀ := T.biUnion fun y => S (J y) (V y) (hV y) (hVJ y)
  have z : ∀ a ∉ S₀, ∀ j, (s a).f j = 0 := fun a ha j => by
    refine ext_cover (fun y : T => M.U j ⊓ V y) (fun _ => inf_le_left) (fun x hx => ?_) fun y => ?_
    · obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hyT⟩, hx, hxy⟩
    · have z₀ : rs (hVJ y) ((s a).f (J y)) = 0 := (hs a _ _ (hV y) (hVJ y)).trans
        (hS _ _ _ _ a fun h => ha (Finset.mem_biUnion.2 ⟨y, y.2, h⟩))
      rw [sec_compat (s a) j (J y) inf_le_left (inf_le_right.trans (hVJ y)),
        ← rs_rs (hVJ y) inf_le_right, z₀, map_zero, map_zero, mul_zero]
  refine ⟨_, S₀, b, s, fun j => ?_⟩
  refine ext_cover (fun W : {W : Y.Opens // IsAffineOpen W ∧ W ≤ M.U j} => p ⁻¹ᵁ W.1)
    (fun W => pre_mono p W.2.2) (fun x hx => ?_) fun W => ?_
  · obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine (M.U j) (show p x ∈ M.U j from hx))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨W, hW⟩
  · obtain ⟨W, hW, h⟩ := W
    have e : ∀ a, rs (pre_mono p h) (constHom π' _ (b a) * (p.app _).hom ((s a).f j)) =
        constHom π' (p ⁻¹ᵁ W) (b a) *
          rs le_rfl ((p.app W).hom (Λ a W hW (rs (pre_mono p h) (loc t j)))) := fun a => by
      rw [map_mul, rs_constHom, ← app_rs p h, hs a j W hW h, rs_self]
    have e' : rs (pre_mono p h) (loc t j) = ∑ a ∈ S j W hW h ∪ S₀, constHom π' (p ⁻¹ᵁ W) (b a) *
          rs le_rfl ((p.app W).hom (Λ a W hW (rs (pre_mono p h) (loc t j)))) :=
      hS' j W hW h (S j W hW h ∪ S₀) Finset.subset_union_left
    refine e'.trans ((Finset.sum_congr rfl fun a _ => (e a).symm).trans
      ((Finset.sum_subset Finset.subset_union_right fun a _ ha => ?_).symm.trans (map_sum _ _ _).symm))
    rw [z a ha, map_zero, mul_zero, map_zero]

end Field

theorem main : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (M : LB X₀), M.IsLB → IsPullback φ p p₀ (spMap i) → ∀ t : (M.pull φ).Sec, ∃ (n : ℕ) (c : Fin n → K) (s : Fin n → M.Sec), ∀ j : PUnit → M.ι, ∀ h : (M.pull φ).U j ≤ φ ⁻¹ᵁ M.U (j PUnit.unit), t.f j = ∑ a, constFn p _ (c a) * (φ.appLE _ _ h).hom ((s a).f (j PUnit.unit)) := by
  intro K₀ K _ _ i X₀ X p₀ p φ _ _ M hM H t
  let := i.toAlgebra
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace p₀
  obtain ⟨J, S, c, s, e⟩ := exists_sum_sec (K := K₀) (F := K) H hM t
  refine ⟨S.card, fun a => c (S.equivFin.symm a), fun a => s (S.equivFin.symm a), fun j h => ?_⟩
  have e₁ : t.f j = rs h (loc t (j PUnit.unit)) := ((rs_rs _ _ _).trans (rs_self _ _)).symm
  rw [e₁, e, map_sum, ← Finset.sum_coe_sort, ← S.equivFin.symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, rs_constHom]
  rfl

end GlobalTheory.SectionsDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem isFinite_lift_comp {X X' X'' S S' S'' : Scheme.{0}} {s : X ⟶ S} {s' : X' ⟶ S'} {s'' : X'' ⟶ S''}
    {g : S' ⟶ S} {g' : S'' ⟶ S'} {g'' : S'' ⟶ S} (hg : g'' = g' ≫ g) {p : X' ⟶ X} {p' : X'' ⟶ X'}
    (w : p ≫ s = s' ≫ g) (w' : p' ≫ s' = s'' ≫ g') (w'' : (p' ≫ p) ≫ s = s'' ≫ g'')
    (h : IsFinite (pullback.lift p s' w)) (h' : IsFinite (pullback.lift p' s'' w')) :
    IsFinite (pullback.lift (p' ≫ p) s'' w'') := by
  subst hg
  obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : pullback s' g' ⟶ pullback s (g' ≫ g),
      θ ≫ pullback.fst s (g' ≫ g) = pullback.fst s' g' ≫ p ∧ θ ≫ pullback.snd s (g' ≫ g) = pullback.snd s' g' :=
    ⟨pullback.lift (pullback.fst s' g' ≫ p) (pullback.snd s' g')
      (by rw [Category.assoc, w, pullback.condition_assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ : pullback s (g' ≫ g) ⟶ pullback s g,
      κ ≫ pullback.fst s g = pullback.fst s (g' ≫ g) ∧ κ ≫ pullback.snd s g = pullback.snd s (g' ≫ g) ≫ g' :=
    ⟨pullback.lift (pullback.fst s (g' ≫ g)) (pullback.snd s (g' ≫ g) ≫ g')
      (by rw [Category.assoc]; exact pullback.condition), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  have hfac : pullback.lift (p' ≫ p) s'' w'' = pullback.lift p' s'' w' ≫ θ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hθ1, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, hθ2, pullback.lift_snd]

  have hright : IsPullback (pullback.snd s (g' ≫ g)) κ g' (pullback.snd s g) := by
    refine IsPullback.of_bot ?_ hκ2.symm (IsPullback.of_hasPullback s g).flip
    rw [hκ1]
    exact (IsPullback.of_hasPullback s (g' ≫ g)).flip

  have hsq : IsPullback θ (pullback.fst s' g') κ (pullback.lift p s' w) := by
    refine IsPullback.of_right ?_ ?_ hright
    · rw [hθ2, pullback.lift_snd]
      exact (IsPullback.of_hasPullback s' g').flip
    · apply pullback.hom_ext
      · simp only [Category.assoc, hκ1, hθ1, pullback.lift_fst]
      · simp only [Category.assoc, hκ2, reassoc_of% hθ2, pullback.lift_snd, pullback.condition]
  have hfin : IsFinite θ := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip h
  rw [hfac]
  infer_instance

theorem above_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (r : U' ⟶ U) (ν : SABMap t' t r) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (ν'' : SABMap t'' t (r' ≫ r)) (a : C'.Above C b r ν) (a' : C''.Above C' b' r' ν'), ν''.φ = ν'.φ ≫ ν.φ → ∃ a'' : C''.Above C (b'.comp b) (r' ≫ r) ν'', a''.π = a'.π ≫ a.π ∧ a''.mu.φ = a'.mu.φ ≫ a.mu.φ := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' r ν r' ν' ν'' a a' hν
  obtain ⟨mu, hmu⟩ := sabComp pullCubComp E H _ _ _ C.t C'.t C''.t a.π a'.π a.mu a'.mu
  have hsp : spMap (b'.comp b) = spMap b' ≫ spMap b := by
    unfold spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hover : (a'.π ≫ a.π) ≫ C.s = C''.s ≫ spMap (b'.comp b) := by
    rw [hsp, Category.assoc, a.π_over, ← Category.assoc, a'.π_over, Category.assoc]
  refine ⟨⟨a'.π ≫ a.π, hover, isFinite_lift_comp hsp a.π_over a'.π_over hover a.fin a'.fin, mu, ?_, ?_⟩, rfl, hmu⟩
  · rw [← Category.assoc, a'.j_comm, Category.assoc, a.j_comm, Category.assoc]
  · rw [hmu, hν, ← Category.assoc, a'.φ_comm, Category.assoc, a.φ_comm, Category.assoc]

end GlobalTheory.Models
end

