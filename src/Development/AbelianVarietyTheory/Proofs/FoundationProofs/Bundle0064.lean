import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallPowDvdGerm
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
section
universe u v

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.PrimeSection

theorem res_appLE {X Y : Scheme.{u}} (j : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U) (h' : W' ≤ W) (s : Γ(X, U)) :
    Y.presheaf.map (homOfLE h').op (j.appLE U W h s) = j.appLE U W' (h'.trans h) s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {X Y : Scheme.{u}} (j : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U') (h' : U' ≤ U) (s : Γ(X, U)) :
    j.appLE U' W h (X.presheaf.map (homOfLE h').op s) =
      j.appLE U W (h.trans (j.preimage_mono h')) s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_appLE {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X) {k : Z ⟶ X} (hk : i ≫ j = k)
    {U : X.Opens} {W : Y.Opens} {A : Z.Opens} (h : W ≤ j ⁻¹ᵁ U) (h' : A ≤ i ⁻¹ᵁ W)
    (h'' : A ≤ k ⁻¹ᵁ U) (s : Γ(X, U)) :
    i.appLE W A h' (j.appLE U W h s) = k.appLE U A h'' s := by
  subst hk
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem appLE_bijective {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] {U : X.Opens}
    (hU : U ≤ j.opensRange) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Bijective (j.appLE U W h.le) := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  have := j.isIso_app U hU
  exact ConcreteCategory.bijective_of_isIso _

theorem eq_preimage_inf {X Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] {D U : X.Opens}
    (hj : j.opensRange = D) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) : W = j ⁻¹ᵁ (U ⊓ D) := by
  subst h hj
  exact le_antisymm (fun y hy ↦ ⟨hy, y, rfl⟩) fun y hy ↦ hy.1

theorem appLE_injective {X Y : Scheme.{u}} [IsIntegral X] (j : Y ⟶ X) [IsOpenImmersion j]
    [Nonempty Y] {U : X.Opens} {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Injective (j.appLE U W h.le) := by
  intro s s' H
  obtain ⟨y⟩ := ‹Nonempty Y›
  refine res_inf_injective (D := j.opensRange) (genericPoint_mem ⟨y, rfl⟩) U
    ((appLE_bijective j inf_le_right (eq_preimage_inf rfl h)).1 ?_)
  rw [appLE_res, appLE_res]
  exact H

section Immersion

variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
  [IsIntegral X] [IsLocallyNoetherian X]
  {Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] (hj : j.opensRange = X.basicOpen t)
  {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
  {W : ι → Y.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)

omit [IsIntegral X] [IsLocallyNoetherian X] in
include hj in

theorem exists_transport (r : ∀ a, Γ(Y, W a))
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (τ : Γ(Y, ⊤)ˣ) (hτ : (τ : Γ(Y, ⊤)) = j.appTop t) :
    ∃ (r' : ∀ a, Γ(X, U a ⊓ X.basicOpen t)) (τ' : Γ(X, X.basicOpen t)ˣ),
      (τ' : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t ∧
      (∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r' a) =
        X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op
          (g a b) * X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r' b)) ∧
      (∀ a, r' a = 0 → r a = 0) ∧ (∀ a, IsUnit (r a) → IsUnit (r' a)) ∧
      ∀ (n : ℤ) (a : ι) (s : Γ(X, U a)), X.presheaf.map (homOfLE inf_le_left).op s =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ' ^ n) : Γ(X, X.basicOpen t)) * r' a ↔
        j.appLE (U a) (W a) (hW a).le s =
          Y.presheaf.map (homOfLE le_top).op (↑(τ ^ n) : Γ(Y, ⊤)) * r a := by
  have hb := fun a ↦ appLE_bijective j (inf_le_right.trans hj.ge) (eq_preimage_inf hj (hW a))
  choose r' hr' using fun a ↦ (hb a).2 (r a)
  obtain ⟨τ', hτ'⟩ := exists_unit_eq_res t
  have htop : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ X.basicOpen t := fun y _ ↦ hj.le ⟨y, rfl⟩
  have hττ : Units.map (j.appLE _ ⊤ htop).hom.toMonoidHom τ' = τ := by
    ext
    rw [Units.coe_map, hτ, hτ']
    exact (appLE_res j _ _ _).trans (congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(Y, ⊤) ↦ φ t) j.appLE_eq_app)
  refine ⟨r', τ', hτ', fun a b ↦ ?_, fun a h ↦ by rw [← hr', h, map_zero], fun a h ↦ ?_,
    fun n a s ↦ ?_⟩
  · have hab : W a ⊓ W b = j ⁻¹ᵁ (U a ⊓ U b) := by rw [hW, hW]; rfl
    refine (appLE_bijective j (inf_le_right.trans hj.ge) (eq_preimage_inf hj hab)).1 ?_
    have := hr a b
    rw [← hr' a, ← hr' b, res_appLE, res_appLE] at this
    rw [map_mul, appLE_res, appLE_res, appLE_res]
    exact this
  · rw [← hr' a] at h
    exact (isUnit_map_iff (RingEquiv.ofBijective _ (hb a)) _).1 h
  · rw [← (hb a).1.eq_iff, map_mul, appLE_res, appLE_res, hr', ← hττ, ← map_zpow, Units.coe_map]
    exact iff_of_eq (congrArg (_ = · * _) (res_appLE j htop le_top _).symm)

include hη hp hj in

theorem existsUnique_zpow_mul_appLE (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    (τ : Γ(Y, ⊤)ˣ) (hτ : (τ : Γ(Y, ⊤)) = j.appTop t) {r : ∀ a, Γ(Y, W a)}
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(X, U a),
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, j.appLE (U a) (W a) (hW a).le (s a) =
        Y.presheaf.map (homOfLE le_top).op (↑(τ ^ n) : Γ(Y, ⊤)) * r a) ∧
      ∃ a, ∃ x, x ∉ X.basicOpen t ∧ x ∈ X.basicOpen (s a) := by
  obtain ⟨r', τ', hτ', hr', h0, -, H⟩ := exists_transport hj hW r hr τ hτ
  simpa only [H] using existsUnique_zpow_mul hη hp hU hg τ' hτ' hr'
    (hr0.imp fun a ha h ↦ ha (h0 a h))

include hη hp hj in

theorem exists_isUnit_appLE_eq (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    {r : ∀ a, Γ(Y, W a)}
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (hru : ∀ a, IsUnit (r a)) {T T' : Scheme.{u}} [IsIntegral T] [Nonempty T'] (e : T ⟶ X)
    (k : T' ⟶ T) [IsOpenImmersion k] (e' : T' ⟶ Y) (he : e' ≫ j = k ≫ e)
    {y : T} (hy : e y ∉ X.basicOpen t) {a₀ : ι} {A : T.Opens} (hyA : y ∈ A)
    (hA : A ≤ e ⁻¹ᵁ U a₀) {A' : T'.Opens} (hA' : A' = k ⁻¹ᵁ A) (hA'' : A' ≤ e' ⁻¹ᵁ W a₀)
    {u : Γ(T, A)} (hu : IsUnit u) (hur : k.appLE A A' hA'.le u = e'.appLE (W a₀) A' hA'' (r a₀)) :
    ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, j.appLE (U a) (W a) (hW a).le (s a) = r a := by
  obtain ⟨τ, hτ⟩ : IsUnit (j.appTop t) := by
    obtain ⟨τ', hτ'⟩ := exists_unit_eq_res t
    have htop : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ X.basicOpen t := fun y _ ↦ hj.le ⟨y, rfl⟩
    have := τ'.isUnit.map (j.appLE _ ⊤ htop).hom
    rw [hτ', appLE_res] at this
    rwa [← show j.appLE ⊤ ⊤ _ = j.appTop from j.appLE_eq_app]
  obtain ⟨r', τ', hτ', hr', -, hu', H⟩ := exists_transport hj hW r hr τ hτ
  obtain ⟨n, s, hsu, hc, hs⟩ :=
    exists_zpow_mul_isUnit hη hp hU hg τ' hτ' hr' fun a ↦ hu' a (hru a)
  simp only [H] at hs
  have hnat : ∀ z : Γ(X, U a₀), k.appLE A A' hA'.le (e.appLE _ A hA z) =
      e'.appLE (W a₀) A' hA'' (j.appLE _ _ (hW a₀).le z) := fun z ↦ by
    have h : A' ≤ (k ≫ e) ⁻¹ᵁ U a₀ := hA'.le.trans (k.preimage_mono hA)
    rw [appLE_appLE k e rfl _ _ h, appLE_appLE e' j he _ _ h]
  let φ : Γ(Y, ⊤) →+* Γ(T', A') :=
    (e'.appLE (W a₀) A' hA'').hom.comp (Y.presheaf.map (homOfLE le_top).op).hom
  obtain rfl : n = 0 := by
    refine zpow_eq_zero (k.appLE A A' hA'.le).hom (appLE_injective k hA')
      ((hsu a₀).map (e.appLE _ A hA).hom) hu
      (p := e.appLE _ A hA (X.presheaf.map (homOfLE (le_top : U a₀ ≤ ⊤)).op t)) (fun H ↦ hy ?_)
      (Units.map φ.toMonoidHom τ) ?_ ?_
    · have := T.basicOpen_of_isUnit H
      rw [Scheme.basicOpen_appLE, Scheme.basicOpen_res] at this
      exact (show y ∈ A ⊓ e ⁻¹ᵁ (U a₀ ⊓ X.basicOpen t) from this.ge hyA).2.2
    · rw [hnat, appLE_res, Units.coe_map, hτ,
        ← show j.appLE ⊤ ⊤ le_top = j.appTop from j.appLE_eq_app]
      exact congrArg (e'.appLE (W a₀) A' hA'') (res_appLE j _ _ _)
    · rw [hnat, hs, map_mul, hur, ← map_zpow, Units.coe_map]
      rfl
  exact ⟨s, hsu, hc, fun a ↦ by simpa using hs a⟩

end Immersion

theorem isIntegral_of_basicOpen {X Y : Scheme.{u}} {t : Γ(X, ⊤)}
    (ht : ∀ U : X.Opens, IsAffineOpen U →
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∈ nonZeroDivisors Γ(X, U))
    (j : Y ⟶ X) [IsOpenImmersion j] [IsIntegral Y] (hj : j.opensRange = X.basicOpen t) :
    IsIntegral X := by
  have hinj : ∀ U : X.Opens, IsAffineOpen U →
      Function.Injective (j.appLE U (j ⁻¹ᵁ U) le_rfl) := fun U hU s s' h ↦ by
    have := hU.isLocalization_basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
    refine IsLocalization.injective
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
      ((Submonoid.powers_le).2 (ht U hU)) ?_
    have he : X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) =
      U ⊓ X.basicOpen t := X.basicOpen_res _ _
    refine (appLE_bijective j (W := j ⁻¹ᵁ U) (he.le.trans (inf_le_right.trans hj.ge))
      (he ▸ eq_preimage_inf hj rfl)).1 ?_
    exact (appLE_res j _ _ s).trans (h.trans (appLE_res j _ _ s').symm)
  have : IsReduced X := ⟨fun W ↦ ⟨fun s hs ↦ X.IsSheaf.section_ext fun x hx ↦ by
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨U, hUW, hxU, hinj U hU ?_⟩
    rw [map_zero, map_zero]
    exact ((hs.map _).map _).eq_zero⟩⟩
  have hdense : Dense (Set.range j) := by
    refine dense_iff_inter_open.2 fun W hW ⟨x, hx⟩ ↦ ?_
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨W, hW⟩) hx
    by_contra hne
    have hbot : j ⁻¹ᵁ U = ⊥ := eq_bot_iff.2 fun y hy ↦ hne ⟨j y, hUW hy, y, rfl⟩
    have : Subsingleton Γ(Y, j ⁻¹ᵁ U) := by rw [hbot]; infer_instance
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    exact not_subsingleton Γ(X, U) (hinj U hU).subsingleton
  have : IrreducibleSpace X := by
    have h := (IrreducibleSpace.isIrreducible_univ Y).image j j.continuous.continuousOn
    rw [Set.image_univ] at h
    have h' := h.closure
    rw [hdense.closure_eq] at h'
    exact (irreducibleSpace_def X).2 h'
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem ker_eq_map_of_isPushout {A B C P : CommRingCat.{u}} {α : A ⟶ B} {β : A ⟶ C} {γ : B ⟶ P}
    {δ : C ⟶ P} (h : IsPushout α β γ δ) (hβ : Function.Surjective β) :
    RingHom.ker γ.hom = (RingHom.ker β.hom).map α.hom := by
  refine le_antisymm (fun z hz ↦ ?_) (Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_)
  · let J := (RingHom.ker β.hom).map α.hom
    have hJ : RingHom.ker β.hom ≤ RingHom.ker ((Ideal.Quotient.mk J).comp α.hom) := fun a ha ↦
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    let ψ : C →+* B ⧸ J := RingHom.liftOfSurjective β.hom hβ ⟨_, hJ⟩
    have w : α ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) = β ≫ CommRingCat.ofHom ψ := by
      ext a
      exact (RingHom.liftOfSurjective_comp_apply β.hom hβ ⟨_, hJ⟩ a).symm
    have := congrArg (fun φ : B ⟶ CommRingCat.of (B ⧸ J) ↦ φ z) (h.inl_desc _ _ w)
    rw [CommRingCat.comp_apply, show γ z = 0 from hz, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  · have := congrArg (fun φ : A ⟶ P ↦ φ a) h.w
    simp only [CommRingCat.comp_apply] at this
    rw [show β a = 0 from ha, map_zero] at this
    exact this

theorem ker_app_eq_span {X Z : Scheme.{u}} {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) {c : A} (hc : RingHom.ker β.hom = Ideal.span {c})
    {f : X ⟶ Spec A} {i : Z ⟶ X} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β))
    {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom = Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (f.appTop ((Scheme.ΓSpecIso A).inv c))} := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  rw [ker_eq_map_of_isPushout hpo' hβ, hc, Ideal.map_span, Set.image_singleton]
  rfl

end GlobalTheory.PrimeSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegers
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Topology

lemma exists_lt_one_lt_pow (r : ℝ≥0) (hr : r < 1) (k : ℕ) : ∃ t : ℝ≥0, t < 1 ∧ r < t ^ k := by
  have hopen : IsOpen {t : ℝ≥0 | r < t ^ k} := isOpen_lt continuous_const (continuous_pow k)
  have hmem : {t : ℝ≥0 | r < t ^ k} ∈ 𝓝 (1 : ℝ≥0) := hopen.mem_nhds (by simpa using hr)
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hmem ⟨0, zero_lt_one⟩
  obtain ⟨t, hlt, ht1⟩ := exists_between hl
  exact ⟨t, ht1, hsub ⟨hlt, ht1.le⟩⟩

lemma smul_mem_fix {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) [hN : N.Normal] (g : G) {y : L} (hy : y ∈ Fix L N) : g • y ∈ Fix L N := by
  intro n
  have hc : g⁻¹ * (n : G) * g ∈ N := by
    have := hN.conj_mem (n : G) n.2 g⁻¹
    simpa using this
  have h1 : (g⁻¹ * (n : G) * g) • y = y := hy ⟨_, hc⟩
  show (n : G) • g • y = g • y
  calc (n : G) • g • y = g • ((g⁻¹ * (n : G) * g) • y) := by
        simp only [mul_smul, smul_inv_smul]
    _ = g • y := by rw [h1]

lemma fix_smul {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) {y : L} (hy : y ∈ Fix L N) {σ : G} (hσ : σ ∈ N) : σ • y = y :=
  hy ⟨σ, hσ⟩

theorem almostSep_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal →
    N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  intro L _ v G _ _ hv N hN hfi hmov r hr
  classical
  haveI : Finite (G ⧸ N) := inferInstance
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set s : Finset (G ⧸ N) := Finset.univ.erase 1 with hs
  obtain ⟨t, ht1, hrt⟩ := exists_lt_one_lt_pow r hr s.card
  have hex : ∀ q : G ⧸ N, ∃ y : L, y ∈ Fix L N ∧ v y ≤ 1 ∧ (q ≠ 1 → t < v (q.out • y - y)) := by
    intro q
    by_cases hq : q = 1
    · exact ⟨0, zero_mem _, by simp, fun h => absurd hq h⟩
    · have hout : q.out ∉ N := by
        intro hm
        apply hq
        rw [← QuotientGroup.out_eq' q]
        exact (QuotientGroup.eq_one_iff _).2 hm
      obtain ⟨y, hyF, hyv, hyt⟩ := hmov _ hout t ht1
      exact ⟨y, hyF, hyv, fun _ => hyt⟩
  choose y hyF hyv hyt using hex
  let x : G ⧸ N → L := fun q => q.out • y q
  have hxF : ∀ q, x q ∈ Fix L N := fun q => smul_mem_fix N _ (hyF q)
  have hxv : ∀ q, v (x q) ≤ 1 := fun q => by simp only [x, hv]; exact hyv q
  obtain ⟨n, a, b, hab, hsum⟩ := GlobalTheory.T.separating_family_sum_closed_under_prod L v G (Fix L N) (G ⧸ N) s x y
    (fun j _ => ⟨hxF j, hyF j, hxv j, hyv j⟩)
  refine ⟨n, a, b, ∏ q ∈ s, (x q - y q), ?_, ?_⟩
  · refine
      { a_mem := fun i => (hab i).1
        b_mem := fun i => (hab i).2.1
        c_mem := ?_
        a_le := fun i => (hab i).2.2.1
        b_le := fun i => (hab i).2.2.2
        c_le := ?_
        sum_in := ?_
        sum_out := ?_ }
    · exact prod_mem fun q _ => sub_mem (hxF q) (hyF q)
    · rw [map_prod]
      refine Finset.prod_le_one (fun _ _ => zero_le) fun q _ => ?_
      exact (Valuation.map_sub v _ _).trans (max_le (hxv q) (hyv q))
    · intro σ hσ
      rw [hsum σ]
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [fix_smul N (hyF q) hσ]
    · intro σ hσ
      rw [hsum σ]
      have hq : (σ : G ⧸ N) ∈ s := by
        rw [hs, Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro h
        exact hσ ((QuotientGroup.eq_one_iff σ).1 h)
      refine Finset.prod_eq_zero hq ?_
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul N σ
      simp only [x]
      rw [hm, mul_smul, fix_smul N (hyF _) m.2, sub_self]
  · rw [map_prod]
    calc r < t ^ s.card := hrt
      _ = ∏ _q ∈ s, t := by rw [Finset.prod_const]
      _ ≤ ∏ q ∈ s, v (x q - y q) := by
        refine Finset.prod_le_prod (fun _ _ => zero_le) fun q hq => ?_
        exact (hyt q (Finset.ne_of_mem_erase hq)).le

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixingSubgroupOfIntermediateFieldPropertiesStatement
section
open GlobalTheory.KCoh Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixingSubgroupOfIntermediateField_properties : ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [Algebra.IsAlgebraic F Ω],
 (∀ g : Ω ≃ₐ[F] Ω, g ∈ GlobalTheory.K4.geo F K Ω ↔ ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) ∧
 (∃ e : (Ω ≃ₐ[K] Ω) ≃* GlobalTheory.K4.geo F K Ω, (∀ g x, ((e g : GlobalTheory.K4.geo F K Ω) : Ω ≃ₐ[F] Ω) x = g x) ∧ Continuous e ∧ Continuous e.symm) ∧
 (Normal F K → (GlobalTheory.K4.geo F K Ω).Normal) ∧ (IsGalois K Ω → IsCompact (GlobalTheory.K4.geo F K Ω : Set (Ω ≃ₐ[F] Ω))) ∧
 (∀ (B : ValuationSubring Ω) (r g : Ω ≃ₐ[F] Ω), GlobalTheory.NeedB.Inert B r → GlobalTheory.NeedB.Inert (B.comap (g : Ω →+* Ω)) (g⁻¹ * r * g)) := by
  first | exact @GlobalTheory.K4.geo_facts | exact GlobalTheory.K4.geo_facts | (intros; apply GlobalTheory.K4.geo_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeomIccOneLeTwoMulSub
section
open Finset ArithmeticFunction

namespace GlobalTheory

theorem geom_Icc_one_le_two_mul_sub (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (N : ℕ) :
    ∑ i ∈ Icc 1 N, r ^ i ≤ 2 * r - 2 * r ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hp : 0 ≤ r ^ (n + 1) := pow_nonneg h0 _
    have : r ^ (n + 1 + 1) = r ^ (n + 1) * r := pow_succ _ _
    nlinarith

theorem primePowerSum_le_two_mul_log_div (x : ℝ) (hx : 0 < x) (p : ℕ) (hp : p.Prime) :
    Formalism.HermitianLattices.GL2a2.sP x p ≤ 2 * x * Real.log p / p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  unfold Formalism.HermitianLattices.GL2a2.sP
  set N := ⌊x ^ (400 : ℝ)⌋₊
  have hc : 0 ≤ x * Real.log p := by positivity
  calc ∑ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N), Formalism.HermitianLattices.GL2PrimeSums.cn x (p ^ i)
      ≤ ∑ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N), x * Real.log p * (1 / (p : ℝ)) ^ i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi1 : i ≠ 0 := by
          have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hi).1).1
          omega
        unfold Formalism.HermitianLattices.GL2PrimeSums.cn
        rw [vonMangoldt_apply_pow hi1, vonMangoldt_apply_prime hp]
        calc Real.log p * min 1 (x / ((p ^ i : ℕ) : ℝ))
            ≤ Real.log p * (x / ((p ^ i : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hlog
          _ = x * Real.log p * (1 / (p : ℝ)) ^ i := by
              push_cast
              rw [one_div_pow]
              ring
    _ ≤ ∑ i ∈ Icc 1 N, x * Real.log p * (1 / (p : ℝ)) ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
    _ = x * Real.log p * ∑ i ∈ Icc 1 N, (1 / (p : ℝ)) ^ i := by rw [Finset.mul_sum]
    _ ≤ x * Real.log p * (2 * (1 / (p : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        have h := geom_Icc_one_le_two_mul_sub _ hr0 hr1 N
        have : 0 ≤ (1 / (p : ℝ)) ^ (N + 1) := pow_nonneg hr0 _
        linarith
    _ = 2 * x * Real.log p / p := by ring

theorem large_prime_sum_bound : Formalism.HermitianLattices.GL2a2.SizeSpLarge :=
  fun x hx p hp _ => primePowerSum_le_two_mul_log_div x hx p hp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesQDerivativeSubstUpperTriangular
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.CyclotomicQExpansion

theorem qD_sub (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ) (hk : 0 < a / d)
    (φ : HahnSeries ℚ Ω) :
    qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  have hcm : ∀ (c : ℚ → Ω) (ψ : HahnSeries ℚ Ω) (r : ℚ), (cm c ψ).coeff r = c r * ψ.coeff r :=
    fun _ _ _ => rfl
  have hsc : ∀ (ψ : HahnSeries ℚ Ω) (r : ℚ), (scale (a / d) ψ).coeff (a / d * r) = ψ.coeff r := by
    intro ψ r
    rw [scale, dif_pos hk]
    exact HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (a / d) hk).toOrderEmbedding) (a := r)
  rw [HahnSeries.C_mul_eq_smul]
  ext s
  obtain ⟨r, rfl⟩ : ∃ r, s = a / d * r := ⟨s / (a / d), (mul_div_cancel₀ s hk.ne').symm⟩
  rw [HahnSeries.coeff_smul]
  simp only [qD, sub]
  rw [hcm, hsc, hsc, hcm, hcm, hcm, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CyclotomicQExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M]) (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) := by
  first | exact @GlobalTheory.Sieg.EisQ.hasQ_cF_one | exact GlobalTheory.Sieg.EisQ.hasQ_cF_one | (intros; apply GlobalTheory.Sieg.EisQ.hasQ_cF_one; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorPreservesModularFormGamma1InterGamma0
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isBoundedAt_finsetSum {ι : Type*} (s : Finset ι) (c : OnePoint ℝ) (k : ℤ) {F : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, c.IsBoundedAt (F i) k) : c.IsBoundedAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uOp_modularForm : ∀ (N l q : ℕ) (k : ℤ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k,
      ⇑g = GlobalTheory.Hk.uOp q ⇑f := by
  intro N l q k hN hl hq hqd f
  have hq0 : 0 < q := hq.pos
  have hinv : ∀ γ ∈ lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ => by
    rw [SL_slash]; exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  have hU := GlobalTheory.T.heckeUOperatorExplicit_slash_invariant_gamma1InterGamma0 N l q k (⇑f) hN hl hq hqd hinv
  refine ⟨{ toFun := uOp q ⇑f
            slash_action_eq' := ?_
            holo' := (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k 1 (⇑f) hq0 f.holo').1
            bdd_at_cusps' := ?_ }, rfl⟩
  · intro γ hγ
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hγ
    have := hU s hs
    rw [SL_slash] at this
    exact this
  · intro c hc
    rw [GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq0]
    exact isBoundedAt_finsetSum _ c k fun j _ => GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level N l k _ hN hl (by
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc

end GlobalTheory.Hk
end

