import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherianIdealIntegralOrSplit
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Dich

open TopologicalSpace Scheme.IdealSheafData

theorem isReduced_subscheme_of_radical_eq {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : J.radical = J) : IsReduced J.subscheme := by
  have : ∀ U, IsReduced (J.subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ J.ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    have e : (J.ideal U).radical = J.ideal U := congr($(h).ideal U)
    exact Ideal.radical_eq_iff.mp e
  exact IsReduced.of_openCover _ J.subschemeCover.openCover

theorem irreducibleSpace_subscheme {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : IsIrreducible (J.support : Set X)) : IrreducibleSpace J.subscheme := by
  have hr : Set.range J.subschemeι = (J.support : Set X) := J.range_subschemeι
  have hirr : IsIrreducible (Set.range J.subschemeι) := hr ▸ h
  have : IrreducibleSpace (Set.range J.subschemeι) :=
    { toPreirreducibleSpace := Subtype.preirreducibleSpace hirr.2
      toNonempty := hirr.1.to_subtype }
  exact J.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this

theorem exists_radical_pow_le {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData) :
    ∃ k : ℕ, J.radical ^ k ≤ J := by
  have hU : ∀ U : X.affineOpens, ∃ k : ℕ, (J.ideal U).radical ^ k ≤ J.ideal U := fun U => by
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    exact Ideal.exists_radical_pow_le_of_fg _ (IsNoetherian.noetherian _)
  choose k hk using hU
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.2) (fun x _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.sup k, le_of_iSup_eq_top (fun i : t => i.1) ?_ fun i => ?_⟩
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  · change (J.ideal i.1).radical ^ t.sup k ≤ J.ideal i.1
    exact (Ideal.pow_le_pow_right (Finset.le_sup i.2)).trans (hk i.1)

theorem exists_of_radical_ne {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData)
    (hJ : J ≠ ⊤) (hr : J.radical ≠ J) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  classical
  have hex := exists_radical_pow_le J
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, J.radical ^ (m + 1) ≤ J ∧ ¬ J.radical ^ m ≤ J := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk | hk
    · have hs := Nat.find_spec hex
      rw [hk, pow_zero] at hs
      exact absurd (top_le_iff.mp hs) hJ
    · refine ⟨Nat.find hex - 1, ?_, Nat.find_min hex (by omega)⟩
      rw [Nat.sub_add_cancel hk]
      exact Nat.find_spec hex
  refine ⟨J.radical, J ⊔ J.radical ^ m, lt_of_le_of_ne J.le_radical hr.symm,
    left_lt_sup.mpr hm₂, fun U a b ha hb => ?_⟩
  have hle : J.radical.ideal U * (J ⊔ J.radical ^ m).ideal U ≤ J.ideal U := by
    change J.radical.ideal U * (J.ideal U ⊔ (J.radical.ideal U) ^ m) ≤ J.ideal U
    rw [Ideal.mul_sup]
    refine sup_le Ideal.mul_le_right ?_
    rw [← pow_succ']
    exact hm₁ U
  exact hle (Ideal.mul_mem_mul ha hb)

theorem exists_of_not_preirreducible {X : Scheme.{0}} (J : X.IdealSheafData)
    (hr : J.radical = J) (hirr : ¬ IsPreirreducible (J.support : Set X)) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
  push_neg at hirr
  obtain ⟨Z₁, Z₂, h₁, h₂, hcov, hn₁, hn₂⟩ := hirr
  let C₁ : Closeds X := J.support ⊓ ⟨Z₁, h₁⟩
  let C₂ : Closeds X := J.support ⊓ ⟨Z₂, h₂⟩
  have hsup : C₁ ⊔ C₂ = J.support := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    rcases hcov hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hlt : ∀ (C : Closeds X) (Z : Set X), C ≤ J.support → (C : Set X) ⊆ Z →
      ¬ (J.support : Set X) ⊆ Z → J < vanishingIdeal C := by
    intro C Z hC hCZ hn
    refine lt_of_le_not_ge (le_support_iff_le_vanishingIdeal.mp hC) fun hle => hn ?_
    intro x hx
    have hx' : x ∈ ((vanishingIdeal C).support : Set X) := support_antitone hle hx
    rw [coe_support_vanishingIdeal] at hx'
    exact hCZ hx'
  refine ⟨vanishingIdeal C₁, vanishingIdeal C₂, hlt C₁ Z₁ inf_le_left (fun x hx => hx.2) hn₁,
    hlt C₂ Z₂ inf_le_left (fun x hx => hx.2) hn₂, fun U a b ha hb => ?_⟩
  have e : vanishingIdeal C₁ ⊓ vanishingIdeal C₂ = J := by
    rw [← vanishingIdeal_sup, hsup, vanishingIdeal_support, hr]
  have hm : a * b ∈ (vanishingIdeal C₁ ⊓ vanishingIdeal C₂).ideal U :=
    ⟨Ideal.mul_mem_right _ _ ha, Ideal.mul_mem_left _ _ hb⟩
  rwa [e] at hm

theorem isIntegral_or_exists_mul_mem : ∀ {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData),
    J ≠ ⊤ → IsIntegral J.subscheme ∨ ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧
      ∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U →
        a * b ∈ J.ideal U := by
  intro X _ J hJ
  by_cases hr : J.radical = J
  · by_cases hirr : IsPreirreducible (J.support : Set X)
    · left
      have hne : (J.support : Set X).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro h
        exact hJ (J.support_eq_bot_iff.mp (SetLike.coe_injective h))
      haveI := isReduced_subscheme_of_radical_eq J hr
      haveI := irreducibleSpace_subscheme J ⟨hne, hirr⟩
      exact isIntegral_of_irreducibleSpace_of_isReduced _
    · exact Or.inr (exists_of_not_preirreducible J hr hirr)
  · exact Or.inr (exists_of_radical_ne J hJ hr)

end GlobalTheory.CompanionTheory.GE.Dich
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperInfIdealSheaves
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Union

theorem support_inf_subset {X : Scheme.{0}} (T₁ T₂ : X.IdealSheafData) :
    ((T₁ ⊓ T₂).support : Set X) ⊆ (T₁.support : Set X) ∪ T₂.support := by
  have hle : T₁ * T₂ ≤ T₁ ⊓ T₂ := fun U => Ideal.mul_le_inf
  have h := Scheme.IdealSheafData.support_antitone hle
  intro x hx
  have hx' : x ∈ (T₁ * T₂).support := h hx
  rw [Scheme.IdealSheafData.support_mul] at hx'
  exact hx'

theorem universallyClosed_of_cover {Z₁ Z₂ Z S : Scheme.{0}} (p₁ : Z₁ ⟶ Z) (p₂ : Z₂ ⟶ Z)
    (h : Z ⟶ S) (h₁ : UniversallyClosed (p₁ ≫ h)) (h₂ : UniversallyClosed (p₂ ≫ h))
    (hc : ∀ z : Z, z ∈ Set.range p₁ ∨ z ∈ Set.range p₂) : UniversallyClosed h := by
  rw [universallyClosed_iff]
  intro X' Y' i₁ i₂ f' H
  have key : ∀ {W : Scheme.{0}} (p : W ⟶ Z), UniversallyClosed (p ≫ h) →
      IsClosedMap (pullback.fst i₁ p ≫ f') := by
    intro W p hp
    have H' : IsPullback (pullback.fst i₁ p ≫ f') (pullback.snd i₁ p) i₂ (p ≫ h) :=
      (IsPullback.of_hasPullback i₁ p).paste_horiz H
    exact (universallyClosed_iff _).mp hp _ _ _ H'
  have lift : ∀ {W : Scheme.{0}} (p : W ⟶ Z) (x : X'), i₁ x ∈ Set.range p →
      ∃ z : ↑(pullback i₁ p), pullback.fst i₁ p z = x := by
    rintro W p x ⟨w, hw⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
    exact ⟨z, hz⟩
  show IsClosedMap f'
  intro C hC
  have hEq : f' '' C = (pullback.fst i₁ p₁ ≫ f') '' (pullback.fst i₁ p₁ ⁻¹' C) ∪
      (pullback.fst i₁ p₂ ≫ f') '' (pullback.fst i₁ p₂ ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hc (i₁ x) with hr | hr
      · obtain ⟨z, hz⟩ := lift p₁ x hr
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz⟩ := lift p₂ x hr
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨_, hz, by simp⟩
      · exact ⟨_, hz, by simp⟩
  rw [hEq]
  exact (key p₁ h₁ _ (hC.preimage (pullback.fst i₁ p₁).continuous)).union
    (key p₂ h₂ _ (hC.preimage (pullback.fst i₁ p₂).continuous))

theorem isProper_inf : ∀ {X S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    (T₁ T₂ : X.IdealSheafData), IsProper (T₁.subschemeι ≫ f) → IsProper (T₂.subschemeι ≫ f) →
    IsProper ((T₁ ⊓ T₂).subschemeι ≫ f) := by
  intro X S f _ _ T₁ T₂ hT₁ hT₂
  let K : X.IdealSheafData := T₁ ⊓ T₂
  let p₁ : T₁.subscheme ⟶ K.subscheme := IsClosedImmersion.lift K.subschemeι T₁.subschemeι
    (by simpa [K] using (inf_le_left : T₁ ⊓ T₂ ≤ T₁))
  let p₂ : T₂.subscheme ⟶ K.subscheme := IsClosedImmersion.lift K.subschemeι T₂.subschemeι
    (by simpa [K] using (inf_le_right : T₁ ⊓ T₂ ≤ T₂))
  have e₁ : p₁ ≫ K.subschemeι = T₁.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have e₂ : p₂ ≫ K.subschemeι = T₂.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have u₁ : UniversallyClosed (p₁ ≫ K.subschemeι ≫ f) := by
    rw [← Category.assoc, e₁]; infer_instance
  have u₂ : UniversallyClosed (p₂ ≫ K.subschemeι ≫ f) := by
    rw [← Category.assoc, e₂]; infer_instance
  have cover : ∀ {T : X.IdealSheafData} (p : T.subscheme ⟶ K.subscheme),
      p ≫ K.subschemeι = T.subschemeι → ∀ z : K.subscheme, K.subschemeι z ∈ (T.support : Set X) →
      z ∈ Set.range p := by
    intro T p e z hz
    obtain ⟨w, hw⟩ := T.range_subschemeι.ge hz
    refine ⟨w, K.subschemeι.isEmbedding.injective ?_⟩
    rw [← hw, ← e]
    rfl
  have hc : ∀ z : K.subscheme, z ∈ Set.range p₁ ∨ z ∈ Set.range p₂ := by
    intro z
    have hz : K.subschemeι z ∈ (K.support : Set X) := K.range_subschemeι.le ⟨z, rfl⟩
    rcases support_inf_subset T₁ T₂ hz with h | h
    · exact Or.inl (cover p₁ e₁ z h)
    · exact Or.inr (cover p₂ e₂ z h)
  have : UniversallyClosed (K.subschemeι ≫ f) :=
    universallyClosed_of_cover p₁ p₂ _ u₁ u₂ hc
  exact ⟨⟩

end GlobalTheory.CompanionTheory.GE.Union
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.SupSecs

variable {X : Scheme.{0}} {E : X.Modules}

def sumMap (S T : Subobject E) : (S : X.Modules) ⊞ (T : X.Modules) ⟶ E :=
  biprod.desc S.arrow T.arrow

theorem sup_eq_imageSubobject (S T : Subobject E) : S ⊔ T = imageSubobject (sumMap S T) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact Subobject.le_of_comm (biprod.inl ≫ factorThruImageSubobject (sumMap S T))
        (by rw [Category.assoc, imageSubobject_arrow_comp, sumMap, biprod.inl_desc])
    · exact Subobject.le_of_comm (biprod.inr ≫ factorThruImageSubobject (sumMap S T))
        (by rw [Category.assoc, imageSubobject_arrow_comp, sumMap, biprod.inr_desc])
  · refine imageSubobject_le (sumMap S T)
      (biprod.desc (Subobject.ofLE S (S ⊔ T) le_sup_left)
        (Subobject.ofLE T (S ⊔ T) le_sup_right)) ?_
    apply biprod.hom_ext' <;> simp [sumMap]

theorem sumMap_app (S T : Subobject E) (V : X.Opens)
    (x : Γ((S : X.Modules) ⊞ (T : X.Modules), V)) :
    (sumMap S T).app V x =
      S.arrow.app V ((biprod.fst : (S : X.Modules) ⊞ (T : X.Modules) ⟶ _).app V x) +
        T.arrow.app V ((biprod.snd : (S : X.Modules) ⊞ (T : X.Modules) ⟶ _).app V x) := by
  have h : sumMap S T = biprod.fst ≫ S.arrow + biprod.snd ≫ T.arrow := by
    apply biprod.hom_ext' <;> simp [sumMap, Preadditive.comp_add]
  rw [h]
  rfl

theorem sumMap_app_add (S T : Subobject E) (V : X.Opens) (s : Γ((S : X.Modules), V))
    (t : Γ((T : X.Modules), V)) :
    (sumMap S T).app V
        ((biprod.inl : _ ⟶ (S : X.Modules) ⊞ (T : X.Modules)).app V s +
          (biprod.inr : _ ⟶ (S : X.Modules) ⊞ (T : X.Modules)).app V t) =
      S.arrow.app V s + T.arrow.app V t := by
  have hs : biprod.inl ≫ sumMap S T = S.arrow := by simp [sumMap]
  have ht : biprod.inr ≫ sumMap S T = T.arrow := by simp [sumMap]
  rw [map_add, GlobalTheory.QCoh.app_app, GlobalTheory.QCoh.app_app, hs, ht]

end GlobalTheory.CompanionTheory.GE.SupSecs

namespace GlobalTheory.CompanionTheory.GE

open SupSecs in

theorem supsecs {X : Scheme.{0}} {E : X.Modules} (hE : E.IsQuasicoherent) (S T : Subobject E)
    (hS : (S : X.Modules).IsQuasicoherent) (hT : (T : X.Modules).IsQuasicoherent) :
    ((S ⊔ T : Subobject E) : X.Modules).IsQuasicoherent ∧
      ∀ V : X.Opens, IsAffineOpen V →
        secs (S ⊔ T) V = {x | ∃ s ∈ secs S V, ∃ t ∈ secs T V, x = s + t} := by
  rw [sup_eq_imageSubobject]
  refine ⟨GlobalTheory.QCoh.isQuasicoherent_of_iso (imageSubobjectIso (sumMap S T)).symm, fun V hV ↦ ?_⟩
  have hr : secs (imageSubobject (sumMap S T)) V = Set.range ((sumMap S T).app V) := by
    have harrow : (imageSubobject (sumMap S T)).arrow =
        (imageSubobjectIso (sumMap S T)).hom ≫ image.ι (sumMap S T) :=
      (imageSubobject_arrow (sumMap S T)).symm
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := GlobalTheory.QCoh.surjective_factorThruImage_app (sumMap S T) hV
        ((imageSubobjectIso (sumMap S T)).hom.app V a)
      refine ⟨b, ?_⟩
      rw [harrow, ← GlobalTheory.QCoh.app_app, ← hb, GlobalTheory.QCoh.app_app, image.fac]
    · rintro ⟨b, rfl⟩
      refine ⟨(factorThruImageSubobject (sumMap S T)).app V b, ?_⟩
      rw [GlobalTheory.QCoh.app_app, imageSubobject_arrow_comp]
  rw [hr]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, sumMap_app S T V y⟩
  · rintro ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, sumMap_app_add S T V s t⟩

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientFiltrationBijectiveOfCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.QuoK

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem toSq_bijective_of_bot (a₀ b : IdF A) (h0 : ∀ T, a₀.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (j : ℕ) :
    Function.Bijective ((toSq a₀ b h0).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij (toSq a₀ b h0).hom (fun n => ⟨fun f f' h => ?_, fun y => ?_⟩) j
  · funext s
    have h1 := congrArg Subtype.val (congrFun h s)
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hb] at h2
    exact sub_eq_zero.1 h2
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a₀ b _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

end Abstract

section Concrete
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem ks_le_of_le {u s : ℕ} (hus : u ≤ s) (𝒱 : Set X.Opens) : KS q u 𝒱 ≤ KS q s 𝒱 := by
  rintro T ⟨⟨h1, h2⟩, hV⟩
  exact ⟨⟨le_bot_iff.1 (h1 ▸ T.pdPow_anti hus), h2⟩, hV⟩

theorem quoK_comm {u s : ℕ} (hus : u ≤ s) (𝒱 : Set X.Opens) (r : ℤ) (j : ℕ) (x : HdR q j) :
    ((incl (ks_le_of_le q hus 𝒱)).sq (incl_fil _ 0) (incl_fil _ r)).pull j (quoK q (KS q s 𝒱) r j x) =
      quoK q (KS q u 𝒱) r j x := by
  obtain ⟨z, hz, hx⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx (CH.modF (thA (smFun X q)))) j).1 x
  subst hx
  rfl

theorem quoK_bij_self {u : ℕ} (𝒱 : Set X.Opens) (j : ℕ) (h : Function.Bijective (resK q (KS q u 𝒱) j)) :
    Function.Bijective (quoK q (KS q u 𝒱) (u : ℤ) j) := by
  have hB := toSq_bijective_of_bot (sFil (KS q u 𝒱) 0) (sFil (KS q u 𝒱) (u : ℤ)) (fun T => T.obj.pdPow_zero)
    (fun T => by
      have h := T.property.1.1
      change T.obj.pdPow ((u : ℤ).toNat) = ⊥
      rw [Int.toNat_natCast]
      exact h) j
  exact hB.comp h

end Concrete

theorem quoK_bijective : KH.KIso → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (U : Cov q) (s u : ℕ), (∀ α, U.d α < u) → u ≤ s → ∀ (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ (j : ℕ),
    Function.Bijective (quoK q (KS q s 𝒱) (u : ℤ) j) := by
  intro hK K _ _ X q U s u hd hus 𝒱 h𝒱 j
  have h1 := quoK_bij_self q 𝒱 j (hK q U u hd 𝒱 h𝒱 j).1
  have h2 := GlobalTheory.T.filtered_cohomology_restriction_bijective (TF 1 s) 1 u (Or.inr ⟨s, hus, rfl⟩) 𝒱 (ks_le_of_le q hus 𝒱) 0 (u : ℤ) le_rfl j
  refine (Function.Bijective.of_comp_iff' h2 _).1 ?_
  have e : (((incl (ks_le_of_le q hus 𝒱)).sq (incl_fil _ 0) (incl_fil _ (u : ℤ))).pull j) ∘ (quoK q (KS q s 𝒱) (u : ℤ) j) =
      quoK q (KS q u 𝒱) (u : ℤ) j := funext (quoK_comm q hus 𝒱 (u : ℤ) j)
  exact (congrArg Function.Bijective e).mpr h1

end GlobalTheory.CompanionTheory.QuoK
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenPeriodFiniteExtension
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

open GroundTheory.PAdicHodge GroundTheory.PAdicHodge.EigenChar

theorem cycloChar_inertia_image_infinite : ∀ {l : ℕ} [Fact l.Prime],
    (∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x) →
    ∀ (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥L],
      ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite := by
  intro l _ h L _
  let H : Subgroup Gal(Om l/↥L) :=
    { carrier := {σ | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}
      mul_mem' := by
        intro a b ha hb w hw
        show a (b w) = w
        rw [hb w hw, ha w hw]
      one_mem' := by
        intro w _
        rfl
      inv_mem' := by
        intro a ha w hw
        have haw : a w = w := ha w hw
        calc a⁻¹ w = a⁻¹ (a w) := by rw [haw]
          _ = w := by simp [AlgEquiv.aut_inv] }
  intro hfin
  obtain ⟨M, hM⟩ : ∃ M : Subgroup ℤ_[l]ˣ, M = H.map (GroundTheory.PAdicHodge.cycloChar L) := ⟨_, rfl⟩
  have hMfin : Finite M := by
    have hs : (M : Set ℤ_[l]ˣ).Finite := by
      rw [hM, Subgroup.coe_map]
      exact hfin
    exact hs.to_subtype
  obtain ⟨n, hnM⟩ : ∃ n : ℕ, n = Nat.card M := ⟨_, rfl⟩
  have hn : 0 < n := by
    rw [hnM]
    exact Nat.card_pos
  have hpow : ∀ σ ∈ H, (GroundTheory.PAdicHodge.cycloChar L σ) ^ n = 1 := by
    intro σ hσ
    have hmem : GroundTheory.PAdicHodge.cycloChar L σ ∈ M := by
      rw [hM]
      exact Subgroup.mem_map_of_mem _ hσ
    have h1 : (⟨GroundTheory.PAdicHodge.cycloChar L σ, hmem⟩ : M) ^ n = 1 := by
      rw [hnM]
      exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hroots : ∀ σ : Gal(Om l/↥L), GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → σ ∈ H := by
    intro σ hσ
    have hfix := (GroundTheory.LocalField.unramifiedDegree_eq_one_iff σ).mp hσ
    have hS : ∀ y ∈ GroundTheory.PAdicHodge.primeToPRoots l, σ y = y := by
      rintro y ⟨m, hm0, hmcop, hym⟩
      apply hfix
      have hcop : Nat.Coprime l m := Nat.Coprime.symm hmcop
      have hmod : l ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
      have hle : 1 ≤ l ^ Nat.totient m := Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)
      have hdvd : m ∣ l ^ Nat.totient m - 1 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      obtain ⟨c, hc⟩ := hdvd
      refine GroundTheory.PAdicHodge.EigenWitt.mem_unramifiedRoots_of_pow_eq_one (L := L)
        (Nat.totient_pos.2 hm0) ?_
      rw [hc, pow_mul, hym, one_pow]
    have hσ' : (σ.restrictScalars ℚ_[l]) ∈
        (IntermediateField.adjoin ℚ_[l] (GroundTheory.PAdicHodge.primeToPRoots l)).fixingSubgroup :=
      GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff.mpr (fun y hy => hS y hy)
    show ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w
    intro w hw
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ' w hw
  let ψ : Gal(Om l/↥L) →* ℤ_[l]ˣ := (powMonoidHom n).comp (GroundTheory.PAdicHodge.cycloChar L)
  have hψc : Continuous ψ := (GroundTheory.PAdicHodge.continuous_cycloChar L).pow n
  have hψu : ∀ σ, GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → ψ σ = 1 := by
    intro σ hσ
    exact hpow σ (hroots σ hσ)
  obtain ⟨f, hf, x, hx0, hx⟩ := h L ψ hψc hψu
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = -((n * f : ℕ) : ℤ) := ⟨_, rfl⟩
  have hj0 : j ≠ 0 := by
    rw [hj, neg_ne_zero, Nat.cast_ne_zero]
    exact Nat.mul_ne_zero hn.ne' hf.ne'
  have hinv : x ∈ (GroundTheory.PAdicHodge.cpTwistRep L j).invariants := by
    change ∀ σ, (GroundTheory.PAdicHodge.cpTwistRep L j σ) x = x
    intro σ
    have key : (((GroundTheory.PAdicHodge.cycloChar L σ ^ j : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) *
        ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) ^ f = 1 := by
      have hψσ : ψ σ = GroundTheory.PAdicHodge.cycloChar L σ ^ n := rfl
      have hu : GroundTheory.PAdicHodge.cycloChar L σ ^ j * (GroundTheory.PAdicHodge.cycloChar L σ ^ n) ^ f = 1 := by
        rw [hj, ← pow_mul, zpow_neg, zpow_natCast, inv_mul_cancel]
      rw [hψσ, ← PadicInt.coe_pow, ← PadicInt.coe_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hu]
      simp
    rw [GroundTheory.PAdicHodge.cpTwistRep_apply, hx σ, GroundTheory.PAdicHodge.twistScalar, ← mul_assoc, ← map_mul, key,
      map_one, one_mul]
  rw [GroundTheory.PAdicHodge.cpTwistRep_invariants_eq_bot L hj0] at hinv
  exact hx0 ((Submodule.mem_bot _).mp hinv)

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

theorem secs_pullback_arrow {X : Scheme.{0}} {E : X.Modules} (D S : Subobject E) (V : X.Opens) :
    secs ((Subobject.pullback D.arrow).obj S) V = (D.arrow.app V) ⁻¹' secs S V := by
  let G : X.Modules ⥤ Type :=
    Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (Opposite.op V) ⋙ forget Ab
  haveI : PreservesLimitsOfSize.{0, 0} ((evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab).obj
      (Opposite.op V)) := ⟨fun {J} _ => evaluation_preservesLimitsOfShape _⟩
  haveI : PreservesLimitsOfShape WalkingCospan (Scheme.Modules.toPresheaf X) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan (forget Ab.{0}) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan G := inferInstance
  have hp := (Subobject.isPullback D.arrow S).map G
  ext d
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨(Subobject.pullbackπ D.arrow S).app V p, ?_⟩
    exact congr($(hp.w) p)
  · rintro ⟨s, hs⟩
    obtain ⟨p, h₁, h₂⟩ := Types.exists_of_isPullback hp s d hs
    exact ⟨p, h₂⟩

end GlobalTheory.CompanionTheory.GE
end
end

