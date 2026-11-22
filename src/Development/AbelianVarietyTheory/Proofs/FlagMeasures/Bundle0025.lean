import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CintTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChange
section
noncomputable section
open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt.Transport

variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma apply_out_mk_eq_of_invariant {B : AddSubgroup W} {φ : W → ℂ}
    (hφ : ∀ w b, b ∈ B → φ (w + b) = φ w) (y : W) :
    φ (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) = φ y := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) : W ⧸ B) =
      QuotientAddGroup.mk y := Quotient.out_eq _
  rw [QuotientAddGroup.eq] at h
  have := hφ (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) _ h
  rw [add_neg_cancel_left] at this
  exact this.symm

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma Fine_map_addEquiv_and_finsum_eq (e : W ≃+ W') {A B : AddSubgroup W}
    {φ : W' → ℂ} (hB : _root_.GlobalTheory.IdxInt.Fine A (fun w => φ (e w)) B) :
    _root_.GlobalTheory.IdxInt.Fine (A.map e.toAddMonoidHom) φ (B.map e.toAddMonoidHom) ∧
      (∑ᶠ c : W' ⧸ B.map e.toAddMonoidHom, φ (Quotient.out c)) =
        ∑ᶠ c : W ⧸ B, φ (e (Quotient.out c)) := by
  obtain ⟨hBA, hBi, hφ, hsupp⟩ := hB
  have hφ' : ∀ w b, b ∈ B.map e.toAddMonoidHom → φ (w + b) = φ w := by
    rintro w _ ⟨b, hb, rfl⟩
    have := hφ (e.symm w) b hb
    simpa using this
  let q : W ⧸ B ≃+ W' ⧸ B.map e.toAddMonoidHom := QuotientAddGroup.congr _ _ e rfl
  have hq : ∀ y : W, q (QuotientAddGroup.mk y) = QuotientAddGroup.mk (e y) := fun _ => rfl
  refine ⟨⟨AddSubgroup.map_mono hBA, ?_, hφ', ?_⟩, ?_⟩
  · rw [AddSubgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hBi
  · refine (hsupp.image q).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨QuotientAddGroup.mk (e.symm y), ⟨e.symm y, by simpa using hy, rfl⟩, ?_⟩
    rw [hq, AddEquiv.apply_symm_apply]
  · rw [← finsum_comp_equiv q.toEquiv]
    refine finsum_congr fun c => ?_
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    change φ (Quotient.out (q (QuotientAddGroup.mk y))) = _
    rw [hq, apply_out_mk_eq_of_invariant hφ', apply_out_mk_eq_of_invariant (φ := fun w => φ (e w)) hφ]

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma map_symm_map_addEquiv (e : W ≃+ W') (A : AddSubgroup W) :
    (A.map e.toAddMonoidHom).map e.symm.toAddMonoidHom = A := by
  ext x
  simp

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma Fine_of_le_and_finsum_eq_relIndex_mul {A B C : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex B ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ C ∧
      (∑ᶠ c : W ⧸ C, φ (Quotient.out c)) =
        (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ (Quotient.out c) := by
  obtain ⟨hBA, hBi, hφ, hsupp⟩ := hB
  haveI : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hC
  let e := AddSubgroup.quotientEquivProdOfLE hCB
  have he : ∀ y : W, (e (QuotientAddGroup.mk y)).1 = QuotientAddGroup.mk y := fun _ => rfl
  have hφC : ∀ w b, b ∈ C → φ (w + b) = φ w := fun w b hb => hφ w b (hCB hb)
  have hcomp : ∀ x : W ⧸ C, φ (Quotient.out x) = φ (Quotient.out (e x).1) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [he, apply_out_mk_eq_of_invariant hφC, apply_out_mk_eq_of_invariant hφ]
  set T : Set (W ⧸ B) := (fun w : W => (w : W ⧸ B)) '' Function.support φ with hT
  have hgT : Function.support (fun c : W ⧸ B => φ (Quotient.out c)) ⊆ T := by
    intro c hc
    refine ⟨Quotient.out c, hc, ?_⟩
    exact Quotient.out_eq c
  refine ⟨⟨hCB.trans hBA, ?_, hφC, ?_⟩, ?_⟩
  · rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA]
    exact mul_ne_zero hC hBi
  · refine ((hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
      e.injective.injOn).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, Set.mem_univ _⟩
    rw [he]
    exact ⟨y, hy, rfl⟩
  · rw [finsum_congr hcomp,
      finsum_comp_equiv e (f := fun p : (W ⧸ B) × (B ⧸ C.addSubgroupOf B) => φ (Quotient.out p.1))]
    rw [finsum_curry _ ?_]
    · haveI := Fintype.ofFinite (B ⧸ C.addSubgroupOf B)
      simp only [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_finsum]
      congr 1
      funext a
      rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
    · exact (hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).subset
        fun p hp => ⟨hgT hp, Set.mem_univ _⟩

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma finsum_out_div_relIndex_eq_inf_of_fine {A B₁ B₂ : AddSubgroup W} {φ : W → ℂ}
    (h₁ : _root_.GlobalTheory.IdxInt.Fine A φ B₁) (h₂ : _root_.GlobalTheory.IdxInt.Fine A φ B₂) :
    (∑ᶠ c : W ⧸ B₁, φ (Quotient.out c)) / (B₁.relIndex A : ℂ) =
      (∑ᶠ c : W ⧸ (B₁ ⊓ B₂), φ (Quotient.out c)) / ((B₁ ⊓ B₂).relIndex A : ℂ) := by
  have hle : B₁ ⊓ B₂ ≤ B₁ := inf_le_left
  have hprod := AddSubgroup.relIndex_mul_relIndex (B₁ ⊓ B₂) B₁ A hle h₁.1
  have hA : (B₁ ⊓ B₂).relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h₁.2.1 h₂.2.1
  have hi : (B₁ ⊓ B₂).relIndex B₁ ≠ 0 := by
    rw [← hprod] at hA
    exact left_ne_zero_of_mul hA
  rw [(Fine_of_le_and_finsum_eq_relIndex_mul h₁ hle hi).2, ← hprod, Nat.cast_mul,
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hi)]

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma cint_eq_finsum_div_relIndex_of_fine {A B : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) :
    _root_.GlobalTheory.IdxInt.cint A φ = (∑ᶠ c : W ⧸ B, φ (Quotient.out c)) / (B.relIndex A : ℂ) := by
  have hnice : _root_.GlobalTheory.IdxInt.Nice A φ := ⟨B, hB⟩
  unfold _root_.GlobalTheory.IdxInt.cint
  rw [dif_pos hnice, finsum_out_div_relIndex_eq_inf_of_fine hnice.choose_spec hB,
    finsum_out_div_relIndex_eq_inf_of_fine hB hnice.choose_spec, inf_comm]

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma Fine_inf_of_relIndex_ne_zero {A A' B : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (h₂ : A'.relIndex A ≠ 0) (h₁ : A.relIndex A' ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ (B ⊓ A') ∧ _root_.GlobalTheory.IdxInt.Fine A' φ (B ⊓ A') := by
  have hBA : B ≤ A := hB.1
  have hCA : (B ⊓ A').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 h₂
  have hi : (B ⊓ A').relIndex B ≠ 0 := by
    have h := hCA
    rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') B A inf_le_left hBA] at h
    exact left_ne_zero_of_mul h
  have hfine := (Fine_of_le_and_finsum_eq_relIndex_mul hB inf_le_left hi).1
  refine ⟨hfine, inf_le_right, ?_, hfine.2.2⟩
  have hCD : B ⊓ A' ≤ A ⊓ A' := inf_le_inf_right A' hBA
  have hD : (B ⊓ A').relIndex (A ⊓ A') ≠ 0 := by
    have h := hCA
    rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left] at h
    exact left_ne_zero_of_mul h
  rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A' hCD inf_le_right,
    AddSubgroup.inf_relIndex_right]
  exact mul_ne_zero hD h₁

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in

theorem _root_.GlobalTheory.IdxInt.Transport.cint_map_and_change : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (_root_.GlobalTheory.IdxInt.Nice (A.map e.toAddMonoidHom) φ ↔ _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w))) ∧ _root_.GlobalTheory.IdxInt.cint (A.map e.toAddMonoidHom) φ = _root_.GlobalTheory.IdxInt.cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (_root_.GlobalTheory.IdxInt.Nice A φ ↔ _root_.GlobalTheory.IdxInt.Nice A' φ) ∧ _root_.GlobalTheory.IdxInt.cint A' φ * (A.relIndex A' : ℂ) = _root_.GlobalTheory.IdxInt.cint A φ * (A'.relIndex A : ℂ) := by
  intro W _ W' _
  refine ⟨fun e A φ => ?_, fun A A' φ h₁ h₂ => ?_⟩
  · have hiff : _root_.GlobalTheory.IdxInt.Nice (A.map e.toAddMonoidHom) φ ↔
        _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w)) := by
      constructor
      · rintro ⟨B', hB'⟩
        have hB'' : _root_.GlobalTheory.IdxInt.Fine (A.map e.toAddMonoidHom)
            (fun w => (fun w => φ (e w)) (e.symm w)) B' := by simpa using hB'
        have h := (Fine_map_addEquiv_and_finsum_eq e.symm (φ := fun w => φ (e w)) hB'').1
        rw [map_symm_map_addEquiv] at h
        exact ⟨_, h⟩
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_map_addEquiv_and_finsum_eq e hB).1⟩
    refine ⟨hiff, ?_⟩
    by_cases hN : _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w))
    · obtain ⟨B, hB⟩ := hN
      rw [cint_eq_finsum_div_relIndex_of_fine hB, cint_eq_finsum_div_relIndex_of_fine (Fine_map_addEquiv_and_finsum_eq e hB).1,
        (Fine_map_addEquiv_and_finsum_eq e hB).2, AddSubgroup.relIndex_map_map_of_injective _ _ e.injective]
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dif_neg hN, dif_neg (hiff.not.mpr hN)]
  · have hiff : _root_.GlobalTheory.IdxInt.Nice A φ ↔ _root_.GlobalTheory.IdxInt.Nice A' φ := by
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_inf_of_relIndex_ne_zero hB h₂ h₁).2⟩
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_inf_of_relIndex_ne_zero hB h₁ h₂).2⟩
    refine ⟨hiff, ?_⟩
    by_cases hN : _root_.GlobalTheory.IdxInt.Nice A φ
    · obtain ⟨B, hB⟩ := hN
      have hC := Fine_inf_of_relIndex_ne_zero hB h₂ h₁
      have hCD : B ⊓ A' ≤ A ⊓ A' := inf_le_inf_right A' hB.1
      have hD : (B ⊓ A').relIndex (A ⊓ A') ≠ 0 := by
        have h := hC.1.2.1
        rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left] at h
        exact left_ne_zero_of_mul h
      rw [cint_eq_finsum_div_relIndex_of_fine hC.1, cint_eq_finsum_div_relIndex_of_fine hC.2,
        ← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A' hCD inf_le_right,
        ← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left,
        AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_left]
      have hD' : ((B ⊓ A').relIndex (A ⊓ A') : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
      have h₁' : (A.relIndex A' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h₁
      have h₂' : (A'.relIndex A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h₂
      push_cast
      field_simp
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dif_neg hN, dif_neg (hiff.not.mp hN)]
      simp

end GlobalTheory.IdxInt.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralValIntegerIff
section
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc

noncomputable def idemPairHom {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) : F × F →ₐ[F] E :=
  AlgHom.ofLinearMap
    ((LinearMap.toSpanSingleton F E p).coprod (LinearMap.toSpanSingleton F E q))
    (by simpa using h1)
    (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      simp only [Prod.mk_mul_mk, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
        Algebra.smul_def, map_mul]
      linear_combination
        (-(algebraMap F E a * algebraMap F E c * p) - algebraMap F E b * algebraMap F E d * q) * h1
        + (algebraMap F E a * algebraMap F E c + algebraMap F E b * algebraMap F E d
          - algebraMap F E a * algebraMap F E d - algebraMap F E b * algebraMap F E c) * h0)

theorem idemPairHom_apply {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) (y : F × F) :
    idemPairHom p q h1 h0 y = y.1 • p + y.2 • q := rfl

theorem LocE_isField_or_split {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) :
    IsField E ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap := by
  by_cases hE : IsField E
  · exact Or.inl hE
  right
  haveI := L.reduced
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  obtain ⟨x, hx0, hxu⟩ : ∃ x : E, x ≠ 0 ∧ ¬ IsUnit x := by
    by_contra hcon
    push Not at hcon
    exact hE ⟨exists_pair_ne E, mul_comm, fun {a} ha => (hcon a ha).exists_right_inv⟩
  obtain ⟨n, hn⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  obtain ⟨t, ht⟩ := (L.cj_fix (x + L.cj x)).1 (by rw [map_add, L.cj_cj, add_comm])
  have hn0 : n = 0 := by
    by_contra h
    apply hxu
    have : IsUnit (x * L.cj x) := hn ▸ (IsUnit.mk0 n h).map (algebraMap F E)
    exact isUnit_of_mul_isUnit_left this
  have hN : x * L.cj x = 0 := by rw [← hn, hn0, map_zero]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero] at ht
    apply hx0
    apply IsNilpotent.eq_zero
    exact ⟨2, by linear_combination (-x) * ht - hN⟩
  set p : E := t⁻¹ • x with hp
  have hq : L.cj p = t⁻¹ • L.cj x := by rw [hp, map_smul]
  have h1 : p + L.cj p = 1 := by
    rw [hq, hp, ← smul_add, ← ht, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ ht0, map_one]
  have h0 : p * L.cj p = 0 := by
    rw [hq, hp, smul_mul_smul_comm, hN, smul_zero]
  have hp0 : p ≠ 0 := smul_ne_zero (inv_ne_zero ht0) hx0
  have hq0 : L.cj p ≠ 0 := by simpa using hp0
  have hpp : p * p = p := by linear_combination p * h1 - h0
  have hqq : L.cj p * L.cj p = L.cj p := by linear_combination L.cj p * h1 - h0
  clear_value p
  let φ : F × F →ₐ[F] E := idemPairHom p (L.cj p) h1 h0
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    change a • p + b • L.cj p = 0 at hab
    have ha : a • p = 0 := by
      have := congrArg (p * ·) hab
      simpa [mul_add, hpp, h0] using this
    have hb : b • L.cj p = 0 := by rwa [ha, zero_add] at hab
    have ha' : a = 0 := (smul_eq_zero.1 ha).resolve_right hp0
    have hb' : b = 0 := (smul_eq_zero.1 hb).resolve_right hq0
    simp [ha', hb']
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (by rw [L.rank]; simp)).1 hinj
  refine ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm, fun z => ?_⟩
  obtain ⟨y, rfl⟩ := (AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).surjective z
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_eq]
  change L.cj (y.1 • p + y.2 • L.cj p) = y.2 • p + y.1 • L.cj p
  rw [map_add, map_smul, map_smul, L.cj_cj, add_comm]

theorem isIntegral_valInteger_iff {F : Type} [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] :=
  ⟨fun h => (Valuation.integer.integers (valuation F)).mem_of_integral h,
    fun h => isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := ⟨a, h⟩)⟩

theorem isField_or_split : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → IsField E ∨ ∃ e : E ≃ₐ[F] F × F, (∀ x, e (M.L.cj x) = (e x).swap) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x, x ∈ M.L.O ↔ ((e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) := by
  intro F _ _ _ E _ _ _ _ M hM
  rcases LocE_isField_or_split M.L with h | ⟨e, he⟩
  · exact Or.inl h
  haveI := hM.loc
  haveI := M.L.top
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  refine Or.inr ⟨e, he, ?_, ?_, fun x => ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  · exact IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  · rw [M.L.O_def, ← isIntegral_algEquiv (e.restrictScalars 𝒪[F]), ← isIntegral_valInteger_iff,
      ← isIntegral_valInteger_iff, ← IsIntegral.pair_iff]
    rfl

end GlobalTheory.SgLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend
section
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc.PtAlg

variable {E : Type} [CommRing E]

theorem ptEntryL_append (bs : List (Eˣ × ℕ+)) (t : Eˣ) (s : ℕ+) :
    ∀ (m : ℕ), (bs.map (fun b => (b.2 : ℕ))).sum = m → ∀ a b : ℕ,
      ptEntryL (bs ++ [(t, s)]) a b =
        if a < m ∧ b < m then ptEntryL bs a b
        else if m ≤ a ∧ m ≤ b ∧ a + b + 1 = 2 * m + s then (t : E) else 0 := by
  induction bs with
  | nil =>
    intro m hm a b
    simp only [List.map_nil, List.sum_nil] at hm
    subst hm
    simp only [List.nil_append, ptEntryL]
    split_ifs <;> first | rfl | omega
  | cons hd bs ih =>
    obtain ⟨t', s'⟩ := hd
    intro m hm a b
    simp only [List.map_cons, List.sum_cons] at hm
    simp only [List.cons_append, ptEntryL]
    rw [ih _ rfl]
    split_ifs <;> first | rfl | omega

theorem mat_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) (a b : Fin (m + s)) :
    (h.snoc t s).mat a b =
      if hab : (a : ℕ) < m ∧ (b : ℕ) < m then h.mat ⟨a, hab.1⟩ ⟨b, hab.2⟩
      else if m ≤ (a : ℕ) ∧ m ≤ (b : ℕ) ∧ (a : ℕ) + b + 1 = 2 * m + s then (t : E) else 0 := by
  show ptEntryL (h.blocks ++ [(t, s)]) a b = _
  rw [ptEntryL_append h.blocks t s m h.size]
  split_ifs <;> rfl

theorem det_snoc_eq {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det =
      h.mat.det * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : E) ^ (s : ℕ)) := by
  have key : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (h.snoc t s).mat =
      Matrix.fromBlocks h.mat 0 0
        ((t : E) • (Fin.revPerm : Equiv.Perm (Fin s)).permMatrix E) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, mat_snoc,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] <;>
      have hi := i.isLt <;> have hj := j.isLt
    · rw [dif_pos ⟨hi, hj⟩]
    · rw [dif_neg (by omega), if_neg (by omega)]
    · rw [dif_neg (by omega), if_neg (by omega)]
    · rw [dif_neg (by omega)]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
      by_cases hij : Fin.rev i = j
      · rw [if_pos (by rw [← hij, Fin.val_rev]; omega), if_pos hij, mul_one]
      · rw [if_neg (fun hc => hij (Fin.ext (by rw [Fin.val_rev]; omega))), if_neg hij, mul_zero]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
    Matrix.det_permutation, Fintype.card_fin] at hdet
  rw [hdet]
  ring

theorem det_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det = h.mat.det * (t : E) ^ (s : ℕ) ∨
      (h.snoc t s).mat.det = -(h.mat.det * (t : E) ^ (s : ℕ)) := by
  rw [det_snoc_eq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h1 | h1
  · left
    rw [h1]
    simp
  · right
    rw [h1]
    simp

private theorem isUnit_det_of_mem_UH_Hpk (bs : List (Eˣ × ℕ+)) :
    ∀ (n : ℕ) (hn : (bs.map (fun b => (b.2 : ℕ))).sum = n),
      IsUnit (Pt.mat (⟨bs, hn⟩ : Pt E n)).det := by
  induction bs using List.reverseRecOn with
  | nil =>
    intro n hn
    have hn' : n = 0 := by rw [← hn]; simp
    subst hn'
    simp
  | append_singleton bs x ih =>
    obtain ⟨t, s⟩ := x
    intro n hn
    have hn' : n = (bs.map (fun b => (b.2 : ℕ))).sum + s := by rw [← hn]; simp
    subst hn'
    have hu := ih _ rfl
    change IsUnit (Pt.snoc (⟨bs, rfl⟩ : Pt E _) t s).mat.det
    rcases det_snoc (⟨bs, rfl⟩ : Pt E _) t s with h1 | h1
    · rw [h1]
      exact hu.mul ((Units.isUnit t).pow _)
    · rw [h1]
      exact (hu.mul ((Units.isUnit t).pow _)).neg

theorem isUnit_det {m : ℕ} (h : Pt E m) : IsUnit h.mat.det := by
  exact isUnit_det_of_mem_UH_Hpk h.blocks m h.size

end GlobalTheory.SgLoc.PtAlg

namespace GlobalTheory.SgLoc

end GlobalTheory.SgLoc
end

