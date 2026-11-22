import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHyperbolicPairTransitive
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace HyperbolicPairTransitive

omit [NumberField E] in

theorem sesq_swap (h : HermitianForm F E W) (x y : W) :
    h.toSesq y x = conj F E (h.toSesq x y) :=
  (h.isSymm.eq x y).symm

omit [NumberField E] in

theorem exists_unitary_of_preserves (h : HermitianForm F E W) [FiniteDimensional E W]
    (f : W →ₗ[E] W) (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) :
    ∃ g : h.unitaryGroup, ∀ z, (g : W ≃ₗ[E] W) z = f z := by
  have inj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun z hz => h.nonsingular.1 ?_
    ext y
    rw [← hf, hz, map_zero]
    rfl
  exact ⟨⟨LinearEquiv.ofInjectiveEndo f inj, fun x y => hf x y⟩, fun _ => rfl⟩

theorem exists_unitary_sub_smul (h : HermitianForm F E W) [FiniteDimensional E W] (u : W) (β : E)
    (hβ : β ≠ 0) (hs : β + conj F E β = h.toSesq u u) :
    ∃ g : h.unitaryGroup, ∀ z, (g : W ≃ₗ[E] W) z = z - (h.toSesq u z / β) • u := by
  have hβ' : conj F E β ≠ 0 := by
    intro h0; apply hβ; rw [← conj_conj (F := F) β, h0, map_zero]
  obtain ⟨g, hg⟩ := exists_unitary_of_preserves h
    (LinearMap.id - β⁻¹ • (h.toSesq u).smulRight u) (fun x y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
        LinearMap.smulRight_apply, smul_smul, map_sub, LinearMap.map_smulₛₗ, map_smul,
        LinearMap.smul_apply, smul_eq_mul, conjHom_apply, map_mul, map_inv₀]
      rw [sesq_swap h x u, sesq_swap h u u, ← hs, map_add, conj_conj]
      field_simp
      simp only [conj_conj]
      ring)
  exact ⟨g, fun z => by
    rw [hg]
    simp [smul_smul, div_eq_inv_mul]⟩

theorem exists_unitary_carry (h : HermitianForm F E W) [FiniteDimensional E W] (x y c : W)
    (hxy : h.toSesq x x = h.toSesq y y) (hx : h.toSesq x x ≠ 0)
    (hxc : h.toSesq x c = 0) (hyc : h.toSesq y c = 0) :
    ∃ g : h.unitaryGroup, (g : W ≃ₗ[E] W) x = y ∧ (g : W ≃ₗ[E] W) c = c := by
  have hr : ∀ z, conj F E (h.toSesq z z) = h.toSesq z z := fun z => h.isSymm.eq z z
  have two : (2 : E) ≠ 0 := two_ne_zero
  by_cases hβ : h.toSesq (x - y) x = 0
  ·
    have hyx : h.toSesq y x = h.toSesq x x := by
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hβ
      exact hβ.symm
    obtain ⟨g₁, hg₁⟩ := exists_unitary_sub_smul h (x + y) (2 * h.toSesq x x)
      (mul_ne_zero two hx) (by
        simp only [map_add, LinearMap.add_apply, map_mul, map_ofNat, hr]
        rw [sesq_swap h y x, hyx, hr, ← hxy]; ring)
    obtain ⟨g₂, hg₂⟩ := exists_unitary_sub_smul h y (h.toSesq y y / 2)
      (div_ne_zero (hxy ▸ hx) two) (by rw [map_div₀, map_ofNat, hr]; ring)
    refine ⟨g₂ * g₁, ?_, ?_⟩
    · change (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) x) = y
      have e1 : (g₁ : W ≃ₗ[E] W) x = -y := by
        rw [hg₁, map_add, LinearMap.add_apply, hyx, ← two_mul, div_self (mul_ne_zero two hx),
          one_smul]
        abel
      have hy : h.toSesq y y ≠ 0 := hxy ▸ hx
      rw [e1, hg₂, map_neg, neg_div, neg_smul, sub_neg_eq_add,
        show h.toSesq y y / (h.toSesq y y / 2) = 2 by field_simp, two_smul]
      abel
    · change (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) c) = c
      rw [hg₁, map_add, LinearMap.add_apply, hxc, hyc, add_zero, zero_div, zero_smul, sub_zero,
        hg₂, hyc, zero_div, zero_smul, sub_zero]
  · obtain ⟨g, hg⟩ := exists_unitary_sub_smul h (x - y) (h.toSesq (x - y) x) hβ (by
      simp only [map_sub, LinearMap.sub_apply, hr]
      rw [sesq_swap h x y, hxy, conj_conj]; ring)
    refine ⟨g, ?_, ?_⟩
    · rw [hg, div_self hβ, one_smul, sub_sub_cancel]
    · rw [hg, map_sub, LinearMap.sub_apply, hxc, hyc, sub_zero, zero_div, zero_smul, sub_zero]

theorem proof (h : HermitianForm F E W) [FiniteDimensional E W] :
    HyperbolicPairTransitive.Statement h := by
  intro v w v' w' ⟨hv, hw, hvw⟩ ⟨hv', hw', hvw'⟩
  have hwv : h.toSesq w v = 1 := by rw [sesq_swap h v w, hvw, map_one]
  have hwv' : h.toSesq w' v' = 1 := by rw [sesq_swap h v' w', hvw', map_one]
  have ee : ∀ a b : W, h.toSesq a a = 0 → h.toSesq b b = 0 → h.toSesq a b = 1 →
      h.toSesq b a = 1 → h.toSesq (a + b) (a + b) = 2 ∧ h.toSesq (a - b) (a - b) = -2 ∧
        h.toSesq (a - b) (a + b) = 0 := by
    intro a b ha hb hab hba
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, ha, hb, hab, hba]
    norm_num
  obtain ⟨e1, f1, fe1⟩ := ee v w hv hw hvw hwv
  obtain ⟨e2, f2, fe2⟩ := ee v' w' hv' hw' hvw' hwv'
  have two : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨g₁, hg₁, -⟩ := exists_unitary_carry h (v + w) (v' + w') 0 (e1.trans e2.symm)
    (e1 ▸ two) (map_zero _) (map_zero _)
  have hf : h.toSesq ((g₁ : W ≃ₗ[E] W) (v - w)) (v' + w') = 0 := by
    rw [← hg₁, g₁.2, fe1]
  obtain ⟨g₂, hg₂, hc⟩ := exists_unitary_carry h ((g₁ : W ≃ₗ[E] W) (v - w)) (v' - w') (v' + w')
    (by rw [g₁.2, f1, f2]) (by rw [g₁.2, f1]; exact neg_ne_zero.2 two) hf fe2
  have key : ∀ z, (g₂ * g₁ : h.unitaryGroup) • z = (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) z) :=
    fun _ => rfl
  have hE : (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) (v + w)) = v' + w' := by rw [hg₁, hc]
  have hv2 : v = (2 : E)⁻¹ • ((v + w) + (v - w)) := by
    rw [add_add_sub_cancel, ← two_smul E v, smul_smul, inv_mul_cancel₀ two, one_smul]
  have hw2 : w = (2 : E)⁻¹ • ((v + w) - (v - w)) := by
    rw [add_sub_sub_cancel, ← two_smul E w, smul_smul, inv_mul_cancel₀ two, one_smul]
  refine ⟨g₂ * g₁, ?_, ?_⟩
  · rw [key, hv2, map_smul, map_smul, map_add, map_add, hE, hg₂, add_add_sub_cancel,
      ← two_smul E v', smul_smul, inv_mul_cancel₀ two, one_smul]
  · rw [key, hw2, map_smul, map_smul, map_sub, map_sub, hE, hg₂, add_sub_sub_cancel,
      ← two_smul E w', smul_smul, inv_mul_cancel₀ two, one_smul]

end HyperbolicPairTransitive

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLinePairOrbitsFinite
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

universe u

section Sandwich

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem fg_map_of_fg {H : AddSubgroup A} (hH : H.FG) (φ : A →+ B) : (H.map φ).FG := by
  rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hH ⊢
  obtain ⟨k, f, rfl⟩ := hH
  exact ⟨k, φ.comp f, by rw [AddMonoidHom.range_comp]⟩

theorem fg_of_le_fg {H K : AddSubgroup A} (hHK : H ≤ K) (hK : K.FG) : H.FG := by
  have hK' : K.toIntSubmodule.FG := (Submodule.fg_iff_addSubgroup_fg _).2 hK
  have := isNoetherian_of_fg_of_noetherian _ hK'
  exact (Submodule.fg_iff_addSubgroup_fg H.toIntSubmodule).1
    (Submodule.FG.of_le_of_isNoetherian (S := H.toIntSubmodule) (T := K.toIntSubmodule) hHK)

variable [NoZeroSMulDivisors ℕ A]

theorem finite_sandwich (M : AddSubgroup A) {n : ℕ} (hn : 0 < n) :
    {L : AddSubgroup A | M ≤ L ∧ (∀ x ∈ L, n • x ∈ M) ∧ L.FG}.Finite := by
  rcases Set.eq_empty_or_nonempty {L : AddSubgroup A | M ≤ L ∧ (∀ x ∈ L, n • x ∈ M) ∧ L.FG}
    with he | ⟨L₀, hML₀, -, hL₀⟩
  · rw [he]
    exact Set.finite_empty
  have hM : M.FG := fg_of_le_fg hML₀ hL₀
  let f : A →+ A := nsmulAddMonoidHom n
  have hf : Function.Injective f := fun x y hxy => by
    have hxy' : n • x = n • y := hxy
    exact smul_right_injective A hn.ne' hxy'

  let N : AddSubgroup A := M.comap f
  have hNM : (N.map f) ≤ M := AddSubgroup.map_comap_le _ _
  have hN : N.FG := by
    have h1 : (N.map f).FG := fg_of_le_fg hNM hM
    have h2 : N.toIntSubmodule.FG := by
      refine Submodule.fg_of_fg_map_injective f.toIntLinearMap hf ?_
      have : (N.toIntSubmodule.map f.toIntLinearMap) = (N.map f).toIntSubmodule := by
        ext x
        simp
      rw [this]
      exact (Submodule.fg_iff_addSubgroup_fg _).2 h1
    exact (Submodule.fg_iff_addSubgroup_fg _).1 h2
  have hMN : M ≤ N := fun x hx => M.nsmul_mem hx n
  let M' : AddSubgroup N := M.addSubgroupOf N
  have : AddGroup.FG N := (AddGroup.fg_iff_addSubgroup_fg N).2 hN
  have : AddGroup.FG (N ⧸ M') :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective M')
  have : Finite (N ⧸ M') := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective M' q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact x.2

  let q : AddSubgroup A → Set (N ⧸ M') := fun L =>
    QuotientAddGroup.mk' M' '' {y : N | (y : A) ∈ L}
  refine Set.Finite.of_finite_image (f := q) (Set.toFinite _) ?_
  rintro L ⟨hML, hLn, -⟩ L' ⟨hML', hL'n, -⟩ hq
  have key : ∀ L L' : AddSubgroup A, M ≤ L' → (∀ x ∈ L, n • x ∈ M) → q L ⊆ q L' → L ≤ L' := by
    intro L L' hML' hLn hsub x hx
    have hxN : x ∈ N := hLn x hx
    obtain ⟨y, hy, hyx⟩ := hsub ⟨⟨x, hxN⟩, hx, rfl⟩
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq] at hyx
    have hd : -(y : A) + x ∈ M := by
      have := AddSubgroup.mem_addSubgroupOf.1 hyx
      simpa using this
    have : x = y + (-(y : A) + x) := by abel
    rw [this]
    exact L'.add_mem hy (hML' hd)
  exact le_antisymm (key L L' hML' hLn hq.le) (key L' L hML hL'n hq.ge)

end Sandwich

section Pairs

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W]

theorem LinePairOrbitsFinite.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (h₂ : WittPartner.Statement h)
    (h₃ : ComplementForm.Statement h) (h₄ : ComplementExtension.Statement h)
    (h₅ : AdaptedReduction.Statement h) : LinePairOrbitsFinite.Statement h := by
  intro D
  by_cases hex : ∃ v₀ : W, v₀ ≠ 0 ∧ h.toSesq v₀ v₀ = 0
  swap
  · refine ⟨∅, Set.finite_empty, fun La l _ hl => ?_⟩
    exfalso
    have hne : l ≠ ⊥ := fun hb => by
      have := hl.1
      rw [hb, finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨x, hxl, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact hex ⟨x, hx0, hl.2 x hxl x hxl⟩
  obtain ⟨v₀, hv₀, hv₀₀⟩ := hex
  obtain ⟨w₀, hvw, hww⟩ := h₂ v₀ hv₀ hv₀₀
  have hp : IsHyperbolicPair h v₀ w₀ := ⟨hv₀₀, hww, hvw⟩
  obtain ⟨h', hh'⟩ := h₃ v₀ w₀ hp
  obtain ⟨KK, hKK, n, D', hn, hred⟩ := h₅ v₀ w₀ hp h' hh' D
  have hdim : finrank E (hypComplement h v₀ w₀) < finrank E W := by
    refine Submodule.finrank_lt fun htop => ?_
    have hv : v₀ ∈ hypComplement h v₀ w₀ := htop ▸ Submodule.mem_top
    have h1 : h.toSesq w₀ v₀ = 1 := by
      rw [← h.isSymm.eq v₀ w₀, hvw, map_one]
    exact one_ne_zero (h1 ▸ (mem_hypComplement.1 hv).2)
  obtain ⟨S', hS', hS'L⟩ := h₁ (hypComplement h v₀ w₀) h' hdim D'
  have : NoZeroSMulDivisors ℕ W := ⟨fun {c x} hcx => by
    rw [← Nat.cast_smul_eq_nsmul E] at hcx
    rcases smul_eq_zero.1 hcx with h0 | h0
    · exact Or.inl (Nat.cast_eq_zero.1 h0)
    · exact Or.inr h0⟩
  let Mof : AddSubgroup E × AddSubgroup E → AddSubgroup (hypComplement h v₀ w₀) →
      AddSubgroup W := fun p L =>
    p.1.map ((smulAddHom E W).flip v₀) ⊔ L.map (hypComplement h v₀ w₀).subtype.toAddMonoidHom ⊔
      p.2.map ((smulAddHom E W).flip w₀)
  refine ⟨(⋃ p ∈ KK, ⋃ L ∈ S', {La | Mof p L ≤ La ∧ (∀ x ∈ La, n • x ∈ Mof p L) ∧ La.FG}) ×ˢ
    {Submodule.span E {v₀}},
    (hKK.biUnion fun p _ => hS'.biUnion fun L _ => finite_sandwich _ hn).prod
      (Set.finite_singleton _), ?_⟩
  intro La l hLa hl
  obtain ⟨g, La₁, hgLa, hgv, hK, hsplit, hInt⟩ := hred La l hLa hl
  obtain ⟨L, hL, m, hmL⟩ := hS'L _ hInt
  obtain ⟨gm, hgv₀, hgw₀, hgx⟩ := h₄ v₀ w₀ hp h' hh' m

  have hsmul : ∀ (γ : h.unitaryGroup) (c : E) (x : W), γ • (c • x) = c • (γ • x) := fun γ c x =>
    map_smul (γ : W ≃ₗ[E] W) c x
  have hmem : ∀ x : W, x ∈ gm⁻¹ • La₁ ↔ gm • x ∈ La₁ := fun x => by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
      simpa using hy
    · intro hx
      have := AddSubgroup.smul_mem_pointwise_smul _ gm⁻¹ La₁ hx
      rw [inv_smul_smul] at this
      exact this
  refine ⟨(gm⁻¹ • La₁, Submodule.span E {v₀}), ⟨?_, rfl⟩, g * gm, ?_, ?_⟩
  · refine Set.mem_iUnion₂.2 ⟨_, hK, Set.mem_iUnion₂.2 ⟨L, hL, ?_, ?_, ?_⟩⟩
    · refine sup_le (sup_le ?_ ?_) ?_
      · rintro _ ⟨a, ha, rfl⟩
        rw [hmem]
        change gm • (a • v₀) ∈ La₁
        rw [hsmul, hgv₀]
        exact ha
      · rintro _ ⟨y, hy, rfl⟩
        rw [hmem]
        change gm • (y : W) ∈ La₁
        rw [hgx]
        have : m • y ∈ m • L := AddSubgroup.smul_mem_pointwise_smul y m L hy
        rw [hmL] at this
        exact this
      · rintro _ ⟨b, hb, rfl⟩
        rw [hmem]
        change gm • (b • w₀) ∈ La₁
        rw [hsmul, hgw₀]
        exact hb
    · intro x hx
      rw [hmem] at hx
      obtain ⟨a, ha, b, hb, hz⟩ := hsplit _ hx
      set z : W := n • (gm • x) - a • v₀ - b • w₀ with hzdef
      have hzL : z ∈ La₁ :=
        La₁.sub_mem (La₁.sub_mem (La₁.nsmul_mem hx n) ha) hb
      have hz' : (⟨z, hz⟩ : hypComplement h v₀ w₀) ∈ m • L := by
        rw [hmL]
        exact hzL
      obtain ⟨y, hy, hyz⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hz'
      have hnx : n • x = a • v₀ + (y : W) + b • w₀ := by
        apply (MulAction.injective gm)
        show gm • (n • x) = gm • (a • v₀ + (y : W) + b • w₀)
        have e1 : gm • (n • x) = n • (gm • x) := map_nsmul (gm : W ≃ₗ[E] W) n x
        have e2 : gm • (y : W) = z := by
          rw [hgx, hyz]
        rw [e1, smul_add, smul_add, hsmul, hsmul, hgv₀, hgw₀, e2, hzdef]
        abel
      rw [hnx]
      refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) ?_
      · exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_left ⟨a, ha, rfl⟩)
      · exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_right ⟨y, hy, rfl⟩)
      · exact AddSubgroup.mem_sup_right ⟨b, hb, rfl⟩
    · have hLa₁ : La₁ = g⁻¹ • La := by
        rw [← hgLa, inv_smul_smul]
      have hfg : ∀ (γ : h.unitaryGroup) (S : AddSubgroup W), S.FG → (γ • S).FG := by
        intro γ S hS
        have : γ • S = S.map (((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom) := by
          ext x
          constructor
          · intro hx
            obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
            exact ⟨y, hy, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            exact AddSubgroup.smul_mem_pointwise_smul y γ S hy
        rw [this]
        exact fg_map_of_fg hS _
      exact hfg _ _ (hLa₁ ▸ hfg _ _ hLa.isLattice.fg)
  · rw [mul_smul, smul_inv_smul, hgLa]
  · have hgv0 : (g : W ≃ₗ[E] W) v₀ ≠ 0 := fun h0 =>
      hv₀ ((g : W ≃ₗ[E] W).map_eq_zero_iff.1 h0)
    have hg' : ((g * gm : h.unitaryGroup) : W ≃ₗ[E] W) v₀ = (g : W ≃ₗ[E] W) v₀ := by
      change (g : W ≃ₗ[E] W) ((gm : W ≃ₗ[E] W) v₀) = _
      exact congrArg _ hgv₀
    change (Submodule.span E {v₀}).map _ = l
    rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span E {((g * gm : h.unitaryGroup) : W ≃ₗ[E] W) v₀} = l
    rw [hg']
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hgv
    · rw [finrank_span_singleton hgv0, hl.1]

end Pairs

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantStabCompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace MajorantStabCompact

theorem form_mulVec {ι : Type*} [Fintype ι] {P A : Matrix ι ι ℂ}
    (hA : (A.map (starRingEnd ℂ))ᵀ * P * A = P) (y : ι → ℂ) :
    star (A *ᵥ y) ⬝ᵥ (P *ᵥ (A *ᵥ y)) = star y ⬝ᵥ (P *ᵥ y) := by
  have hc : (A.map (starRingEnd ℂ))ᵀ = Aᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hc] at hA
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

end MajorantStabCompact

open MajorantStabCompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem MajorantStabCompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantStabCompact.Statement h v := by
  intro M
  set e : Fin (Fintype.card ι) → W := v ∘ (Fintype.equivFin ι).symm
  have he : Submodule.span E (Set.range e) = ⊤ := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, v.span_eq]
  set C : ℝ := ∑ a, M.len (vecAt v (e a))
  have hcpt := BoundedInverseCompact.proof h v M _ e he C

  have hclosed : IsClosed (M.stab : Set (archUnitary h v)) := by
    have : (M.stab : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v |
        ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map (starRingEnd ℂ))ᵀ * M.P w *
          (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) = M.P w} := by
      ext g
      simp [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi, mem_unitaryGroupMatrix]
    rw [this]
    refine isClosed_iInter fun w => isClosed_eq ?_ continuous_const
    have hg : Continuous fun g : archUnitary h v =>
        (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) :=
      Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
    exact ((hg.matrix_map Complex.continuous_conj).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hg
  refine hcpt.of_isClosed_subset hclosed ?_
  intro g hg a

  have hgi : (g⁻¹ : archUnitary h v) ∈ M.stab := inv_mem hg
  have hw : ∀ w, (((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map
      (starRingEnd ℂ))ᵀ * M.P w * ((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ)) = M.P w := by
    intro w
    have := (Subgroup.mem_pi _).mp (Subgroup.mem_subgroupOf.mp hgi) w (Set.mem_univ w)
    exact mem_unitaryGroupMatrix.mp this
  have heq : M.len (invApply g (vecAt v (e a))) = M.len (vecAt v (e a)) := by
    simp only [Majorant.len, invApply]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by rw [form_mulVec (hw w)]
  rw [heq]
  exact Finset.single_le_sum (f := fun a => M.len (vecAt v (e a)))
    (fun b _ => Real.sqrt_nonneg _) (Finset.mem_univ a)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementArchCocompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def ComplementArchCocompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (La : AddSubgroup W) (x₀ w₀ : W) (m : ℕ), IsLattice E La → IsHyperbolicPair h x₀ w₀ → 0 < m →
    ∃ K : Set (InfinitePlace E → ι → ℂ), IsCompact K ∧ ∀ Y : InfinitePlace E → ι → ℂ,
      (∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 ∧
        star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0) →
      ∃ y ∈ hypComplement h x₀ w₀, (∃ z ∈ La, y = m • z) ∧ Y - vecAt v y ∈ K

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StImaginaryLatticeCocompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable (F E : Type*) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

def ImaginaryLatticeCocompact.Statement : Prop :=
  ∀ m : ℕ, 0 < m → ∃ R : ℝ, ∀ s : InfinitePlace E → ℝ, ∃ a : 𝓞 E,
    (m : E) * a + conj F E ((m : E) * a) = 0 ∧ ∀ w, |(w.embedding ((m : E) * a)).im - s w| ≤ R

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

