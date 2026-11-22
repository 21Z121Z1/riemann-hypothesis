import Mathlib
import GroundTheory.LocalFields.BrauerInductionCharacters
import GroundTheory.LocalFields.Bundle0002
import GroundTheory.LocalFields.BrauerInductionClifford
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.UnitsPowers

-- bundled from GroundTheory.LocalFields.BrauerInductionMonomial
section
noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section Nilpotent

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_normal_commute_of_not_commute {M : Type*} [Monoid M] [Group.IsNilpotent G] (ρ : G →* M)
    (h : ∃ a b, ρ a * ρ b ≠ ρ b * ρ a) :
    ∃ A : Subgroup G, A.Normal ∧ (∀ a ∈ A, ∀ b ∈ A, ρ a * ρ b = ρ b * ρ a) ∧
      ∃ a ∈ A, ∃ g, ρ g * ρ a ≠ ρ a * ρ g := by
  let ρ' := ρ.toHomUnits
  let cent : Set G → Subgroup G := fun s ↦ (Subgroup.centralizer (ρ' '' s)).comap ρ'
  have hcent : ∀ (s : Set G) (x : G), x ∈ cent s ↔ ∀ y ∈ s, ρ y * ρ x = ρ x * ρ y := by
    intro s x
    simp only [cent, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.forall_mem_image,
      Units.ext_iff, Units.val_mul, ρ', MonoidHom.coe_toHomUnits]

  let S := cent Set.univ
  have hS : ∀ x, x ∈ S ↔ ∀ y, ρ y * ρ x = ρ x * ρ y := fun x ↦ by
    simp [S, hcent]
  obtain ⟨z, hz2, hz1⟩ : ∃ z, (∀ y, ⁅z, y⁆ ∈ S) ∧ z ∉ S := by
    by_contra hcon
    push Not at hcon
    have hle : ∀ n, Subgroup.upperCentralSeries G n ≤ S := by
      intro n
      induction n with
      | zero =>
        intro x hx
        rw [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] at hx
        rw [hx]
        exact S.one_mem
      | succ n ih =>
        intro x hx
        exact hcon x fun y ↦ ih (Subgroup.mem_upperCentralSeries_succ_iff.mp hx y)
    obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent G
    obtain ⟨a, b, hab⟩ := h
    exact hab ((hS b).mp (hle n (hn ▸ Subgroup.mem_top b)) a)
  have hzmem : z ∈ insert z (S : Set G) := Set.mem_insert z _
  have hSmem : ∀ x ∈ S, x ∈ insert z (S : Set G) := fun x hx ↦ Set.mem_insert_of_mem z hx
  refine ⟨Subgroup.closure (insert z (S : Set G)), ⟨fun n hn g ↦ ?_⟩, fun a ha b hb ↦ ?_, ?_⟩
  ·
    have hle : Subgroup.closure (insert z (S : Set G)) ≤
        (Subgroup.closure (insert z (S : Set G))).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases hx with rfl | hx
      · rw [show g * x * g⁻¹ = ⁅x, g⁆⁻¹ * x by rw [commutatorElement_inv, commutatorElement_def]; group]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (hSmem _ (hz2 g))))
          (Subgroup.subset_closure hzmem)
      · apply Subgroup.subset_closure
        apply hSmem
        rw [hS]
        intro y
        have hx' : ρ (g * x * g⁻¹) = ρ x := by
          rw [map_mul, map_mul, (hS x).mp hx g, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
        rw [hx']
        exact (hS x).mp hx y
    exact hle hn
  ·
    have h1 : ∀ y ∈ insert z (S : Set G), Subgroup.closure (insert z (S : Set G)) ≤ cent {y} := by
      intro y hy
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, hcent]
      intro y' hy'
      rw [Set.mem_singleton_iff.mp hy']
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · rfl
        · exact ((hS y).mp hy x).symm
      · exact (hS x).mp hx y
    have h2 : Subgroup.closure (insert z (S : Set G)) ≤ cent {a} := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, hcent]
      intro a' ha'
      rw [Set.mem_singleton_iff.mp ha']
      exact ((hcent {y} a).mp (h1 y hy ha) y rfl).symm
    exact ((hcent {a} b).mp (h2 hb) a rfl)
  · refine ⟨z, Subgroup.subset_closure hzmem, ?_⟩
    rw [hS] at hz1
    push Not at hz1
    exact hz1

end Nilpotent

section Scalar

variable {G : Type*} [Group G] {A : Subgroup G} [A.Normal] [Fintype A]

theorem apply_eq_smul_of_forall_conj {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [hρ : ρ.IsIrreducible] (l : A →* ℂˣ)
    (h : charInner A (ρ.character ∘ A.subtype) (fun a ↦ (l a : ℂ)) ≠ 0)
    (hl : ∀ (g : G) (a : A), l (conjNormal A g a) = l a) (a : A) (v : V) :
    ρ a v = (l a : ℂ) • v := by
  have hrank : finrank ℂ (IntertwiningMap (linRep l) (ρ.comp A.subtype)) ≠ 0 := by
    rw [← Nat.cast_ne_zero (R := ℂ), ← charInner_character_character, character_linRep]
    exact h
  have : Nontrivial (IntertwiningMap (linRep l) (ρ.comp A.subtype)) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hrank)
  obtain ⟨F, hF⟩ := exists_ne (0 : IntertwiningMap (linRep l) (ρ.comp A.subtype))
  let W : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {w | ∀ a : A, ρ a w = (l a : ℂ) • w}
          add_mem' := fun {w w'} hw hw' a ↦ by rw [map_add, hw a, hw' a, smul_add]
          zero_mem' := fun a ↦ by rw [map_zero, smul_zero]
          smul_mem' := fun c w hw a ↦ by rw [map_smul, hw a, smul_comm] }
      apply_mem_toSubmodule := fun g w hw a ↦ by
        have hag : (a : G) * g = g * (conjNormal A g a : G) := by simp [mul_assoc]
        change ρ a (ρ g w) = (l a : ℂ) • ρ g w
        rw [← Module.End.mul_apply, ← map_mul, hag, map_mul, Module.End.mul_apply]
        rw [show ρ (conjNormal A g a : G) w = (l (conjNormal A g a) : ℂ) • w from hw _, hl, map_smul] }
  have hF1 : F 1 ∈ W.toSubmodule := fun a ↦ by
    have := IntertwiningMap.isIntertwining _ _ F a 1
    rw [linRep_apply, mul_one,
      show ((l a : ℂˣ) : ℂ) = (l a : ℂ) • (1 : ℂ) by rw [smul_eq_mul, mul_one], map_smul] at this
    exact this.symm
  have hW : W = ⊤ := by
    refine (hρ.eq_bot_or_eq_top W).resolve_left fun hb ↦ hF ?_
    have h0 : F 1 = 0 := by
      have := hF1
      rw [hb] at this
      exact this
    apply IntertwiningMap.ext
    apply LinearMap.ext_ring
    rw [IntertwiningMap.toLinearMap_apply, h0]
    rfl
  have hv : v ∈ W.toSubmodule := by
    rw [hW]
    exact Submodule.mem_top
  exact hv a

end Scalar

section Monomial

universe u

open Classical in

theorem exists_eq_indFun_of_isNilpotent_of_card (n : ℕ) :
    ∀ (G : Type u) [Group G] [Fintype G] [Group.IsNilpotent G], Nat.card G = n →
      ∀ {χ : G → ℂ}, IsIrrCharacter χ →
        ∃ (K : Subgroup G) (l : K →* ℂˣ), χ = indFun K.subtype (fun k ↦ (l k : ℂ)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ _ hn χ hχ
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hχ

  by_cases hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a
  · obtain ⟨l, hl⟩ := exists_hom_of_isIrreducible_of_commute ρ hc
    exact ⟨⊤, l.comp (⊤ : Subgroup G).subtype, by rw [hl, indFun_top_hom]⟩
  push Not at hc
  obtain ⟨A, hAn, hAc, a₀, ha₀, g₀, hg₀⟩ := exists_normal_commute_of_not_commute ρ hc

  have hχA : IsCharacter (ρ.character ∘ A.subtype) := (isCharacter_character ρ).comp _
  have hne0 : ρ.character ∘ A.subtype ≠ 0 := fun h0 ↦
    (isIrrCharacter_character ρ).one_ne_zero (by simpa using congrFun h0 1)
  obtain ⟨φ, hφ, hφne⟩ : ∃ φ ∈ irrChars A, charInner A (ρ.character ∘ A.subtype) φ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne0 (eq_zero_of_isClassFun_of_charInner hχA.isClassFun hcon)
  obtain ⟨W, _, _, _, σ, hσ, rfl⟩ := mem_irrChars.mp hφ

  have hrank : finrank ℂ (IntertwiningMap σ (ρ.comp A.subtype)) ≠ 0 := by
    rw [← Nat.cast_ne_zero (R := ℂ), ← charInner_character_character]
    exact hφne
  have : Nontrivial (IntertwiningMap σ (ρ.comp A.subtype)) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hrank)
  obtain ⟨F, hF⟩ := exists_ne (0 : IntertwiningMap σ (ρ.comp A.subtype))
  have hFinj : Function.Injective F := (IsIrreducible.injective_or_eq_zero F).resolve_right hF
  have hσc : ∀ a b : A, σ a * σ b = σ b * σ a := by
    intro a b
    apply LinearMap.ext
    intro w
    apply hFinj
    change F (σ a (σ b w)) = F (σ b (σ a w))
    rw [IntertwiningMap.isIntertwining _ _ F, IntertwiningMap.isIntertwining _ _ F,
      IntertwiningMap.isIntertwining _ _ F, IntertwiningMap.isIntertwining _ _ F]
    change (ρ a * ρ b) (F w) = (ρ b * ρ a) (F w)
    rw [hAc a a.2 b b.2]
  obtain ⟨l, hl⟩ := exists_hom_of_isIrreducible_of_commute σ hσc
  rw [hl] at hφne
  by_cases hT : inertia A (fun a ↦ (l a : ℂ)) = ⊤
  ·
    exfalso
    have hlinv : ∀ (g : G) (a : A), l (conjNormal A g a) = l a := by
      intro g a
      have hg : g ∈ inertia A (fun a ↦ (l a : ℂ)) := hT ▸ Subgroup.mem_top g
      exact Units.ext (hg a)
    apply hg₀
    apply LinearMap.ext
    intro v
    change ρ g₀ (ρ ((⟨a₀, ha₀⟩ : A) : G) v) = ρ ((⟨a₀, ha₀⟩ : A) : G) (ρ g₀ v)
    rw [apply_eq_smul_of_forall_conj ρ l hφne hlinv, apply_eq_smul_of_forall_conj ρ l hφne hlinv,
      map_smul]
  ·
    obtain ⟨ψ, hψ, hχψ⟩ :=
      (isIrrCharacter_character ρ).exists_eq_indFun_inertia (isIrrCharacter_hom l) hφne
    set T := inertia A (fun a ↦ (l a : ℂ))
    have hlt : Nat.card T < n := hn ▸ lt_of_le_of_ne (Subgroup.card_le_card_group T)
      fun h ↦ hT ((Subgroup.card_eq_iff_eq_top T).mp h)
    obtain ⟨K, l', hK⟩ := ih (Nat.card T) hlt T rfl hψ
    refine ⟨K.map T.subtype,
      l'.comp (K.equivMapOfInjective T.subtype T.subtype_injective).symm.toMonoidHom, ?_⟩
    rw [hχψ, hK, indFun_subtype_indFun_subtype]
    rfl

open Classical in

theorem IsIrrCharacter.exists_eq_indFun_of_isNilpotent {G : Type*} [Group G] [Fintype G]
    [Group.IsNilpotent G] {χ : G → ℂ} (h : IsIrrCharacter χ) :
    ∃ (K : Subgroup G) (l : K →* ℂˣ), χ = indFun K.subtype (fun k ↦ (l k : ℂ)) :=
  exists_eq_indFun_of_isNilpotent_of_card _ G rfl h

end Monomial

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.UnramifiedDefs
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

class IsUnramified (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : Prop where

  ramificationIndex_eq_one : ramificationIndex K L = 1

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

theorem isUnramified_iff : IsUnramified K L ↔ ramificationIndex K L = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnramified_iff_residueDegree_eq_finrank :
    IsUnramified K L ↔ residueDegree K L = Module.finrank K L := by
  rw [isUnramified_iff, ← ramificationIndex_mul_residueDegree K L]
  have h := residueDegree_pos K L
  constructor
  · intro h1
    rw [h1, one_mul]
  · intro h1
    have : ramificationIndex K L * residueDegree K L = 1 * residueDegree K L := by
      rw [one_mul]
      exact h1.symm
    exact Nat.eq_of_mul_eq_mul_right h this

theorem isUnramified_iff_finrank_residueField :
    IsUnramified K L ↔ Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  rw [isUnramified_iff_residueDegree_eq_finrank, residueDegree_eq_finrank]

theorem IsUnramified.residueDegree_eq_finrank [IsUnramified K L] :
    residueDegree K L = Module.finrank K L :=
  (isUnramified_iff_residueDegree_eq_finrank K L).1 inferInstance

theorem IsUnramified.finrank_residueField [IsUnramified K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
  (isUnramified_iff_finrank_residueField K L).1 inferInstance

end Topological

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional L M]

theorem isUnramified_tower_iff :
    IsUnramified K M ↔ IsUnramified K L ∧ IsUnramified L M := by
  simp only [isUnramified_iff, ramificationIndex_tower K L M, mul_eq_one]

theorem IsUnramified.trans [IsUnramified K L] [IsUnramified L M] : IsUnramified K M :=
  (isUnramified_tower_iff K L M).2 ⟨inferInstance, inferInstance⟩

theorem IsUnramified.of_tower_left [IsUnramified K M] : IsUnramified K L :=
  ((isUnramified_tower_iff K L M).1 inferInstance).1

theorem IsUnramified.of_tower_right [IsUnramified K M] : IsUnramified L M :=
  ((isUnramified_tower_iff K L M).1 inferInstance).2

end Tower

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.UnramifiedRootsOfUnity
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

section RootsOfUnity

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem exists_pow_eq_one_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {a : 𝓀[L]} (ha : a ^ m = 1) :
    ∃ x : 𝒪[L], x ^ m = 1 ∧ IsLocalRing.residue 𝒪[L] x = a := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hmon : (X ^ m - C (1 : 𝒪[L])).Monic := monic_X_pow_sub_C 1 hm0
  have hev : (X ^ m - C (1 : 𝒪[L])).eval a₀ ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp [ha]
  have hder : IsUnit (Ideal.Quotient.mk 𝓂[L] ((X ^ m - C (1 : 𝒪[L])).derivative.eval a₀)) := by
    have ha0 : IsLocalRing.residue 𝒪[L] a₀ ≠ 0 := by
      rintro h
      rw [h, zero_pow hm0] at ha
      exact zero_ne_one ha
    change IsUnit (IsLocalRing.residue 𝒪[L] _)
    rw [isUnit_iff_ne_zero]
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_pow,
      eval_X, eval_natCast, map_mul, map_pow, map_natCast]
    exact mul_ne_zero hm (pow_ne_zero _ ha0)
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian _ hmon a₀ hev hder
  refine ⟨x, ?_, ?_⟩
  · simpa [sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hxa

theorem eq_of_pow_eq_one_of_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {x y : 𝒪[L]}
    (hx : x ^ m = 1) (hy : y ^ m = 1)
    (h : IsLocalRing.residue 𝒪[L] x = IsLocalRing.residue 𝒪[L] y) : x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hxu : IsUnit x := (isUnit_pow_iff hm0).mp (hx ▸ isUnit_one)
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ m - C 1)
    (by simp [hx]) (by simp [hy]) ?_ ?_
  · rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, h, sub_self]
  · simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
      eval_pow, eval_X]
    refine IsUnit.mul ?_ (hxu.pow _)
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simpa using hm

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in

theorem mem_integer_of_pow_eq_one {m : ℕ} (hm : m ≠ 0) {x : L} (hx : x ^ m = 1) : x ∈ 𝒪[L] := by
  rw [Valuation.mem_integer_iff]
  have h : valuation L x ^ m = 1 := by rw [← map_pow, hx, map_one]
  refine le_of_not_gt fun h1 ↦ ?_
  have := one_lt_pow₀ h1 hm
  rw [h] at this
  exact this.false

theorem exists_isPrimitiveRoot_card_residueField_sub_one :
    ∃ ζ : 𝒪[L], IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := 𝓀[L]ˣ)
  have hpg : IsPrimitiveRoot (g : 𝓀[L]) (Nat.card 𝓀[L] - 1) := by
    rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  obtain ⟨x, hx, hxg⟩ :=
    exists_pow_eq_one_residue_eq (natCast_card_residueField_sub_one_ne_zero L) hpg.pow_eq_one
  refine ⟨x, hx, fun l hl ↦ hpg.dvd_of_pow_eq_one l ?_⟩
  rw [← hxg, ← map_pow, hl, map_one]

end RootsOfUnity

section Degree

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natDegree_minpoly_residue_le (x : 𝒪[L]) :
    (minpoly 𝓀[K] (IsLocalRing.residue 𝒪[L] x)).natDegree ≤ (minpoly K (x : L)).natDegree := by
  have hx : IsIntegral 𝒪[K] (x : L) := (isIntegral_iff K L x).mpr x.2
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, (minpoly.monic hx).natDegree_map]
  set g := minpoly 𝒪[K] (x : L)
  have hg0 : aeval x g = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero, ← minpoly.aeval 𝒪[K] (x : L)]
    exact (aeval_algebraMap_apply L x g).symm
  have hmon : (g.map (algebraMap 𝒪[K] 𝓀[K])).Monic := (minpoly.monic hx).map _
  refine (natDegree_le_natDegree (minpoly.min 𝓀[K] _ hmon ?_)).trans
    ((minpoly.monic hx).natDegree_map _).le
  rw [aeval_map_algebraMap, ← IsLocalRing.ResidueField.algebraMap_eq, aeval_algebraMap_apply, hg0,
    map_zero]

end Degree

end GroundTheory.LocalField
end
end

