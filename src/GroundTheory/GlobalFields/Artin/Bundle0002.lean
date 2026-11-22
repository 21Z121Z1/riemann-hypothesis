import Mathlib
import GroundTheory.GlobalFields.Artin.MemInvariantsCompSubtypeIff
import GroundTheory.LocalFields.Bundle0002
import GroundTheory.TateCohomology.DoubleCosetSum

-- bundled from GroundTheory.GlobalFields.Artin.InflationTower
section
noncomputable section

open IsDedekindDomain NumberField
open scoped Pointwise

namespace GroundTheory.Global

section Average

variable {G H : Type*} [Group G] [Group H]

theorem card_mul_sum_comp_of_surjective {A B : Type*} [Group A] [Group B] [Fintype A]
    [Fintype B] (ψ : A →* B) (hψ : Function.Surjective ψ) (F : B → ℂ) :
    (Fintype.card B : ℂ) * ∑ a, F (ψ a) = (Fintype.card A : ℂ) * ∑ b, F b := by
  have h1 : ∀ b : B, ∑ a, F (b * ψ a) = ∑ a, F (ψ a) := by
    intro b
    obtain ⟨a₀, rfl⟩ := hψ b
    calc ∑ a, F (ψ a₀ * ψ a) = ∑ a, F (ψ (a₀ * a)) := by simp only [map_mul]
      _ = ∑ a, F (ψ a) := Equiv.sum_comp (Equiv.mulLeft a₀) (fun a => F (ψ a))
  have h2 : ∀ a : A, ∑ b, F (b * ψ a) = ∑ b, F b := fun a =>
    Equiv.sum_comp (Equiv.mulRight (ψ a)) F
  calc (Fintype.card B : ℂ) * ∑ a, F (ψ a) = ∑ _b : B, ∑ a, F (ψ a) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ b : B, ∑ a, F (b * ψ a) := Finset.sum_congr rfl fun b _ => (h1 b).symm
    _ = ∑ a : A, ∑ b, F (b * ψ a) := Finset.sum_comm
    _ = ∑ _a : A, ∑ b, F b := Finset.sum_congr rfl fun a _ => h2 a
    _ = (Fintype.card A : ℂ) * ∑ b, F b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem cosetAverage_comp (I : Subgroup G) [Finite I] (π : G →* H) (f : H → ℂ) (g : G) :
    cosetAverage I (f ∘ π) g = cosetAverage (I.map π) f (π g) := by
  classical
  have : Finite (I.map π) := Finite.of_surjective _ (π.subgroupMap_surjective I)
  have : Fintype I := Fintype.ofFinite _
  have : Fintype (I.map π) := Fintype.ofFinite _
  have key := card_mul_sum_comp_of_surjective (π.subgroupMap I) (π.subgroupMap_surjective I)
    (fun j => f (π g * j))
  have hI : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJ : (Fintype.card (I.map π) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold cosetAverage
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff hI hJ]
  simp only [Function.comp_apply, map_mul]
  have hsub : ∀ i : I, π (i : G) = ((π.subgroupMap I i : I.map π) : H) := fun _ => rfl
  simp only [hsub]
  linear_combination key

end Average

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [IsGalois K F] [IsGalois K L]

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem algebraMap_restrictNormalHom_smul (σ : Gal(L/K)) (x : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F σ • x) =
      σ • algebraMap (𝓞 F) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective
  change algebraMap F L ((σ.restrictNormal F) (x : F)) = σ (algebraMap F L (x : F))
  exact AlgEquiv.restrictNormal_commutes σ F x

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem under_smul (σ : Gal(L/K)) (Q : Ideal (𝓞 L)) :
    (σ • Q).under (𝓞 F) = AlgEquiv.restrictNormalHom F σ • Q.under (𝓞 F) := by
  ext x
  simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.under_def, Ideal.mem_comap,
    ← map_inv, algebraMap_restrictNormalHom_smul]

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem restrictNormalHom_restrictScalars (g : Gal(L/F)) :
    AlgEquiv.restrictNormalHom F (g.restrictScalars K) = 1 := by
  refine AlgEquiv.ext fun x => (algebraMap F L).injective ?_
  change algebraMap F L (((g.restrictScalars K).restrictNormal F) x) = algebraMap F L x
  rw [AlgEquiv.restrictNormal_commutes]
  exact g.commutes x

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K F] [IsGalois K L] in

theorem restrictScalars_smul_ideal (g : Gal(L/F)) (I : Ideal (𝓞 L)) :
    g.restrictScalars K • I = g • I := by
  rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
  rfl

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem restrictNormalHom_mem_stabilizer {Q : Ideal (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) Q) :
    AlgEquiv.restrictNormalHom F σ ∈ MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F)) := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [← under_smul, hσ]

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem restrictNormalHom_mem_inertia {Q : Ideal (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ Q.inertia Gal(L/K)) :
    AlgEquiv.restrictNormalHom F σ ∈ (Q.under (𝓞 F)).inertia Gal(F/K) := by
  rw [AddSubgroup.mem_inertia] at hσ ⊢
  intro x
  change algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F σ • x - x) ∈ Q
  rw [map_sub, algebraMap_restrictNormalHom_smul]
  exact hσ _

omit [NumberField K] in

theorem exists_mem_stabilizer_restrictNormalHom_eq (Q : Ideal (𝓞 L)) [Q.IsPrime]
    {τ : Gal(F/K)} (hτ : τ ∈ MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F))) :
    ∃ σ ∈ MulAction.stabilizer Gal(L/K) Q, AlgEquiv.restrictNormalHom F σ = τ := by
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  obtain ⟨σ₀, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := F) L τ
  have : (σ₀ • Q).LiesOver (Q.under (𝓞 F)) :=
    ⟨by rw [under_smul, MulAction.mem_stabilizer_iff.1 hτ]⟩
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Q.under (𝓞 F)) (σ₀ • Q) Q Gal(L/F)
  refine ⟨g.restrictScalars K * σ₀, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, restrictScalars_smul_ideal, hg]
  · rw [map_mul, restrictNormalHom_restrictScalars, one_mul]

theorem exists_mem_inertia_restrictNormalHom_eq (Q : Ideal (𝓞 L)) [Q.IsPrime]
    {τ : Gal(F/K)} (hτ : τ ∈ (Q.under (𝓞 F)).inertia Gal(F/K)) :
    ∃ σ ∈ Q.inertia Gal(L/K), AlgEquiv.restrictNormalHom F σ = τ := by
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  obtain ⟨σ₁, hσ₁Q, hσ₁⟩ := exists_mem_stabilizer_restrictNormalHom_eq Q
    (Ideal.inertia_le_stabilizer _ hτ)

  let e₀ := Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) Gal(L/K) ⟨σ₁, hσ₁Q⟩
  have he₀ : ∀ y : 𝓞 L, e₀ (Ideal.Quotient.mk Q y) = Ideal.Quotient.mk Q (σ₁ • y) :=
    fun _ => rfl

  let e : (𝓞 L ⧸ Q) ≃ₐ[𝓞 F ⧸ Q.under (𝓞 F)] (𝓞 L ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
      change e₀ (Ideal.Quotient.mk Q (algebraMap (𝓞 F) (𝓞 L) x)) = _
      rw [he₀, ← algebraMap_restrictNormalHom_smul, Ideal.Quotient.eq, ← map_sub, hσ₁]
      exact AddSubgroup.mem_inertia.1 hτ x)
  have he : ∀ y : 𝓞 L, e (Ideal.Quotient.mk Q y) = Ideal.Quotient.mk Q (σ₁ • y) :=
    fun _ => rfl
  obtain ⟨ρ, hρ⟩ := Ideal.Quotient.stabilizerHom_surjective Gal(L/F) (Q.under (𝓞 F)) Q e.symm
  have hρ' : ∀ z : 𝓞 L,
      Ideal.Quotient.mk Q ((ρ : Gal(L/F)) • z) = e.symm (Ideal.Quotient.mk Q z) :=
    fun z => by rw [← hρ]; rfl
  refine ⟨(ρ : Gal(L/F)).restrictScalars K * σ₁, ?_, ?_⟩
  · rw [AddSubgroup.mem_inertia]
    intro y
    change _ ∈ Q
    rw [← Ideal.Quotient.eq]
    calc Ideal.Quotient.mk Q (((ρ : Gal(L/F)).restrictScalars K * σ₁) • y)
        = Ideal.Quotient.mk Q ((ρ : Gal(L/F)) • (σ₁ • y)) := by rw [mul_smul]; rfl
      _ = e.symm (e (Ideal.Quotient.mk Q y)) := by rw [hρ', he]
      _ = Ideal.Quotient.mk Q y := e.symm_apply_apply _
  · rw [map_mul, restrictNormalHom_restrictScalars, one_mul, hσ₁]

omit [NumberField K] in

theorem map_stabilizer_restrictNormalHom (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    (MulAction.stabilizer Gal(L/K) Q).map (AlgEquiv.restrictNormalHom F) =
      MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F)) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact restrictNormalHom_mem_stabilizer hσ
  · intro hτ
    obtain ⟨σ, hσ, h⟩ := exists_mem_stabilizer_restrictNormalHom_eq Q hτ
    exact ⟨σ, hσ, h⟩

theorem map_inertia_restrictNormalHom (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    (Q.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom F) =
      (Q.under (𝓞 F)).inertia Gal(F/K) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact restrictNormalHom_mem_inertia hσ
  · intro hτ
    obtain ⟨σ, hσ, h⟩ := exists_mem_inertia_restrictNormalHom_eq Q hτ
    exact ⟨σ, hσ, h⟩

theorem IsArithFrobAt.restrictNormalHom {φ : Gal(L/K)} {Q : Ideal (𝓞 L)}
    (h : IsArithFrobAt (𝓞 K) φ Q) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom F φ) (Q.under (𝓞 F)) := by
  intro x
  rw [Ideal.under_under]
  change algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F φ • x -
    x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) ∈ Q
  rw [map_sub, map_pow, algebraMap_restrictNormalHom_smul]
  exact h _

end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.Artin.Mackey
section
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise

namespace GroundTheory.Global.Artin

open GroundTheory.LocalField

variable {G : Type*} [Group G]

section ExtendByZero

theorem mem_conj_smul_iff (H : Subgroup G) (a g : G) :
    g ∈ (MulAut.conj a • H : Subgroup G) ↔ a⁻¹ * g * a ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
    inv_inv]

theorem mem_conj_inv_smul_iff (H : Subgroup G) (x g : G) :
    g ∈ (MulAut.conj x⁻¹ • H : Subgroup G) ↔ x * g * x⁻¹ ∈ H := by
  rw [mem_conj_smul_iff, inv_inv]

open Classical in

def extendByZero (H : Subgroup G) (f : H → ℂ) (g : G) : ℂ :=
  if h : g ∈ H then f ⟨g, h⟩ else 0

theorem extendByZero_of_mem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∈ H) :
    extendByZero H f g = f ⟨g, hg⟩ := by
  unfold extendByZero
  rw [dif_pos hg]

theorem extendByZero_of_notMem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∉ H) :
    extendByZero H f g = 0 := by
  unfold extendByZero
  rw [dif_neg hg]

@[simp]
theorem extendByZero_coe (H : Subgroup G) (f : H → ℂ) (h : H) : extendByZero H f h = f h :=
  extendByZero_of_mem H f h.2

theorem extendByZero_conj {H : Subgroup G} {f : H → ℂ} (hf : IsClassFun f) {h : G} (hh : h ∈ H)
    (g : G) : extendByZero H f (h * g * h⁻¹) = extendByZero H f g := by
  by_cases hg : g ∈ H
  · have hm : h * g * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh)
    rw [extendByZero_of_mem H f hm, extendByZero_of_mem H f hg, ← hf ⟨g, hg⟩ ⟨h, hh⟩]
    rfl
  · have hm : h * g * h⁻¹ ∉ H := fun hm ↦ hg (by
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) hm) hh
      simpa [mul_assoc] using this)
    rw [extendByZero_of_notMem H f hm, extendByZero_of_notMem H f hg]

theorem indFun_subtype_apply [Fintype G] (H : Subgroup G) [Fintype H] (f : H → ℂ) (s : G) :
    indFun H.subtype f s = (Nat.card H : ℂ)⁻¹ * ∑ t : G, extendByZero H f (t⁻¹ * s * t) := by
  classical
  rw [indFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases hm : t⁻¹ * s * t ∈ H
  · rw [extendByZero_of_mem H f hm, Finset.sum_eq_single ⟨_, hm⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (Subtype.ext hb')
    · simp
  · rw [extendByZero_of_notMem H f hm]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [if_neg]
    intro hb'
    exact hm (hb' ▸ b.2)

end ExtendByZero

section Count

variable [Fintype G]

open Classical in

theorem sum_mul_mul_eq (H D : Subgroup G) [Fintype H] [Fintype D] (x : G) (F : G → ℂ) :
    ∑ h : H, ∑ e : D, F (h * x * e) =
      (Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) *
        ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = DoubleCoset.mk H D x), F u := by
  classical
  set E : Subgroup D := (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D with hEdef
  have hE : ∀ c : D, c ∈ E ↔ x * c * x⁻¹ ∈ H := fun c ↦ by
    rw [hEdef, Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]
  have hfib : ∀ u : G, (Finset.univ.filter (fun p : H × D ↦ (p.1 : G) * x * p.2 = u)).card =
      if DoubleCoset.mk H D u = DoubleCoset.mk H D x then Nat.card E else 0 := by
    intro u
    split_ifs with hu
    · obtain ⟨h0, hh0, e0, he0, rfl⟩ := (DoubleCoset.eq H D x u).1 hu.symm
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      refine Finset.card_bij' (fun p _ ↦ ⟨⟨e0 * (p.2 : G)⁻¹, D.mul_mem he0 (D.inv_mem p.2.2)⟩, ?_⟩)
        (fun c _ ↦ (⟨h0 * (x * ((c : D) : G) * x⁻¹), H.mul_mem hh0 ((hE c).1 c.2)⟩,
          ⟨((c : D) : G)⁻¹ * e0, D.mul_mem (D.inv_mem (c : D).2) he0⟩)) ?_ ?_ ?_ ?_
      · rename_i p hp
        rw [Finset.mem_filter] at hp
        rw [hE]
        have hp1 : (p.1 : G) = h0 * x * e0 * (p.2 : G)⁻¹ * x⁻¹ := by
          rw [← hp.2]
          group
        have : x * (e0 * (p.2 : G)⁻¹) * x⁻¹ = h0⁻¹ * p.1 := by
          rw [hp1]
          group
        rw [show ((⟨e0 * (p.2 : G)⁻¹, D.mul_mem he0 (D.inv_mem p.2.2)⟩ : D) : G) =
          e0 * (p.2 : G)⁻¹ from rfl, this]
        exact H.mul_mem (H.inv_mem hh0) p.1.2
      · intro p _
        exact Finset.mem_univ _
      · intro c _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        group
      · intro p hp
        rw [Finset.mem_filter] at hp
        ext
        · change h0 * (x * (e0 * (p.2 : G)⁻¹) * x⁻¹) = p.1
          have hp1 : (p.1 : G) = h0 * x * e0 * (p.2 : G)⁻¹ * x⁻¹ := by
            rw [← hp.2]
            group
          rw [hp1]
          group
        · change (e0 * (p.2 : G)⁻¹)⁻¹ * e0 = p.2
          group
      · intro c _
        ext
        change e0 * (((c : D) : G)⁻¹ * e0)⁻¹ = ((c : D) : G)
        group
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ hp
      apply hu
      exact ((DoubleCoset.eq H D x u).2 ⟨p.1, p.1.2, p.2, p.2.2, hp.symm⟩).symm
  calc ∑ h : H, ∑ e : D, F (h * x * e)
      = ∑ p : H × D, F ((p.1 : G) * x * p.2) := (Fintype.sum_prod_type' _).symm
    _ = ∑ u : G, ∑ p ∈ Finset.univ.filter (fun p : H × D ↦ (p.1 : G) * x * p.2 = u),
          F ((p.1 : G) * x * p.2) :=
        (Finset.sum_fiberwise Finset.univ (fun p : H × D ↦ (p.1 : G) * x * p.2) _).symm
    _ = ∑ u : G, (if DoubleCoset.mk H D u = DoubleCoset.mk H D x then (Nat.card E : ℂ) else 0) *
          F u := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.1 hp).2], Finset.sum_const,
          nsmul_eq_mul, hfib u]
        split_ifs <;> simp
    _ = (Nat.card E : ℂ) *
          ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = DoubleCoset.mk H D x), F u := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp

end Count

section Mackey

def conjFun (H D : Subgroup G) (x : G) (f : H → ℂ) :
    (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D → ℂ :=
  fun d ↦ f ⟨x * ((d : D) : G) * x⁻¹,
    (mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩

theorem extendByZero_conjFun (H D : Subgroup G) (x : G) (f : H → ℂ) (y : D) :
    extendByZero _ (conjFun H D x f) y = extendByZero H f (x * y * x⁻¹) := by
  by_cases hy : y ∈ (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D
  · rw [extendByZero_of_mem _ _ hy, extendByZero_of_mem H f
      ((mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 hy))]
    rfl
  · have hy' : x * (y : G) * x⁻¹ ∉ H := fun h ↦
      hy (Subgroup.mem_subgroupOf.2 ((mem_conj_inv_smul_iff H x _).2 h))
    rw [extendByZero_of_notMem _ _ hy, extendByZero_of_notMem H f hy']

variable [Fintype G]

open Classical in

theorem indFun_comp_subtype_eq_sum (H D : Subgroup G) [Fintype H] [Fintype D] {f : H → ℂ}
    (hf : IsClassFun f) (x : DoubleCoset.Quotient (H : Set G) D → G)
    (hx : ∀ q, DoubleCoset.mk H D (x q) = q) :
    indFun H.subtype f ∘ D.subtype =
      ∑ q, indFun ((MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D).subtype
        (conjFun H D (x q) f) := by
  classical
  funext d
  rw [Function.comp_apply, Finset.sum_apply, indFun_subtype_apply]
  simp_rw [indFun_subtype_apply, extendByZero_conjFun]
  have h1 : ∑ t : G, extendByZero H f (t⁻¹ * D.subtype d * t) =
      ∑ u : G, extendByZero H f (u * d * u⁻¹) :=
    Fintype.sum_equiv (Equiv.inv G) _ _ (fun t ↦ by simp)
  rw [h1, ← Finset.sum_fiberwise Finset.univ (DoubleCoset.mk H D), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have key := sum_mul_mul_eq H D (x q) (fun u ↦ extendByZero H f (u * d * u⁻¹))
  rw [hx q] at key
  set E : Subgroup D := (MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D
  have hE0 : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : ∀ (h : H) (e : D), extendByZero H f ((h * x q * e) * d * (h * x q * e)⁻¹) =
      extendByZero H f (x q * ((e * d * e⁻¹ : D) : G) * (x q)⁻¹) := by
    intro h e
    rw [← extendByZero_conj hf h.2 (x q * ((e * d * e⁻¹ : D) : G) * (x q)⁻¹)]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h3 : ∑ h : H, ∑ e : D, extendByZero H f ((h * x q * e) * d * (h * x q * e)⁻¹) =
      Nat.card H * ∑ t : D, extendByZero H f (x q * ((t⁻¹ * d * t : D) : G) * (x q)⁻¹) := by
    simp_rw [h2]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv D) _ _ (fun e ↦ by simp)
  rw [h3] at key
  have hS : ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = q),
      extendByZero H f (u * d * u⁻¹) = (Nat.card E : ℂ)⁻¹ *
        (Nat.card H * ∑ t : D, extendByZero H f (x q * ((t⁻¹ * d * t : D) : G) * (x q)⁻¹)) := by
    rw [key, inv_mul_cancel_left₀ hE0]
  rw [hS, mul_left_comm, inv_mul_cancel_left₀ hH0]

end Mackey

end GroundTheory.Global.Artin
end
end

