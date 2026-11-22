import Mathlib
import GroundTheory.LocalFields.BrauerInductionPrime
import GroundTheory.LocalFields.Ramification
import GroundTheory.LocalFields.Bundle0006
import GroundTheory.LocalFields.Unramified
import GroundTheory.LocalFields.Eisenstein
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.Bundle0007
import GroundTheory.LocalFields.Bundle0005
import GroundTheory.LocalFields.IntermediateField

-- bundled from GroundTheory.LocalFields.BrauerInductionAssembly
section
noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

universe u

variable {G : Type u} [Group G] [Fintype G]

omit [Fintype G] in
theorem IsElementary.mono {H L : Subgroup G} (hH : IsElementary H) (hLH : L ≤ H) : IsElementary L :=
  let ⟨p, hp, hHp⟩ := hH
  ⟨p, hp, hHp.mono hLH⟩

variable (hmono : ∀ K : Subgroup G, IsElementary K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hmono

theorem one_mem_spanZ_of_mono : (1 : G → ℂ) ∈ spanZ (IsElementary (G := G)) := by
  let T : ℤ →ₗ[ℤ] (G → ℂ) := LinearMap.toSpanSingleton ℤ (G → ℂ) 1
  let I : Submodule ℤ ℤ := (spanZ (IsElementary (G := G))).comap T
  have hmem : ∀ k : ℤ, k ∈ I ↔ k • (1 : G → ℂ) ∈ spanZ (IsElementary (G := G)) := fun k ↦ Iff.rfl
  have hprimes : ∀ p : ℕ, p.Prime → ∃ m : ℕ, ¬ p ∣ m ∧ (m : ℤ) ∈ I := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hpm, hm⟩ := exists_smul_one_mem_spanZ (p := p) (Complex.isPrimitiveRoot_exp _
      Nat.card_pos.ne') (fun K hK χ hχ ↦ hmono K ⟨p, hp, hK⟩ χ hχ)
    exact ⟨m, hpm, (hmem _).mpr (spanZ_mono (fun K hK ↦ ⟨p, hp, hK⟩) hm)⟩
  set d := Submodule.IsPrincipal.generator I
  have hdvd : ∀ k ∈ I, d ∣ k := fun k hk ↦ by
    obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hk
    exact ⟨s, by rw [hs, smul_eq_mul, mul_comm]⟩
  have hd : d.natAbs = 1 := by
    by_contra hd
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    obtain ⟨m, hpm, hm⟩ := hprimes p hp
    apply hpm
    have h1 : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd
    exact Int.natCast_dvd_natCast.mp (h1.trans (hdvd _ hm))
  have hd1 : (1 : ℤ) ∈ I := by
    have hdI : d ∈ I := Submodule.IsPrincipal.generator_mem I
    rcases Int.natAbs_eq d with h | h
    · rw [hd] at h
      rwa [h] at hdI
    · rw [hd] at h
      have := I.smul_mem (-1) hdI
      rwa [h, smul_eq_mul, Nat.cast_one, neg_mul_neg, one_mul] at this
  simpa using (hmem 1).mp hd1

theorem mem_spanZ_of_mono {χ : G → ℂ} (hχ : IsCharacter χ) : χ ∈ spanZ (IsElementary (G := G)) := by
  have h := mul_mem_spanZ (fun K L hK hLK ↦ hK.mono hLK) hmono hχ (one_mem_spanZ_of_mono hmono)
  rwa [mul_one] at h

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LowerIndex
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial

theorem range_restrictScalarsHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) :
    (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range = M.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨τ, rfl⟩ m hm
    exact τ.commutes ⟨m, hm⟩
  · intro h
    refine ⟨{ σ with commutes' := fun m ↦ h m m.2 }, ?_⟩
    ext x
    rfl

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def lowerIndex (σ : L ≃ₐ[K] L) : ℕ∞ :=
  ⨅ x : 𝒪[L], addVal 𝒪[L] (integerAlgEquiv K L σ x - x)

variable {K L}

theorem le_lowerIndex_iff {σ : L ≃ₐ[K] L} {n : ℕ∞} :
    n ≤ lowerIndex K L σ ↔ ∀ x : 𝒪[L], n ≤ addVal 𝒪[L] (integerAlgEquiv K L σ x - x) :=
  le_iInf_iff

theorem lowerIndex_le (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    lowerIndex K L σ ≤ addVal 𝒪[L] (integerAlgEquiv K L σ x - x) :=
  iInf_le _ x

theorem mem_lowerRamificationGroup_iff_lowerIndex {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔ (((i + 1).toNat : ℕ) : ℕ∞) ≤ lowerIndex K L σ := by
  rw [mem_lowerRamificationGroup_iff, le_lowerIndex_iff]
  simp only [mem_maximalIdeal_pow_iff_le_addVal]

theorem mem_lowerRamificationGroup_natCast_iff_lowerIndex {n : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L n ↔ ((n + 1 : ℕ) : ℕ∞) ≤ lowerIndex K L σ := by
  rw [mem_lowerRamificationGroup_natCast_iff, le_lowerIndex_iff]
  simp only [mem_maximalIdeal_pow_iff_le_addVal]

@[simp]
theorem lowerIndex_one : lowerIndex K L 1 = ⊤ := by
  simp [lowerIndex]

theorem lowerIndex_eq_top_iff {σ : L ≃ₐ[K] L} : lowerIndex K L σ = ⊤ ↔ σ = 1 := by
  constructor
  · intro h
    apply algEquiv_eq_one_of_forall_integer
    intro x
    have := lowerIndex_le σ x
    rwa [h, top_le_iff, addVal_eq_top_iff, sub_eq_zero] at this
  · rintro rfl
    exact lowerIndex_one

theorem lowerIndex_ne_top {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) : lowerIndex K L σ ≠ ⊤ :=
  fun h ↦ hσ (lowerIndex_eq_top_iff.mp h)

theorem one_le_lowerIndex_iff {σ : L ≃ₐ[K] L} :
    1 ≤ lowerIndex K L σ ↔ σ ∈ lowerRamificationGroup K L 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, mem_lowerRamificationGroup_natCast_iff_lowerIndex]
  simp

theorem lowerIndex_eq_zero_iff {σ : L ≃ₐ[K] L} :
    lowerIndex K L σ = 0 ↔ σ ∉ lowerRamificationGroup K L 0 := by
  rw [← one_le_lowerIndex_iff, not_le, Order.lt_one_iff]

theorem min_le_lowerIndex_mul (σ τ : L ≃ₐ[K] L) :
    min (lowerIndex K L σ) (lowerIndex K L τ) ≤ lowerIndex K L (σ * τ) := by
  rw [le_lowerIndex_iff]
  intro x
  have h : integerAlgEquiv K L (σ * τ) x - x =
      (integerAlgEquiv K L σ (integerAlgEquiv K L τ x) - integerAlgEquiv K L τ x) +
        (integerAlgEquiv K L τ x - x) := by
    rw [map_mul, AlgEquiv.mul_apply]; ring
  rw [h]
  exact le_trans (min_le_min (lowerIndex_le σ _) (lowerIndex_le τ x)) ((addVal 𝒪[L]).map_add _ _)

theorem lowerIndex_le_lowerIndex_inv (σ : L ≃ₐ[K] L) : lowerIndex K L σ ≤ lowerIndex K L σ⁻¹ := by
  rw [le_lowerIndex_iff]
  intro x
  have h : integerAlgEquiv K L σ⁻¹ x - x =
      -(integerAlgEquiv K L σ (integerAlgEquiv K L σ⁻¹ x) - integerAlgEquiv K L σ⁻¹ x) := by
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    ring
  rw [h, AddValuation.map_neg]
  exact lowerIndex_le σ _

@[simp]
theorem lowerIndex_inv (σ : L ≃ₐ[K] L) : lowerIndex K L σ⁻¹ = lowerIndex K L σ :=
  le_antisymm (by simpa using lowerIndex_le_lowerIndex_inv σ⁻¹) (lowerIndex_le_lowerIndex_inv σ)

theorem lowerIndex_mul_of_lt {σ τ : L ≃ₐ[K] L} (h : lowerIndex K L τ < lowerIndex K L σ) :
    lowerIndex K L (σ * τ) = lowerIndex K L τ := by
  refine le_antisymm ?_ ((min_eq_right h.le).symm.le.trans (min_le_lowerIndex_mul σ τ))
  have h1 := min_le_lowerIndex_mul σ⁻¹ (σ * τ)
  rw [inv_mul_cancel_left, lowerIndex_inv] at h1
  by_contra h2
  rw [not_le] at h2
  exact (lt_min h h2).not_ge h1

theorem lowerIndex_eq_addVal_of_adjoin_eq_top {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤)
    (σ : L ≃ₐ[K] L) : lowerIndex K L σ = addVal 𝒪[L] (integerAlgEquiv K L σ x - x) := by
  refine le_antisymm (lowerIndex_le σ x) ?_
  rw [le_lowerIndex_iff]
  intro z
  have hz : z ∈ Algebra.adjoin 𝒪[K] {x} := hx ▸ trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, rfl⟩ := hz
  rw [addVal_le_iff_dvd]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← aeval_algHom_apply, ← eval_map_algebraMap, ← eval_map_algebraMap]
  exact sub_dvd_eval_sub _ _ _

section Subgroup

variable (M : IntermediateField K L)

@[simp]
theorem lowerIndex_restrictScalars (σ : L ≃ₐ[M] L) :
    lowerIndex K L (σ.restrictScalars K) = lowerIndex M L σ :=
  rfl

theorem lowerRamificationGroup_comap_restrictScalars (i : ℤ) :
    (lowerRamificationGroup K L i).comap (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroup M L i := by
  ext σ
  rw [Subgroup.mem_comap, AlgEquiv.restrictScalarsHom_apply, mem_lowerRamificationGroup_iff_lowerIndex,
    mem_lowerRamificationGroup_iff_lowerIndex, lowerIndex_restrictScalars]

theorem lowerRamificationGroup_map_restrictScalars (i : ℤ) :
    (lowerRamificationGroup M L i).map (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroup K L i ⊓ M.fixingSubgroup := by
  rw [← lowerRamificationGroup_comap_restrictScalars M, Subgroup.map_comap_eq,
    range_restrictScalarsHom, inf_comm]

theorem lowerRamificationGroup_map_fixedField [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) (i : ℤ) :
    (lowerRamificationGroup (IntermediateField.fixedField H) L i).map
        (AlgEquiv.restrictScalarsHom K) = lowerRamificationGroup K L i ⊓ H := by
  rw [lowerRamificationGroup_map_restrictScalars, IntermediateField.fixingSubgroup_fixedField]

end Subgroup

variable (K L) in

theorem card_lowerRamificationGroup_zero [IsGalois K L] :
    Nat.card (lowerRamificationGroup K L 0) = ramificationIndex K L := by
  rw [lowerRamificationGroup_zero]
  exact card_inertiaSubgroup K L

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.RamificationTame
section
noncomputable section

open scoped IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing IsDiscreteValuationRing

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natCast_ramificationIndex_ne_zero
    (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    (ramificationIndex K L : 𝓀[L]) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff 𝓀[L] (ringChar 𝓀[L]), ← Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  intro hdvd
  have h1 := Nat.Coprime.eq_one_of_dvd he.symm hdvd
  exact Nat.not_prime_one (h1 ▸ CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K]))

theorem exists_pow_eq_uniformizer_of_residueDegree_eq_one (hf : residueDegree K L = 1)
    (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ∃ π : 𝒪[K], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
      α ^ ramificationIndex K L = algebraMap 𝒪[K] 𝒪[L] π ∧ K⟮(α : L)⟯ = ⊤ := by
  set e := ramificationIndex K L with he_def
  obtain ⟨ϖK, hϖK⟩ := exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := exists_irreducible 𝒪[L]

  obtain ⟨u, hu⟩ : Associated (algebraMap 𝒪[K] 𝒪[L] ϖK) (ϖL ^ e) := by
    have h := map_maximalIdeal K L
    rw [hϖK.maximalIdeal_eq, hϖL.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
    exact h

  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_maximalIdeal K L hf (u : 𝒪[L])
  have hcu : IsUnit c := by
    by_contra hn
    have hnL : ¬ IsUnit (algebraMap 𝒪[K] 𝒪[L] c) := fun h ↦ hn (isUnit_of_map_unit _ _ h)
    have hmem : algebraMap 𝒪[K] 𝒪[L] c ∈ 𝓂[L] := (mem_maximalIdeal _).mpr hnL
    have : (u : 𝒪[L]) ∈ 𝓂[L] := by
      have := add_mem hc hmem
      rwa [sub_add_cancel] at this
    exact (mem_maximalIdeal _).mp this u.isUnit
  set c' := hcu.unit
  set cL : 𝒪[L]ˣ := Units.map (algebraMap 𝒪[K] 𝒪[L] : 𝒪[K] →* 𝒪[L]) c' with hcL
  have hcLval : (cL : 𝒪[L]) = algebraMap 𝒪[K] 𝒪[L] c := rfl

  have hv : u * cL⁻¹ ∈ unitFiltration L 1 := by
    rw [mem_unitFiltration, pow_one, Units.val_mul,
      show (u : 𝒪[L]) * ((cL⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 = ((u : 𝒪[L]) - cL) * ((cL⁻¹ : 𝒪[L]ˣ) : 𝒪[L])
        by rw [sub_mul, Units.mul_inv], hcLval]
    exact Ideal.mul_mem_right _ _ hc
  obtain ⟨w, hw⟩ := unitFiltration_one_le_range_pow (natCast_ramificationIndex_ne_zero K L he) hv
  have hw' : w ^ e = u * cL⁻¹ := hw
  have hinv : (w⁻¹) ^ e = cL * u⁻¹ := by rw [inv_pow, hw', mul_inv_rev, inv_inv]

  have htot : ramificationIndex K L = Module.finrank K L := by
    have := ramificationIndex_mul_residueDegree K L
    rwa [hf, mul_one] at this
  refine ⟨ϖK * (c' : 𝒪[K]), (irreducible_mul_isUnit c'.isUnit).mpr hϖK,
    ϖL * ((w⁻¹ : 𝒪[L]ˣ) : 𝒪[L]), (irreducible_mul_isUnit (w⁻¹).isUnit).mpr hϖL, ?_, ?_⟩
  · have hui := Units.mul_inv u
    calc (ϖL * ((w⁻¹ : 𝒪[L]ˣ) : 𝒪[L])) ^ e = ϖL ^ e * (((w⁻¹) ^ e : 𝒪[L]ˣ) : 𝒪[L]) := by
          rw [mul_pow, Units.val_pow_eq_pow_val]
      _ = algebraMap 𝒪[K] 𝒪[L] ϖK * u * (cL * ((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L])) := by
          rw [← hu, hinv, Units.val_mul]
      _ = algebraMap 𝒪[K] 𝒪[L] (ϖK * (c' : 𝒪[K])) := by
          rw [map_mul, show algebraMap 𝒪[K] 𝒪[L] (c' : 𝒪[K]) = cL from rfl]
          linear_combination (algebraMap 𝒪[K] 𝒪[L] ϖK * cL) * hui
  · exact adjoin_eq_top_of_irreducible htot ((irreducible_mul_isUnit (w⁻¹).isUnit).mpr hϖL)

variable {K L}

theorem exists_pow_eq_uniformizer_of_isUnramified (T : IntermediateField K L) [IsUnramified K T]
    (hf : residueDegree T L = 1) (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ramificationIndex T L = ramificationIndex K L ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ ramificationIndex K L = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by
  have htow : ramificationIndex T L = ramificationIndex K L := by
    rw [ramificationIndex_tower K T L, IsUnramified.ramificationIndex_eq_one (K := K) (L := T), one_mul]
  have he' : Nat.Coprime (ramificationIndex T L) (ringChar 𝓀[T]) := by
    rw [htow, ← Algebra.ringChar_eq 𝓀[K] 𝓀[T]]
    exact he
  refine ⟨htow, ?_⟩
  rw [← htow]
  exact exists_pow_eq_uniformizer_of_residueDegree_eq_one T L hf he'

end GroundTheory.LocalField
end
end

