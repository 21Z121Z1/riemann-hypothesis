import Mathlib
import GroundTheory.LocalFields.Different
import GroundTheory.LocalFields.LowerIndexQuotient
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0073
import GroundTheory.LocalFields.LocalFourier
import GroundTheory.LocalFields.HerbrandFunction

-- bundled from GroundTheory.LocalFields.DifferentGalois
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

variable {K L} in

theorem map_minpoly_eq_prod {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    (minpoly 𝒪[K] x).map (algebraMap 𝒪[K] 𝒪[L]) =
      ∏ σ : L ≃ₐ[K] L, (X - C (integerAlgEquiv K L σ x)) :=
  _root_.UpperTheory.Reformulated.B.MinpolyProductMap.map_minpoly_eq_prod hx

variable {K L} in

theorem aeval_derivative_minpoly_eq_prod [DecidableEq (L ≃ₐ[K] L)] {x : 𝒪[L]}
    (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    aeval x (derivative (minpoly 𝒪[K] x)) =
      ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (x - integerAlgEquiv K L σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map, map_minpoly_eq_prod hx, derivative_prod_finset,
    eval_finsetSum, Finset.sum_eq_single (1 : L ≃ₐ[K] L)]
  · rw [eval_mul, derivative_X_sub_C, eval_one, mul_one, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  · intro σ _ hσ
    rw [eval_mul, eval_prod]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := 1) ?_ ?_) _
    · exact Finset.mem_erase.mpr ⟨Ne.symm hσ, Finset.mem_univ _⟩
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem differentExponent_eq_sum_lowerIndex [DecidableEq (L ≃ₐ[K] L)] :
    (differentExponent K L : ℕ∞) =
      ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), lowerIndex K L σ := by
  obtain ⟨x, hx⟩ := exists_integer_adjoin_eq_top K L
  rw [differentExponent_eq_addVal hx, aeval_derivative_minpoly_eq_prod hx, addVal_prod]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [lowerIndex_eq_addVal_of_adjoin_eq_top hx, ← AddValuation.map_neg, neg_sub]

theorem differentExponent_eq_sum_card_lowerRamificationGroup {N : ℕ}
    (hN : lowerRamificationGroup K L N = ⊥) :
    differentExponent K L =
      ∑ i ∈ Finset.range N, (Nat.card (lowerRamificationGroup K L i) - 1) := by
  classical
  have h := differentExponent_eq_sum_lowerIndex K L
  have hσ : ∀ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), lowerIndex K L σ =
      (((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card : ℕ∞) := by
    intro σ hσ
    have hne : σ ≠ 1 := Finset.ne_of_mem_erase hσ
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hne)
    have hnN : n ≤ N := by
      by_contra hlt'
      have hlt := not_le.mp hlt'
      have hmem : σ ∈ lowerRamificationGroup K L N := by
        rw [mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn]
        exact_mod_cast hlt
      rw [hN, Subgroup.mem_bot] at hmem
      exact hne hmem
    have hfilter : (Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i) =
        Finset.range n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range,
        mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn, Nat.cast_le]
      omega
    rw [← hn, hfilter, Finset.card_range]
  rw [Finset.sum_congr rfl hσ] at h
  have hswap : ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L),
      ((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card =
      ∑ i ∈ Finset.range N, (Nat.card (lowerRamificationGroup K L i) - 1) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.card_filter, Finset.filter_erase, Finset.card_erase_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_mem _⟩), ← Fintype.card_subtype,
      Nat.card_eq_fintype_card]
  rw [← hswap]
  exact_mod_cast h

theorem differentExponent_eq_finsum_card_lowerRamificationGroup :
    differentExponent K L = ∑ᶠ i : ℕ, (Nat.card (lowerRamificationGroup K L i) - 1) := by
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  rw [differentExponent_eq_sum_card_lowerRamificationGroup K L (hN N le_rfl),
    finsum_eq_sum_of_support_subset _ (s := Finset.range N)]
  intro i hi
  rw [Function.mem_support] at hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h'
  have h := not_lt.mp h'
  apply hi
  rw [hN i (by exact_mod_cast h)]
  simp

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalFourierExistence
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter
open scoped WithZero Pointwise

section RatCircle

def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ : ℚ →+* ℝ).toAddMonoidHom
    (AddSubgroup.zmultiples_le_of_mem (by
      rw [AddSubgroup.mem_comap]
      simp))

theorem ratAddCircleToReal_coe (q : ℚ) :
    ratAddCircleToReal (q : AddCircle (1 : ℚ)) = ((q : ℝ) : AddCircle (1 : ℝ)) := rfl

theorem ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    rw [ratAddCircleToReal_coe, AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this)

def ratCircleChar : AddChar (AddCircle (1 : ℚ)) Circle :=
  (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom ratAddCircleToReal

theorem ratCircleChar_apply (x : AddCircle (1 : ℚ)) :
    ratCircleChar x = AddCircle.toCircle (ratAddCircleToReal x) := rfl

theorem ratCircleChar_injective : Function.Injective ratCircleChar :=
  (AddCircle.injective_toCircle one_ne_zero).comp ratAddCircleToReal_injective

theorem ratCircleChar_eq_one_iff {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply ratCircleChar_injective
    rw [h, AddChar.map_zero_eq_one]
  · rintro rfl
    exact AddChar.map_zero_eq_one _

end RatCircle

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Existence

theorem exists_mem_valBall_neg_one_notMem_valBall_zero :
    ∃ x : K, x ∈ valBall K (-1) ∧ x ∉ valBall K 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hi : (ϖ : K)⁻¹ ≠ 0 := inv_ne_zero h0
  refine ⟨(ϖ : K)⁻¹, ?_, ?_⟩
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
    omega

theorem continuous_of_isTrivialOn {χ : AddChar K Circle} {n : ℤ} (h : IsTrivialOn χ n) :
    Continuous χ := by
  have hlc : IsLocallyConstant χ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{z | z - x ∈ valBall K n},
      (isOpen_valBall n).preimage (continuous_id.sub continuous_const), by simp, fun z hz => ?_⟩
    have e : x + (z - x) = z := by abel
    rw [← e, AddChar.map_add_eq_mul, h _ hz, mul_one]
  exact hlc.continuous

theorem continuous_iff_exists_isTrivialOn (χ : AddChar K Circle) :
    Continuous χ ↔ ∃ n, IsTrivialOn χ n :=
  ⟨exists_isTrivialOn χ, fun ⟨_, h⟩ => continuous_of_isTrivialOn h⟩

theorem exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one :
    ∃ ψ : AddChar K Circle, IsTrivialOn ψ 0 ∧ ¬ IsTrivialOn ψ (-1) := by
  obtain ⟨x, hx1, hx0⟩ := exists_mem_valBall_neg_one_notMem_valBall_zero (K := K)
  let π : K →+ K ⧸ valBall K 0 := QuotientAddGroup.mk' (valBall K 0)
  have hπx : π x ≠ 0 := by
    rwa [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hπx
  let ψ : AddChar K Circle :=
    ratCircleChar.compAddMonoidHom ((c : K ⧸ valBall K 0 →+ AddCircle (1 : ℚ)).comp π)
  have hψ : ∀ y, ψ y = ratCircleChar (c (π y)) := fun _ => rfl
  refine ⟨ψ, fun y hy => ?_, fun h => ?_⟩
  · have : π y = 0 := by
      rwa [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [hψ, this, map_zero, AddChar.map_zero_eq_one]
  · exact hc (ratCircleChar_eq_one_iff.mp ((hψ x).symm.trans (h x hx1)))

theorem exists_addChar_addCharConductor_eq_zero :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = 0 := by
  obtain ⟨ψ, h0, h1⟩ := exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one (K := K)
  have hc : Continuous ψ := continuous_of_isTrivialOn h0
  have hne : ψ ≠ 1 := by
    rintro rfl
    exact h1 fun _ _ => AddChar.one_apply _
  refine ⟨ψ, hc, hne, le_antisymm ((isTrivialOn_iff hc hne 0).mp h0) ?_⟩
  by_contra hlt
  exact h1 ((isTrivialOn_iff hc hne (-1)).mpr (by omega))

theorem exists_addChar_addCharConductor_eq (n : ℤ) :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = n := by
  obtain ⟨ψ, hc, hne, h0⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0ϖ : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have ha : (ϖ : K) ^ (-n) ≠ 0 := zpow_ne_zero _ h0ϖ
  refine ⟨ψ.mulShift ((ϖ : K) ^ (-n)), continuous_mulShift hc _, mulShift_ne_one hne ha, ?_⟩
  have hord : ord ((ϖ : K) ^ (-n)) = -n := by
    simp [ord, map_zpow₀, normalizedValuation_uniformizer hϖ]
  rw [addCharConductor_mulShift hc hne ha, h0, hord]
  ring

theorem exists_addChar_continuous_ne_one :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨ψ, hc, hne, -⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  exact ⟨ψ, hc, hne⟩

theorem nonempty_selfDual :
    Nonempty (Multiplicative K ≃ₜ* PontryaginDual (Multiplicative K)) := by
  obtain ⟨ψ, hc, hne⟩ := exists_addChar_continuous_ne_one (K := K)
  exact ⟨selfDual hc hne⟩

end Existence

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.UpperNumbering
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

theorem enatMin_min (n N : ℕ∞) (a : ℝ) : enatMin (min n N) a = enatMin n (enatMin N a) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k =>
    induction N using ENat.recTopCoe with
    | top => simp
    | coe l =>
      rw [← (Nat.mono_cast (α := ℕ∞)).map_min, enatMin_coe, enatMin_coe, enatMin_coe, Nat.cast_min,
        min_assoc]

theorem natCast_toNat_min (n : ℕ∞) (m : ℕ) : (((min n m).toNat : ℕ) : ℕ∞) = min n m :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top m) (min_le_right _ _))

theorem cast_toNat_min (n : ℕ∞) (m : ℕ) : (((min n m).toNat : ℕ) : ℝ) = enatMin n m := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k =>
    rw [← (Nat.mono_cast (α := ℕ∞)).map_min, ENat.toNat_natCast, enatMin_coe, Nat.cast_min]

section Fiber

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) [Normal K M]

open Classical in

theorem sum_filter_restrictNormalHom_eq {β : Type*} [AddCommMonoid β] [Fintype (L ≃ₐ[K] L)]
    [Fintype (L ≃ₐ[M] L)] (F : (L ≃ₐ[K] L) → β) (σ : L ≃ₐ[K] L) :
    ∑ ρ ∈ Finset.univ.filter
        (fun ρ ↦ AlgEquiv.restrictNormalHom M ρ = AlgEquiv.restrictNormalHom M σ), F ρ =
      ∑ τ : L ≃ₐ[M] L, F (σ * τ.restrictScalars K) := by
  symm
  refine Finset.sum_bij (fun τ _ ↦ σ * τ.restrictScalars K) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro τ _
    rw [Finset.mem_filter, map_mul, restrictNormalHom_restrictScalars, mul_one]
    exact ⟨Finset.mem_univ _, rfl⟩
  · intro a _ b _ hab
    exact AlgEquiv.restrictScalars_injective K (mul_left_cancel hab)
  · intro ρ hρ
    obtain ⟨τ, hτ⟩ := exists_eq_mul_restrictScalars_of_restrictNormalHom_eq M
      (Finset.mem_filter.mp hρ).2
    exact ⟨τ, Finset.mem_univ _, hτ⟩

end Fiber

section QuotientMap

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]

end QuotientMap

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem mem_lowerRamificationGroupReal_of_lowerIndex_le {t : ℝ} {σ σ' : L ≃ₐ[K] L}
    (h : σ ∈ lowerRamificationGroupReal K L t) (hle : lowerIndex K L σ ≤ lowerIndex K L σ') :
    σ' ∈ lowerRamificationGroupReal K L t := by
  rw [lowerRamificationGroupReal, mem_lowerRamificationGroup_iff_lowerIndex] at h ⊢
  exact h.trans hle

variable [IsGalois K L] (M : IntermediateField K L) [IsGalois K M]

theorem exists_lowerIndex_eq_herbrandPhi (σ : L ≃ₐ[K] L) :
    ∃ σ₀ : L ≃ₐ[K] L,
      AlgEquiv.restrictNormalHom M σ₀ = AlgEquiv.restrictNormalHom M σ ∧
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤ lowerIndex K L σ₀) ∧
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ₀ * τ.restrictScalars K) =
        min (lowerIndex M L τ) (lowerIndex K L σ₀)) ∧
      (AlgEquiv.restrictNormalHom M σ = 1 → lowerIndex K L σ₀ = ⊤) ∧
      (AlgEquiv.restrictNormalHom M σ ≠ 1 → ∃ m k : ℕ, lowerIndex K L σ₀ = m ∧
        lowerIndex K M (AlgEquiv.restrictNormalHom M σ) = k ∧
        (k : ℝ) = herbrandPhi M L ((m : ℝ) - 1) + 1) := by
  obtain ⟨τ₀, hmax, hmin⟩ := exists_lowerIndex_mul_eq_min M σ
  set σ₀ := σ * τ₀.restrictScalars K with hσ₀
  have hres : AlgEquiv.restrictNormalHom M σ₀ = AlgEquiv.restrictNormalHom M σ := by
    rw [hσ₀, map_mul, restrictNormalHom_restrictScalars, mul_one]
  refine ⟨σ₀, hres, hmax, hmin, ?_, ?_⟩
  · intro h1
    obtain ⟨τ', hτ'⟩ := exists_eq_mul_restrictScalars_of_restrictNormalHom_eq M (σ := 1) (ρ := σ)
      (by rw [h1, map_one])
    have hm : τ'.restrictScalars K * (τ'⁻¹).restrictScalars K = 1 :=
      AlgEquiv.ext fun x ↦ τ'.apply_symm_apply x
    have := hmax τ'⁻¹
    rwa [← hτ', one_mul, hm, lowerIndex_one, top_le_iff] at this
  · intro hs
    have hσ₀1 : σ₀ ≠ 1 := fun h ↦ hs (by rw [← hres, h, map_one])
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hσ₀1)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hs)
    refine ⟨m, k, hm.symm, hk.symm, ?_⟩
    have hsum := ramificationIndex_mul_lowerIndex_restrictNormalHom M σ₀
    rw [hres, ← hk] at hsum
    simp_rw [hmin, ← hm] at hsum
    have hconv : (∑ τ : L ≃ₐ[M] L, min (lowerIndex M L τ) (m : ℕ∞)) =
        ((∑ τ : L ≃ₐ[M] L, (min (lowerIndex M L τ) (m : ℕ∞)).toNat : ℕ) : ℕ∞) := by
      rw [Nat.cast_sum]
      simp_rw [natCast_toNat_min]
    rw [hconv, ← Nat.cast_mul, Nat.cast_inj] at hsum
    have hsumR : (ramificationIndex M L : ℝ) * k =
        ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex M L τ) (m : ℝ) := by
      simp_rw [← cast_toNat_min]
      exact_mod_cast hsum
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hphi := herbrandPhi_eq_sum_lowerIndex (K := M) (L := L) (u := (m : ℝ) - 1) (by linarith)
    rw [sub_add_cancel, card_lowerRamificationGroup_zero M L, ← hsumR] at hphi
    have he : (0 : ℝ) < ramificationIndex M L := by exact_mod_cast ramificationIndex_pos M L
    rw [hphi]
    field_simp
    ring

theorem sum_enatMin_lowerIndex_coset (σ : L ≃ₐ[K] L) {u : ℝ} (hu : -1 ≤ u) :
    ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex K L (σ * τ.restrictScalars K)) (u + 1) =
      ramificationIndex M L *
        enatMin (lowerIndex K M (AlgEquiv.restrictNormalHom M σ)) (herbrandPhi M L u + 1) := by
  classical
  obtain ⟨σ₀, hres, -, hmin, h1, hne⟩ := exists_lowerIndex_eq_herbrandPhi M σ
  have hre : ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex K L (σ * τ.restrictScalars K)) (u + 1) =
      ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex K L (σ₀ * τ.restrictScalars K)) (u + 1) := by
    rw [← sum_filter_restrictNormalHom_eq M (fun ρ ↦ enatMin (lowerIndex K L ρ) (u + 1)) σ,
      ← sum_filter_restrictNormalHom_eq M (fun ρ ↦ enatMin (lowerIndex K L ρ) (u + 1)) σ₀, hres]
  rw [hre]
  simp_rw [hmin, enatMin_min]
  have he : (0 : ℝ) < ramificationIndex M L := by exact_mod_cast ramificationIndex_pos M L
  have hH : ∀ w : ℝ, 0 ≤ w → ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex M L τ) w =
      ramificationIndex M L * (herbrandPhi M L (w - 1) + 1) := by
    intro w hw
    rw [herbrandPhi_eq_sum_lowerIndex (K := M) (L := L) (by linarith), sub_add_cancel,
      card_lowerRamificationGroup_zero M L, sub_add_cancel, ← mul_assoc, mul_inv_cancel₀ he.ne',
      one_mul]
  by_cases hs : AlgEquiv.restrictNormalHom M σ = 1
  · rw [h1 hs, enatMin_top, hs, lowerIndex_one, enatMin_top, hH (u + 1) (by linarith),
      add_sub_cancel_right]
  · obtain ⟨m, k, hm, hk, hkφ⟩ := hne hs
    rw [hm, hk, enatMin_coe, enatMin_coe, hH _ (le_min (Nat.cast_nonneg m) (by linarith))]
    have hinner : herbrandPhi M L (min (m : ℝ) (u + 1) - 1) + 1 =
        min (k : ℝ) (herbrandPhi M L u + 1) := by
      rw [← min_sub_sub_right, add_sub_cancel_right,
        (herbrandPhi_strictMono (K := M) (L := L)).monotone.map_min, hkφ, min_add_add_right]
    rw [hinner]

theorem herbrandPhi_comp (u : ℝ) :
    herbrandPhi K M (herbrandPhi M L u) = herbrandPhi K L u := by
  classical
  by_cases hu : -1 ≤ u
  · have hv : -1 ≤ herbrandPhi M L u := by
      rw [← herbrandPhi_of_nonpos (K := M) (L := L) (show (-1 : ℝ) ≤ 0 by norm_num)]
      exact (herbrandPhi_strictMono (K := M) (L := L)).monotone hu
    rw [herbrandPhi_eq_sum_lowerIndex (K := K) (L := M) hv,
      herbrandPhi_eq_sum_lowerIndex (K := K) (L := L) hu]
    have hfib : ∑ σ : L ≃ₐ[K] L, enatMin (lowerIndex K L σ) (u + 1) =
        ∑ s : M ≃ₐ[K] M, (ramificationIndex M L : ℝ) *
          enatMin (lowerIndex K M s) (herbrandPhi M L u + 1) := by
      rw [← Finset.sum_fiberwise Finset.univ (fun σ ↦ AlgEquiv.restrictNormalHom M σ)
        (fun σ ↦ enatMin (lowerIndex K L σ) (u + 1))]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) L s
      rw [sum_filter_restrictNormalHom_eq M (fun ρ ↦ enatMin (lowerIndex K L ρ) (u + 1)) σ,
        sum_enatMin_lowerIndex_coset M σ hu]
    rw [hfib, ← Finset.mul_sum, card_lowerRamificationGroup_zero K L,
      card_lowerRamificationGroup_zero K M, ramificationIndex_tower K M L]
    have h1 : (0 : ℝ) < ramificationIndex K M := by exact_mod_cast ramificationIndex_pos K M
    have h2 : (0 : ℝ) < ramificationIndex M L := by exact_mod_cast ramificationIndex_pos M L
    push_cast
    field_simp
  · have hu0 : u ≤ 0 := by linarith [not_le.mp hu]
    rw [herbrandPhi_of_nonpos (K := M) (L := L) hu0, herbrandPhi_of_nonpos hu0,
      herbrandPhi_of_nonpos hu0]

theorem herbrandPsi_comp (v : ℝ) :
    herbrandPsi M L (herbrandPsi K M v) = herbrandPsi K L v := by
  symm
  rw [herbrandPsi_eq_iff, ← herbrandPhi_comp M, herbrandPhi_herbrandPsi, herbrandPhi_herbrandPsi]

theorem map_lowerRamificationGroupReal (u : ℝ) :
    (lowerRamificationGroupReal K L u).map (AlgEquiv.restrictNormalHom M) =
      lowerRamificationGroupReal K M (herbrandPhi M L u) := by
  ext s
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨σ₀, -, hmax, -, -, hne⟩ := exists_lowerIndex_eq_herbrandPhi M σ
    by_cases hs : AlgEquiv.restrictNormalHom M σ = 1
    · rw [hs]
      exact one_mem _
    obtain ⟨m, k, hm, hk, hkφ⟩ := hne hs
    have hle : lowerIndex K L σ ≤ lowerIndex K L σ₀ := by
      have := hmax 1
      rwa [show σ * (1 : L ≃ₐ[M] L).restrictScalars K = σ from AlgEquiv.ext fun _ ↦ rfl] at this
    have hσ₀ := mem_lowerRamificationGroupReal_of_lowerIndex_le hσ hle
    rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hm] at hσ₀
    rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hk, hkφ, add_le_add_iff_right]
    exact (herbrandPhi_strictMono (K := M) (L := L)).monotone (by linarith)
  · intro hs
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) L s
    obtain ⟨σ₀, hres, -, -, -, hne⟩ := exists_lowerIndex_eq_herbrandPhi M σ
    by_cases h1 : AlgEquiv.restrictNormalHom M σ = 1
    · exact ⟨1, one_mem _, by rw [h1, map_one]⟩
    obtain ⟨m, k, hm, hk, hkφ⟩ := hne h1
    refine ⟨σ₀, ?_, hres⟩
    rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hm]
    rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hk, hkφ, add_le_add_iff_right,
      (herbrandPhi_strictMono (K := M) (L := L)).le_iff_le] at hs
    linarith

theorem map_upperRamificationGroup (v : ℝ) :
    (upperRamificationGroup K L v).map (AlgEquiv.restrictNormalHom M) =
      upperRamificationGroup K M v := by
  rw [upperRamificationGroup, map_lowerRamificationGroupReal, ← herbrandPsi_comp M,
    herbrandPhi_herbrandPsi]
  rfl

section Quotient

variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]

end Quotient

end GroundTheory.LocalField
end
end

