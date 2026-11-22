import Mathlib
import GroundTheory.LocalFields.Bundle0012
import GroundTheory.LocalFields.Bundle0014
import GroundTheory.LocalFields.LocalArtinTransport

-- bundled from GroundTheory.LocalFields.ArtinConductorAbelian
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section HasseArf

theorem exists_int_eq_of_forall_upperRamificationGroup_ne_of_isAbelianGalois
    {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M] [IsAbelianGalois K M] {v : ℝ}
    (h : ∀ w, v < w → upperRamificationGroup K M w ≠ upperRamificationGroup K M v) :
    ∃ m : ℤ, v = m := by
  let ι : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let E : IntermediateField K (SeparableClosure K) := ι.fieldRange
  let e : M ≃ₐ[K] E := AlgEquiv.ofInjectiveField ι
  have : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  have : IsAbelianGalois K E := IsAbelianGalois.of_algHom (M := M) e.symm.toAlgHom
  apply exists_int_eq_of_forall_upperRamificationGroup_ne E
  intro w hw heq
  apply h w hw
  rw [← map_upperRamificationGroup_autCongr e w, ← map_upperRamificationGroup_autCongr e v] at heq
  exact Subgroup.map_injective e.autCongr.injective heq

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in

theorem upperRamificationGroup_le_of_herbrandPhi_lt {j : ℕ} {w : ℝ} (hw : herbrandPhi K L j < w) :
    upperRamificationGroup K L w ≤ lowerRamificationGroup K L ((j : ℤ) + 1) := by
  have hψ : (j : ℝ) < herbrandPsi K L w := by
    rw [← herbrandPsi_herbrandPhi (K := K) (L := L) (j : ℝ)]
    exact herbrandPsi_strictMono hw
  show lowerRamificationGroup K L ⌈herbrandPsi K L w⌉ ≤ _
  exact lowerRamificationGroup_antitone K L (Int.add_one_le_iff.mpr (Int.lt_ceil.mpr hψ))

omit [IsGalois K L] in

theorem upperRamificationGroup_herbrandPhi_natCast (j : ℕ) :
    upperRamificationGroup K L (herbrandPhi K L j) = lowerRamificationGroup K L j := by
  rw [upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast]

theorem exists_int_herbrandPhi_eq_of_monoidHom (ψ : (L ≃ₐ[K] L) →* ℂˣ) {j : ℕ}
    (hj : ¬ lowerRamificationGroup K L j ≤ ψ.ker)
    (hj1 : lowerRamificationGroup K L ((j : ℤ) + 1) ≤ ψ.ker) :
    ∃ m : ℤ, herbrandPhi K L j = m := by
  set M := IntermediateField.fixedField ψ.ker
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M).ker = ψ.ker := by
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
  have hcomm : ∀ a b : (L ≃ₐ[K] L) ⧸ ψ.ker, a * b = b * a := fun a b ↦
    QuotientGroup.kerLift_injective ψ (by rw [map_mul, map_mul, mul_comm])
  have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun a b ↦ by
    obtain ⟨a', rfl⟩ := (IsGalois.normalAutEquivQuotient ψ.ker).surjective a
    obtain ⟨b', rfl⟩ := (IsGalois.normalAutEquivQuotient ψ.ker).surjective b
    rw [← map_mul, ← map_mul, hcomm]⟩⟩
  have : IsAbelianGalois K M := { }
  apply exists_int_eq_of_forall_upperRamificationGroup_ne_of_isAbelianGalois (K := K) (M := M)
  intro w hw heq
  have h1 : upperRamificationGroup K M w = ⊥ := by
    rw [← map_upperRamificationGroup M w, Subgroup.map_eq_bot_iff, hker]
    exact (upperRamificationGroup_le_of_herbrandPhi_lt hw).trans hj1
  have h2 : upperRamificationGroup K M (herbrandPhi K L j) ≠ ⊥ := by
    rw [← map_upperRamificationGroup M, Ne, Subgroup.map_eq_bot_iff, hker,
      upperRamificationGroup_herbrandPhi_natCast]
    exact hj
  exact h2 (heq ▸ h1)

end HasseArf

section OneDim

variable {G : Type*} [Group G]

def charRep (ψ : G →* ℂˣ) : Representation ℂ G ℂ :=
  (DistribMulAction.toModuleEnd ℂ ℂ).comp ψ

@[simp]
theorem charRep_apply (ψ : G →* ℂˣ) (g : G) (v : ℂ) : charRep ψ g v = (ψ g : ℂ) * v :=
  rfl

theorem character_charRep (ψ : G →* ℂˣ) (g : G) : (charRep ψ).character g = ψ g := by
  have h : charRep ψ g = (ψ g : ℂ) • LinearMap.id := by
    ext
    simp
  rw [Representation.character, h, map_smul, LinearMap.trace_id, finrank_self]
  simp

open Classical in

theorem finrank_invariants_charRep_comp (ψ : G →* ℂˣ) (S : Subgroup G) :
    finrank ℂ (Representation.invariants ((charRep ψ).comp S.subtype)) = if S ≤ ψ.ker then 1 else 0 := by
  split_ifs with h
  · have htop : Representation.invariants ((charRep ψ).comp S.subtype) = ⊤ := by
      ext v
      simp only [Submodule.mem_top, iff_true]
      intro g
      have : ψ g = 1 := h g.2
      simp [this]
    rw [htop, finrank_top, finrank_self]
  · have hbot : Representation.invariants ((charRep ψ).comp S.subtype) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      obtain ⟨g, hg, hψ⟩ := SetLike.not_le_iff_exists.mp h
      have hv' : (ψ g : ℂ) * v = v := hv ⟨g, hg⟩
      have hne : (ψ g : ℂ) ≠ 1 := fun h1 ↦ hψ (MonoidHom.mem_ker.mpr (Units.val_eq_one.mp h1))
      have : ((ψ g : ℂ) - 1) * v = 0 := by rw [sub_mul, hv', one_mul, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
    rw [hbot, finrank_bot]

end OneDim

section Conductor

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

open Classical in

theorem artinConductor_charRep_eq_sum (ψ : (L ≃ₐ[K] L) →* ℂˣ) {N : ℕ}
    (hN : lowerRamificationGroup K L N = ⊥) :
    artinConductor (charRep ψ) = ∑ i ∈ Finset.range N,
      if lowerRamificationGroup K L i ≤ ψ.ker then 0
      else (Nat.card (lowerRamificationGroup K L i) / Nat.card (lowerRamificationGroup K L 0) : ℚ) := by
  rw [artinConductor_eq_sum _ hN]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [finrank_invariants_charRep_comp, finrank_self]
  split_ifs <;> simp

theorem herbrandPhi_natCast_eq_sum (n : ℕ) :
    herbrandPhi K L n = ∑ i ∈ Finset.range n,
      (Nat.card (lowerRamificationGroup K L ((i : ℤ) + 1)) : ℝ) /
        Nat.card (lowerRamificationGroup K L 0) := by
  induction n with
  | zero => simp [herbrandPhi_zero]
  | succ n ih =>
    have h := herbrandPhi_of_mem_Icc (K := K) (L := L) n (u := (n : ℝ) + 1)
      ⟨by linarith, le_rfl⟩
    have hrel := relIndex_mul_card_inf (lowerRamificationGroup K L ((n : ℤ) + 1))
      (lowerRamificationGroup K L 0)
    rw [inf_of_le_left (lowerRamificationGroup_antitone K L (by omega))] at hrel
    have hc : (Nat.card (lowerRamificationGroup K L ((n : ℤ) + 1)) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hr : ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup K L 0) : ℝ) ≠ 0 := by
      intro h0
      have h0' : (lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex
          (lowerRamificationGroup K L 0) = 0 := by exact_mod_cast h0
      rw [h0', zero_mul] at hrel
      exact Nat.card_pos.ne' hrel.symm
    push_cast
    rw [h, ih, Finset.sum_range_succ, add_sub_cancel_left, ← hrel]
    push_cast
    field_simp

theorem exists_lowerRamificationGroup_jump (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (h0 : ¬ lowerRamificationGroup K L 0 ≤ ψ.ker) :
    ∃ j : ℕ, ¬ lowerRamificationGroup K L j ≤ ψ.ker ∧
      lowerRamificationGroup K L ((j : ℤ) + 1) ≤ ψ.ker := by
  classical
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  have hex : ∃ n : ℕ, lowerRamificationGroup K L n ≤ ψ.ker :=
    ⟨N, by rw [hN N le_rfl]; exact bot_le⟩
  set k := Nat.find hex with hk
  have hk0 : k ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [← hk, h] at this
    exact h0 (by exact_mod_cast this)
  refine ⟨k - 1, Nat.find_min hex (by omega), ?_⟩
  have := Nat.find_spec hex
  rw [← hk] at this
  convert this using 2
  omega

theorem artinConductor_charRep_eq_one_add_herbrandPhi (ψ : (L ≃ₐ[K] L) →* ℂˣ) {j : ℕ}
    (hj : ¬ lowerRamificationGroup K L j ≤ ψ.ker)
    (hj1 : lowerRamificationGroup K L ((j : ℤ) + 1) ≤ ψ.ker) :
    (artinConductor (charRep ψ) : ℝ) = 1 + herbrandPhi K L j := by
  classical
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  have hjN : j < N := by
    by_contra h
    apply hj
    rw [hN j (by exact_mod_cast not_lt.mp h)]
    exact bot_le
  have hiff : ∀ i : ℕ, lowerRamificationGroup K L i ≤ ψ.ker ↔ ¬ i ≤ j := by
    intro i
    constructor
    · intro hi hij
      exact hj ((lowerRamificationGroup_antitone K L (by exact_mod_cast hij)).trans hi)
    · intro hij
      exact (lowerRamificationGroup_antitone K L (by omega)).trans hj1
  have h0 : (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [artinConductor_charRep_eq_sum ψ (hN N le_rfl)]
  simp_rw [hiff, ite_not]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.range N).filter (fun i ↦ i ≤ j) = Finset.range (j + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilt, Finset.sum_range_succ', herbrandPhi_natCast_eq_sum]
  push_cast
  rw [div_self h0, add_comm]

theorem exists_nat_artinConductor_charRep_eq [IsGalois K L] (ψ : (L ≃ₐ[K] L) →* ℂˣ) :
    ∃ n : ℕ, artinConductor (charRep ψ) = n := by
  by_cases h0 : lowerRamificationGroup K L 0 ≤ ψ.ker
  · refine ⟨0, ?_⟩
    rw [Nat.cast_zero, artinConductor_eq_zero_iff]
    intro σ hσ
    have h1 : ψ σ = 1 := h0 hσ
    ext
    simp [h1]
  obtain ⟨j, hj, hj1⟩ := exists_lowerRamificationGroup_jump ψ h0
  obtain ⟨m, hm⟩ := exists_int_herbrandPhi_eq_of_monoidHom ψ hj hj1
  have hpos : (0 : ℝ) ≤ herbrandPhi K L j := by
    rw [← herbrandPhi_zero (K := K) (L := L)]
    exact herbrandPhi_strictMono.monotone (Nat.cast_nonneg j)
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ m := hm ▸ hpos
    exact_mod_cast this
  refine ⟨(1 + m).toNat, ?_⟩
  have h := artinConductor_charRep_eq_one_add_herbrandPhi ψ hj hj1
  rw [hm] at h
  have hn : (((1 + m).toNat : ℕ) : ℝ) = 1 + m := by
    have h2 : (((1 + m).toNat : ℕ) : ℤ) = 1 + m := Int.toNat_of_nonneg (by omega)
    exact_mod_cast h2
  have h' : ((artinConductor (charRep ψ) : ℚ) : ℝ) = ((((1 + m).toNat : ℕ) : ℚ) : ℝ) := by
    rw [Rat.cast_natCast, hn, h]
  exact Rat.cast_injective h'

end Conductor

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalArtinAbstractField
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

section Embedding

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [IsSepClosure K Ω] in
theorem isAbelianGalois_fieldRange (ι : L →ₐ[K] Ω) : IsAbelianGalois K ι.fieldRange :=
  have := IsGalois.of_algEquiv ι.equivFieldRange
  { toIsMulCommutative := ⟨⟨fun σ τ => (AlgEquiv.autCongr ι.equivFieldRange).symm.injective
      ((map_mul _ σ τ).trans ((mul_comm' _ _).trans (map_mul _ τ σ).symm))⟩⟩ }

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsAbelianGalois K L]
  [IsSepClosure K Ω] in
theorem finiteDimensional_fieldRange (ι : L →ₐ[K] Ω) : FiniteDimensional K ι.fieldRange :=
  LinearEquiv.finiteDimensional ι.equivFieldRange.toLinearEquiv

def artinOfEmbedding (ι : L →ₐ[K] Ω) : Kˣ →* (L ≃ₐ[K] L) :=
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  (AlgEquiv.autCongr ι.equivFieldRange).symm.toMonoidHom.comp
    ((restrictAb ι.fieldRange (le_maximalAbelianExtension _)).comp (localArtinMap K Ω))

theorem apply_artinOfEmbedding (ι : L →ₐ[K] Ω) (x : Kˣ) (z : L) :
    ι (artinOfEmbedding ι x z) =
      ((localArtinMap K Ω x ⟨ι z, (have := isAbelianGalois_fieldRange ι;
        le_maximalAbelianExtension ι.fieldRange) ⟨z, rfl⟩⟩ : maximalAbelianExtension K Ω) : Ω) := by
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  have h : ι (artinOfEmbedding ι x z) =
      ((restrictAb ι.fieldRange (le_maximalAbelianExtension _) (localArtinMap K Ω x)
        (ι.equivFieldRange z) : ι.fieldRange) : Ω) := by
    simp only [artinOfEmbedding, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
    rw [← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply]
    rfl
  rw [h, restrictAb_apply]
  rfl

theorem artinOfEmbedding_eq (ι₁ ι₂ : L →ₐ[K] Ω) : artinOfEmbedding ι₁ = artinOfEmbedding ι₂ := by
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : Algebra.IsSeparable ι₁.fieldRange Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K ι₁.fieldRange Ω
  obtain ⟨φ, hφ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) ι₁.fieldRange
    (M := Ω) (E := Ω) (ι₂.comp ι₁.equivFieldRange.symm.toAlgHom)
  have hφι : ∀ z : L, φ (ι₁ z) = ι₂ z := by
    intro z
    have := congrArg (fun f : ι₁.fieldRange →ₐ[K] Ω => f (ι₁.equivFieldRange z)) hφ
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at this
    rw [← this]
    rfl
  set τ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
  set t := topologicalAbelianizationEquiv K Ω (τ : TopologicalAbelianization (Ω ≃ₐ[K] Ω))
  have ht : ∀ w : maximalAbelianExtension K Ω, ((t w : maximalAbelianExtension K Ω) : Ω) = τ w :=
    fun w => topologicalAbelianizationEquiv_mk_apply K Ω τ w
  ext x z
  have key : ι₂ (artinOfEmbedding ι₁ x z) = ι₂ (artinOfEmbedding ι₂ x z) := by
    rw [← hφι (artinOfEmbedding ι₁ x z), apply_artinOfEmbedding ι₂]
    change τ (ι₁ (artinOfEmbedding ι₁ x z)) = _
    rw [apply_artinOfEmbedding ι₁]
    set w : maximalAbelianExtension K Ω := ⟨ι₁ z, (have := isAbelianGalois_fieldRange ι₁;
      le_maximalAbelianExtension ι₁.fieldRange) ⟨z, rfl⟩⟩
    have htw : t w = ⟨ι₂ z, (have := isAbelianGalois_fieldRange ι₂;
        le_maximalAbelianExtension ι₂.fieldRange) ⟨z, rfl⟩⟩ :=
      Subtype.ext ((ht w).trans (hφι z))
    have hc : (localArtinMap K Ω x) (t w) = t ((localArtinMap K Ω x) w) := by
      rw [← AlgEquiv.mul_apply, mul_comm' (localArtinMap K Ω x) t, AlgEquiv.mul_apply]
    rw [← ht, ← hc, htw]
  exact ι₂.injective key

variable {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [IsSepClosure K Ω']

theorem artinOfEmbedding_algEquiv_comp (ε : Ω ≃ₐ[K] Ω') (ι : L →ₐ[K] Ω) :
    artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) = artinOfEmbedding ι := by
  ext x z
  have key : ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) x z) =
      ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ι x z) := by
    rw [apply_artinOfEmbedding]
    change _ = ε (ι (artinOfEmbedding ι x z))
    rw [apply_artinOfEmbedding, localArtinMap_algEquiv_apply]
    rfl
  exact ((ε : Ω →ₐ[K] Ω').comp ι).injective key

end Embedding

section Intrinsic

variable (K L) in

def localArtinMapOfField : Kˣ →* (L ≃ₐ[K] L) :=
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  artinOfEmbedding (IsSepClosed.lift : L →ₐ[K] SeparableClosure K)

theorem localArtinMapOfField_eq_artinOfEmbedding {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (ι : L →ₐ[K] Ω) : localArtinMapOfField K L = artinOfEmbedding ι := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  let ε : SeparableClosure K ≃ₐ[K] Ω := IsSepClosure.equiv K (SeparableClosure K) Ω
  rw [localArtinMapOfField, ← artinOfEmbedding_algEquiv_comp ε]
  exact artinOfEmbedding_eq _ _

theorem ker_artinOfEmbedding {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ι : L →ₐ[K] Ω) : (artinOfEmbedding ι).ker = (normUnits K L).range := by
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  have hker : (artinOfEmbedding ι).ker =
      ((restrictAb ι.fieldRange (le_maximalAbelianExtension _)).comp (localArtinMap K Ω)).ker := by
    ext x
    simp [artinOfEmbedding, MonoidHom.mem_ker]
  rw [hker, ker_restrictAb_localArtinMap]
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨Units.map ι.equivFieldRange.symm.toRingEquiv.toRingHom.toMonoidHom w, Units.ext ?_⟩
    simp [coe_normUnits, Algebra.norm_eq_of_algEquiv]
  · rintro ⟨w, rfl⟩
    refine ⟨Units.map ι.equivFieldRange.toRingEquiv.toRingHom.toMonoidHom w, Units.ext ?_⟩
    simp [coe_normUnits, Algebra.norm_eq_of_algEquiv]

theorem ker_localArtinMapOfField : (localArtinMapOfField K L).ker = (normUnits K L).range := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  exact ker_artinOfEmbedding _

theorem surjective_localArtinMapOfField : Function.Surjective (localArtinMapOfField K L) := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  set ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  intro σ
  obtain ⟨x, hx⟩ := surjective_restrictAb_localArtinMap (Ω := SeparableClosure K) ι.fieldRange
    (AlgEquiv.autCongr ι.equivFieldRange σ)
  refine ⟨x, ?_⟩
  change (AlgEquiv.autCongr ι.equivFieldRange).symm _ = σ
  rw [hx, MulEquiv.symm_apply_apply]

def localReciprocityOfField : Kˣ ⧸ (normUnits K L).range ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq ker_localArtinMapOfField.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ surjective_localArtinMapOfField)

theorem localReciprocityOfField_mk (x : Kˣ) :
    localReciprocityOfField (K := K) (L := L) (x : Kˣ ⧸ (normUnits K L).range) =
      localArtinMapOfField K L x :=
  rfl

end Intrinsic

end GroundTheory.LocalField
end
end

