import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.Bundle0001

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.GelFlagA
section
noncomputable section

open Matrix Module

namespace PositivityTheory.RgBcC.VC.GFA

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

variable {n : ℕ}

theorem mulVec_eq_sum (g : Mat n) (c : Fin n → ℂ) : g *ᵥ c = ∑ j, c j • (fun i => g i j) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem adapted (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) :
    ∃ (g : Mat n) (blk : Fin n → ℕ), IsUnit g ∧ (∀ j, blk j ≤ 2) ∧
      (∀ c, g *ᵥ c ∈ W₁ ↔ ∀ j, blk j ≠ 0 → c j = 0) ∧ (∀ c, g *ᵥ c ∈ W₂ ↔ ∀ j, blk j = 2 → c j = 0) := by
  classical
  obtain ⟨b₁, hb₁, hspan₁, hli₁'⟩ := exists_linearIndependent ℂ (W₁ : Set (Fin n → ℂ))
  have hli₁ : LinearIndepOn ℂ id b₁ := hli₁'
  have hb₁₂ : b₁ ⊆ (W₂ : Set (Fin n → ℂ)) := hb₁.trans hW
  set b₂ := hli₁.extend hb₁₂ with hb₂def
  have hli₂ : LinearIndepOn ℂ id b₂ := hli₁.linearIndepOn_extend hb₁₂
  have hb₂W : b₂ ⊆ (W₂ : Set (Fin n → ℂ)) := hli₁.extend_subset hb₁₂
  have h12 : b₁ ⊆ b₂ := hli₁.subset_extend hb₁₂
  have hW₂s : (W₂ : Set (Fin n → ℂ)) ⊆ Submodule.span ℂ b₂ := hli₁.subset_span_extend hb₁₂
  set B := Module.Basis.extend hli₂ with hBdef
  have h23 : b₂ ⊆ Set.range B := by rw [Module.Basis.range_extend]; exact hli₂.subset_extend _
  have : Finite (hli₂.extend (Set.subset_univ b₂)) := Module.Finite.finite_basis B
  haveI : Fintype (hli₂.extend (Set.subset_univ b₂)) := Fintype.ofFinite _
  have hcard : Fintype.card (hli₂.extend (Set.subset_univ b₂)) = n := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  set B' := B.reindex (Fintype.equivFinOfCardEq hcard) with hB'def
  have hrange : Set.range B' = Set.range B := by
    rw [hB'def, Module.Basis.coe_reindex]
    exact (Fintype.equivFinOfCardEq hcard).symm.surjective.range_comp _
  refine ⟨Matrix.of fun i j => B' j i, fun j => if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2, ?_, ?_, ?_, ?_⟩
  · rw [← linearIndependent_cols_iff_isUnit]
    exact B'.linearIndependent
  · intro j; dsimp only; split_ifs <;> omega
  · intro c
    have e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c := by
      rw [mulVec_eq_sum, Module.Basis.equivFun_symm_apply]; rfl
    have hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j := fun j => by
      have h0 := congrFun (B'.equivFun.apply_symm_apply c) j
      rwa [Module.Basis.equivFun_apply] at h0
    have hW₁ : W₁ = Submodule.span ℂ (B' '' {j | B' j ∈ b₁}) := by
      calc W₁ = Submodule.span ℂ (W₁ : Set (Fin n → ℂ)) := (Submodule.span_eq W₁).symm
        _ = Submodule.span ℂ b₁ := hspan₁.symm
        _ = _ := by
          congr 1
          ext v
          simp only [Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · intro hv
            obtain ⟨j, hj⟩ : v ∈ Set.range B' := hrange ▸ h23 (h12 hv)
            exact ⟨j, hj ▸ hv, hj⟩
          · rintro ⟨j, hj, rfl⟩; exact hj
    rw [e, hW₁, Module.Basis.mem_span_image]
    constructor
    · intro h j hj
      by_contra hc
      have hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n)) := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hr]; exact hc
      have h' : B' j ∈ b₁ := h hm
      change (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0 at hj
      rw [if_pos h'] at hj
      exact hj rfl
    · intro h j hj
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hr] at hj
      show B' j ∈ b₁
      by_contra hb
      refine hj (h j ?_)
      show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0
      rw [if_neg hb]; split_ifs <;> omega
  · intro c
    have e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c := by
      rw [mulVec_eq_sum, Module.Basis.equivFun_symm_apply]; rfl
    have hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j := fun j => by
      have h0 := congrFun (B'.equivFun.apply_symm_apply c) j
      rwa [Module.Basis.equivFun_apply] at h0
    have hW₂ : W₂ = Submodule.span ℂ (B' '' {j | B' j ∈ b₂}) := by
      calc W₂ = Submodule.span ℂ b₂ :=
            le_antisymm (fun x hx => hW₂s hx) (Submodule.span_le.2 hb₂W)
        _ = _ := by
          congr 1
          ext v
          simp only [Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · intro hv
            obtain ⟨j, hj⟩ : v ∈ Set.range B' := hrange ▸ h23 hv
            exact ⟨j, hj ▸ hv, hj⟩
          · rintro ⟨j, hj, rfl⟩; exact hj
    rw [e, hW₂, Module.Basis.mem_span_image]
    constructor
    · intro h j hj
      by_contra hc
      have hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n)) := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hr]; exact hc
      have h' : B' j ∈ b₂ := h hm
      change (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2 at hj
      by_cases h1 : B' j ∈ b₁
      · rw [if_pos h1] at hj; exact absurd hj (by decide)
      · rw [if_neg h1, if_pos h'] at hj; exact absurd hj (by decide)
    · intro h j hj
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hr] at hj
      show B' j ∈ b₂
      by_contra hb
      have hb1 : B' j ∉ b₁ := fun h1 => hb (h12 h1)
      refine hj (h j ?_)
      show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2
      rw [if_neg hb1, if_neg hb]

end PositivityTheory.RgBcC.VC.GFA
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerNIdB
section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC.KN

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem nil_fix {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {u : G n} (hu : u ∈ nilSet W₁ W₂) :
    ∀ v ∈ W₁, u.val *ᵥ v = v := by
  intro v hv
  have h := hu.2.2 v hv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
  exact h

theorem nil_mem₂ {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) {u : G n} (hu : u ∈ nilSet W₁ W₂) :
    ∀ v ∈ W₂, u.val *ᵥ v ∈ W₂ := by
  intro v hv
  have h := W₂.add_mem (hu.1 v) hv
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel] at h

theorem nil_maps {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) {u : G n} (hu : u ∈ nilSet W₁ W₂)
    (hu' : u⁻¹ ∈ nilSet W₁ W₂) :
    W₁.map (Matrix.mulVecLin u.val) = W₁ ∧ W₂.map (Matrix.mulVecLin u.val) = W₂ := by
  constructor
  · apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
      rw [Matrix.mulVecLin_apply, nil_fix hu v hv]
      exact hv
    · intro v hv
      exact Submodule.mem_map.mpr ⟨v, hv, by rw [Matrix.mulVecLin_apply, nil_fix hu v hv]⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
      rw [Matrix.mulVecLin_apply]
      exact nil_mem₂ hW hu v hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨u⁻¹.val *ᵥ v, nil_mem₂ hW hu' v hv, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem mem_nil_of {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {N : Subgroup (G n)} (hN : (N : Set (G n)) = nilSet W₁ W₂)
    (u : N) : (u : G n) ∈ nilSet W₁ W₂ := by
  rw [← hN]
  exact u.2

theorem maps_of {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) {N : Subgroup (G n)}
    (hN : (N : Set (G n)) = nilSet W₁ W₂) (u : N) :
    W₁.map (Matrix.mulVecLin (u : G n).val) = W₁ ∧ W₂.map (Matrix.mulVecLin (u : G n).val) = W₂ := by
  refine nil_maps hW (mem_nil_of hN u) ?_
  rw [← Subgroup.coe_inv]
  exact mem_nil_of hN u⁻¹

theorem cptN (hLg : LgCpt) {N : Subgroup (G n)} (hNc : IsClosed (N : Set (G n))) (R : ℝ) :
    IsCompact {u : N | lg (u : G n).val ≤ R} :=
  hNc.isClosedEmbedding_subtypeVal.isCompact_preimage (hLg n R)

theorem mul_memGL (u : G n) (y : Mat n) (hy : y ∈ GLs n) : u.val * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq] at hy ⊢
  rw [Matrix.det_mul]
  exact mul_ne_zero (by simpa [GLs] using memGL u) hy

theorem integrable_N (hLg : LgCpt) [MeasurableSpace (G n)] [BorelSpace (G n)] {N : Subgroup (G n)}
    (hNc : IsClosed (N : Set (G n))) (ν : Measure N) [IsFiniteMeasureOnCompacts ν] {X : Type} [NormedAddCommGroup X]
    (h : Mat n → X) (hc : ContinuousOn h (GLs n)) (R : ℝ) (hR : ∀ y ∈ GLs n, R < lg y → h y = 0)
    (y : Mat n) (hy : y ∈ GLs n) : Integrable (fun u : N => h ((u : G n).val * y)) ν := by
  have hcont : Continuous (fun u : N => h ((u : G n).val * y)) :=
    hc.comp_continuous ((Units.continuous_val.comp continuous_subtype_val).mul continuous_const)
      (fun u => mul_memGL _ y hy)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (cptN hLg hNc (R + lg y)) ?_
  intro u hu
  simp only [Set.mem_setOf_eq, not_le] at hu
  apply hR _ (mul_memGL _ y hy)
  have := lg_le_of_mul ((u : G n).val) y hy
  linarith

end PositivityTheory.RgBcC.VC.KN
end
end

