import Formalism.FilteredPoleLength.ReducedBasisBounds.Bundle0002

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.BCount
section
namespace Formalism.LatticeBaseChangeAlt

open Finset

theorem levelsSum : LevelsSum := by
  intro ι _ ep f mm v T c' h
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  have hf : (0 : ℝ) ≤ (f z : ℝ) := Nat.cast_nonneg _
  calc (mm z : ℝ) * f z ≤ (ep z * T * c' * v z) * f z := mul_le_mul_of_nonneg_right (h z) hf
    _ = T * c' * ((ep z : ℝ) * f z * v z) := by ring

noncomputable def slackEquiv (D k : ℕ) :
    {α : Fin D → ℕ // ∑ i, α i ≤ k} ≃ {β : Fin (D + 1) → ℕ // ∑ i, β i = k} where
  toFun α := ⟨Fin.cons (k - ∑ i, α.1 i) α.1, by
    have := α.2
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega⟩
  invFun β := ⟨Fin.tail β.1, by
    have := β.2
    rw [Fin.sum_univ_succ] at this
    simp only [Fin.tail]
    omega⟩
  left_inv α := by
    apply Subtype.ext
    simp only [Fin.tail_cons]
  right_inv β := by
    apply Subtype.ext
    have h := β.2
    rw [Fin.sum_univ_succ] at h
    have h0 : k - ∑ i, Fin.tail β.1 i = β.1 0 := by
      simp only [Fin.tail]
      omega
    simp only [h0, Fin.cons_self_tail]

end Formalism.LatticeBaseChangeAlt
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.FilIntegerStep
section
namespace Formalism.LatticeBaseChangeAlt

theorem ordCeil : OrdCeil := by
  intro n x h
  have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  have h2 : (-(⌈x⌉ : ℝ) - 1) < (n : ℝ) := by linarith
  have h3 : (-⌈x⌉ - 1 : ℤ) < n := by exact_mod_cast h2
  omega

theorem poleOrderGood : PoleOrderGood := by
  intro ep T ν νs c' vet e hep hc hv hν ⟨n, hn⟩ he
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hint : (ep : ℝ) * ((T : ℝ) * ν - e) = (((T : ℤ) * n - ep * e : ℤ) : ℝ) := by
    push_cast; rw [← hn]; ring
  rw [hint, Int.ceil_intCast, Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · rw [← hint]
    have : (T : ℝ) * ν - e ≤ T * c' * vet := by nlinarith
    nlinarith

theorem poleOrderBad : PoleOrderBad := by
  intro ep T ν νs c' vet hep hT hc hv hν e
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he : (T : ℝ) * (νs + 1) ≤ (e : ℝ) := Int.le_ceil _
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hx : (ep : ℝ) * ((T : ℝ) * ν - e) ≤ (ep : ℝ) * (T * c' * vet) - ep := by
    have : (T : ℝ) * ν - e ≤ T * c' * vet - 1 := by nlinarith
    nlinarith
  have hc1 : ((⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) < (ep : ℝ) * ((T : ℝ) * ν - e) + 1 :=
    Int.ceil_lt_add_one _
  rw [Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · nlinarith

theorem shareExponent : ShareExponent := by
  intro D T δ xL xF hδ h1 h2
  have hD : (0 : ℝ) ≤ D := by positivity
  nlinarith

theorem heightAbsorb : HeightAbsorb := by
  intro HL Hde X Y a ha ha2 hY h1 h2
  have hm : X ≤ max X 0 := le_max_left _ _
  have hm0 : 0 ≤ max X 0 := le_max_right _ _
  nlinarith

theorem filIntegerStep : FilIntegerStep := by
  intro νF νE T c φ μ h1 h2 h3
  have hT : (0 : ℝ) ≤ T := by positivity
  have : ((T : ℤ) * νE : ℤ) < νF := by
    have : ((T : ℝ) * νE) < νF := by nlinarith
    exact_mod_cast this
  omega

theorem sFChain : SFChain := by
  intro ξn lam d' ρ φ t p RR T c hξ hl hd hρ hφ hφ2 ht hRR hTc hc1
  have h1 : ξn ^ 2 * lam ^ 2 ≤ d' ^ 2 := by
    have : 0 ≤ ξn * lam := by positivity
    nlinarith
  have hξ2 : 0 < ξn ^ 2 := by positivity

  have h2 : 2 * (RR * (T * c)) * (d' ^ 2 * ρ) < ξn ^ 2 * p := by nlinarith
  have h3 : T * c ≤ RR * (T * c) := by nlinarith
  have h4 : (T * c) * (ξn ^ 2 * lam ^ 2 * ρ) ≤ (RR * (T * c)) * (d' ^ 2 * ρ) := by
    apply mul_le_mul h3 (mul_le_mul_of_nonneg_right h1 hρ) (by positivity) (by nlinarith)
  have h5 : (T * c) * (ξn ^ 2 * φ) ≤ (T * c) * (ξn ^ 2 * (2 * ρ * lam ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφ2 hξ2.le) hTc
  have h6 : ξn ^ 2 * (T * c * φ) < ξn ^ 2 * p := by nlinarith
  exact lt_of_mul_lt_mul_left h6 hξ2.le

end Formalism.LatticeBaseChangeAlt
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LinearIndependentOfIsBaseChange
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem linearIndependent_of_isBaseChange_alt {K K' V V₁ ι : Type} [Field K] [Field K'] [Algebra K K']
    [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁]
    [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j) (v : ι → V)
    (hv : LinearIndependent K v) : LinearIndependent K' (fun i => j (v i)) := by
  classical
  have hs : LinearIndepOn K id (Set.range v) := by
    first
    | exact hv.linearIndepOn_id_range
    | exact (linearIndepOn_id_range_iff hv.injective).mpr hv
  let B := Basis.extend hs
  have hsub : Set.range v ⊆ hs.extend (Set.subset_univ _) := hs.subset_extend (Set.subset_univ _)
  let g : ι → hs.extend (Set.subset_univ _) := fun i => ⟨v i, hsub (Set.mem_range_self i)⟩
  have hg : Function.Injective g := fun a c h => hv.injective (congrArg Subtype.val h)
  have hB' : (fun i => j (v i)) = (hj.basis B) ∘ g := by
    funext i
    first
    | simp [B, g, IsBaseChange.basis_apply, Basis.coe_extend]
    | simp [B, g, Basis.coe_extend]
  rw [hB']
  exact (hj.basis B).linearIndependent.comp g hg

theorem span_image_span_alt {K K' V V₁ : Type} [Field K] [Field K'] [Algebra K K']
    [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁]
    [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁) (s : Set V) :
    Submodule.span K' (j '' (Submodule.span K s : Set V)) = Submodule.span K' (j '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : j x ∈ Submodule.span K (j '' s) := by
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem hx
    exact Submodule.span_le_restrictScalars K K' _ h1
  · first
    | exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
    | exact Submodule.span_mono (Set.image_subset _ Submodule.subset_span)

theorem finrank_span_image_alt : FinrankSpanImage := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj V'
  let b := Module.finBasis K V'
  let w : Fin (finrank K V') → V := V'.subtype ∘ b
  have hw : LinearIndependent K w := b.linearIndependent.map' V'.subtype V'.ker_subtype
  have hspan : Submodule.span K (Set.range w) = V' := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have h1 : Submodule.span K' (j '' (V' : Set V)) =
      Submodule.span K' (Set.range (fun i => j (w i))) := by
    have h2 := span_image_span_alt (K' := K') j (Set.range w)
    rw [hspan] at h2
    rw [h2, ← Set.range_comp]
    rfl
  rw [h1, finrank_span_eq_card (linearIndependent_of_isBaseChange_alt j hj w hw), Fintype.card_fin]

theorem isLattice_span_image_alt : IsLatticeSpanImage := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj M hM
  classical
  unfold Formalism.LatticeIndexTer.IsLat at hM ⊢
  have hsm : ∀ (o : O) (x : V), j (o • x) = (algebraMap O O' o) • j x := by
    intro o x
    rw [← algebraMap_smul K o x, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j x),
      ← algebraMap_smul K' (algebraMap O O' o) (j x), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨⟨S, hS⟩, hM2⟩ := hM
  let P : Submodule O' V₁ := Submodule.span O' (j '' (S : Set V))
  let Q : Submodule O V :=
    { carrier := {x | j x ∈ P}
      add_mem' := fun {a b} ha hb => by
        show j (a + b) ∈ P
        rw [map_add]
        exact P.add_mem ha hb
      zero_mem' := by
        show j 0 ∈ P
        rw [map_zero]
        exact P.zero_mem
      smul_mem' := fun c x hx => by
        show j (c • x) ∈ P
        rw [hsm]
        exact P.smul_mem _ hx }
  have hQ : Submodule.span O (S : Set V) ≤ Q :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩)
  have hNP : Submodule.span O' (j '' (M : Set V)) = P := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [← hS] at hm
      exact hQ hm
    · apply Submodule.span_mono
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, by rw [← hS]; exact Submodule.subset_span hx, rfl⟩
  refine ⟨⟨S.image j, ?_⟩, ?_⟩
  · rw [Finset.coe_image, hNP]
  · rw [Submodule.span_span_of_tower, ← span_image_span_alt (K' := K') j (M : Set V), hM2]
    rw [eq_top_iff, ← (hj.basis (Module.finBasis K V)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨Module.finBasis K V i, Submodule.mem_top, ?_⟩
    first
    | simp [IsBaseChange.basis_apply]
    | simp

end Formalism.LatticeBaseChangeAlt
end
end

