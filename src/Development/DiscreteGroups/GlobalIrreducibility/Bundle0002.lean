import Mathlib

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGenLin
section
namespace DiscreteGroups.sglob.DzType

theorem exists_functional_of_finite {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (N : Set G) (θ : G → ℂ) (v : X)
    (h : ∀ F : Finset G, (↑F ⊆ N) →
      ∃ Λ : Module.Dual ℂ X, (∀ u ∈ F, ∀ x, Λ (ρ u x) = θ u * Λ x) ∧ Λ v ≠ 0) :
    ∃ l : Module.Dual ℂ X, (∀ u ∈ N, ∀ x, l (ρ u x) = θ u * l x) ∧ l v ≠ 0 := by
  classical
  set S : Set X := {y | ∃ u ∈ N, ∃ x, y = ρ u x - θ u • x} with hSdef
  set T : Submodule ℂ X := Submodule.span ℂ S with hTdef
  have hv : v ∉ T := by
    intro hvT
    obtain ⟨A, hA, hvA⟩ := Submodule.mem_span_finite_of_mem_span hvT
    let f : X → G := fun t => if h : ∃ u ∈ N, ∃ x, t = ρ u x - θ u • x then h.choose else 1
    have hf : ∀ t ∈ A, f t ∈ N ∧ ∃ x, t = ρ (f t) x - θ (f t) • x := by
      intro t ht
      have h' : ∃ u ∈ N, ∃ x, t = ρ u x - θ u • x := hA ht
      simp only [f, dif_pos h']
      exact ⟨h'.choose_spec.1, h'.choose_spec.2⟩
    obtain ⟨Λ, hΛ, hΛv⟩ := h (A.image f) (by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      exact (hf t ht).1)
    apply hΛv
    have hle : Submodule.span ℂ (↑A : Set X) ≤ LinearMap.ker Λ := by
      rw [Submodule.span_le]
      intro t ht
      obtain ⟨-, x, hx⟩ := hf t ht
      rw [SetLike.mem_coe, LinearMap.mem_ker, hx, map_sub, map_smul,
        hΛ _ (Finset.mem_image_of_mem f ht) x, smul_eq_mul, sub_self]
    exact hle hvA
  have hq : T.mkQ v ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (X ⧸ T), φ (T.mkQ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  refine ⟨φ ∘ₗ T.mkQ, fun u hu x => ?_, hφ⟩
  have hmem : ρ u x - θ u • x ∈ T := Submodule.subset_span ⟨u, hu, x, rfl⟩
  have h0 : (φ ∘ₗ T.mkQ) (ρ u x - θ u • x) = 0 := by
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T).2 hmem, map_zero]
  set l := φ ∘ₗ T.mkQ
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0

end DiscreteGroups.sglob.DzType
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ValuationUnitriLt
section
namespace DiscreteGroups.sglob.DzType

open Matrix

theorem valuation_unitri_lt {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m : ℕ}
    (L U : Matrix (Fin m) (Fin m) K) (hL : ∀ i j, i < j → L i j = 0) (hU1 : ∀ i, U i i = 1)
    (hU0 : ∀ i j, j < i → U i j = 0) (hX : ∀ i j, v ((L * U) i j) ≤ 1) (hXd : ∀ i, v ((L * U) i i) = 1)
    (hXu : ∀ i j, i < j → v ((L * U) i j) < 1) : ∀ i j, i < j → v (U i j) < 1 := by
  classical
  have mlt : ∀ a b : Γ, a ≤ 1 → b < 1 → a * b < 1 := fun a b ha hb =>
    lt_of_le_of_lt (show a * b ≤ b from (by gcongr : a * b ≤ 1 * b).trans_eq (one_mul b)) hb
  have split : ∀ (i c a : Fin m), (L * U) i c = L i a * U a c + ∑ l ∈ Finset.univ.erase a, L i l * U l c := by
    intro i c a
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have key : ∀ n : ℕ, ∀ i : Fin m, i.val = n → ∀ j, i < j → v (U i j) < 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hin
      have up : ∀ l : Fin m, l < i → ∀ j, l < j → v (U l j) < 1 := fun l hl j hlj =>
        ih l.val (by rw [← hin]; exact hl) l rfl j hlj
      have hLi : ∀ p : ℕ, ∀ l : Fin m, l.val = p → l < i → v (L i l) ≤ 1 := by
        intro p
        induction p using Nat.strong_induction_on with
        | _ p ihp =>
          intro l hlp hli
          have hR : v (∑ l' ∈ Finset.univ.erase l, L i l' * U l' l) < 1 := by
            refine Valuation.map_sum_lt v one_ne_zero fun l' hl' => ?_
            have hne : l' ≠ l := Finset.ne_of_mem_erase hl'
            rcases lt_or_gt_of_ne hne with h | h
            · rw [map_mul]
              exact mlt _ _ (ihp l'.val (by rw [← hlp]; exact h) l' rfl (h.trans hli))
                (up l' (h.trans hli) l h)
            · rw [hU0 l' l h, mul_zero, map_zero]; exact zero_lt_one
          have hs := split i l l
          rw [hU1, mul_one] at hs
          have e : L i l = (L * U) i l - ∑ l' ∈ Finset.univ.erase l, L i l' * U l' l := by rw [hs]; ring
          rw [e]
          exact (Valuation.map_sub v _ _).trans (max_le (hX i l) hR.le)
      have hR : ∀ c, (∀ l', l' < i → v (U l' c) < 1) →
          v (∑ l' ∈ Finset.univ.erase i, L i l' * U l' c) < 1 := by
        intro c hc
        refine Valuation.map_sum_lt v one_ne_zero fun l' hl' => ?_
        have hne : l' ≠ i := Finset.ne_of_mem_erase hl'
        rcases lt_or_gt_of_ne hne with h | h
        · rw [map_mul]
          exact mlt _ _ (hLi l'.val l' rfl h) (hc l' h)
        · rw [hL i l' h, zero_mul, map_zero]; exact zero_lt_one
      have hLii : v (L i i) = 1 := by
        have hs := split i i i
        rw [hU1, mul_one] at hs
        have hr := hR i (fun l' h => up l' h i h)
        have e : L i i = (L * U) i i - ∑ l' ∈ Finset.univ.erase i, L i l' * U l' i := by rw [hs]; ring
        refine le_antisymm ?_ ?_
        · rw [e]; exact (Valuation.map_sub v _ _).trans (max_le (hX i i) hr.le)
        · by_contra hlt
          push Not at hlt
          have h2 := Valuation.map_add v (L i i) (∑ l' ∈ Finset.univ.erase i, L i l' * U l' i)
          rw [← hs, hXd i] at h2
          exact absurd (h2.trans_lt (max_lt hlt hr)) (lt_irrefl 1)
      intro j hij
      have hs := split i j i
      have hr := hR j (fun l' h => up l' h j (h.trans hij))
      have h1 : v (L i i * U i j) < 1 := by
        have e : L i i * U i j = (L * U) i j - ∑ l' ∈ Finset.univ.erase i, L i l' * U l' j := by rw [hs]; ring
        rw [e]
        exact (Valuation.map_sub v _ _).trans_lt (max_lt (hXu i j hij) hr)
      rwa [map_mul, hLii, one_mul] at h1
  intro i j hij
  exact key i.val i rfl j hij

end DiscreteGroups.sglob.DzType
end

