import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenMulLeftImageLattice
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem finite_quot_span_of_ne_zero (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have h1 : Ideal.span {c} = IsLocalRing.maximalIdeal O ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow, hu,
      Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [h1]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

theorem finite_between_mulLat (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L)
    (c : K.O) (hc : c ≠ 0) :
    {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  haveI := finite_quot_span_of_ne_zero K.O c hc
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  have hfg : (⊤ : Submodule K.O L).FG := Module.Finite.fg_top
  set S : Submodule K.O L := Ideal.span {c} • (⊤ : Submodule K.O L) with hS
  haveI : Finite (L ⧸ S) := Submodule.finite_quotient_smul _ hfg
  haveI : Finite (Submodule K.O (L ⧸ S)) :=
    Finite.of_injective (fun P : Submodule K.O (L ⧸ S) => (P : Set (L ⧸ S))) SetLike.coe_injective
  let f : Submodule K.O B.A → Submodule K.O (L ⧸ S) := fun M => (M.comap L.subtype).map S.mkQ
  have hSle : ∀ M : Submodule K.O B.A, mulLat K.O (algebraMap K.O B.A c) L ≤ M → S ≤ M.comap L.subtype := by
    intro M hM
    rw [hS, Submodule.smul_le]
    intro r hr x _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have hx : algebraMap K.O B.A c * (x : B.A) ∈ M := hM ⟨x, x.2, rfl⟩
    have : ((a * c) • x : L) = (a • (algebraMap K.O B.A c * (x : B.A)) : B.A) := by
      rw [Submodule.coe_smul, ← Algebra.smul_def, smul_smul]
    rw [Submodule.mem_comap, Submodule.subtype_apply, this]
    exact M.smul_mem a hx
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M₁ h₁ M₂ h₂ heq
  have e1 : M₁.comap L.subtype = M₂.comap L.subtype := by
    have := congrArg (Submodule.comap S.mkQ) heq
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.2 (hSle M₁ h₁.1), sup_eq_right.2 (hSle M₂ h₂.1)] at this
  have e2 := congrArg (Submodule.map L.subtype) e1
  rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 h₁.2,
    inf_eq_right.2 h₂.2] at e2

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenSmulAndSelfStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  first | exact @GlobalTheory.finite_submodules_between_smul_and_self | exact GlobalTheory.finite_submodules_between_smul_and_self | (intros; apply GlobalTheory.finite_submodules_between_smul_and_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddFinrankLeFinrankInfComapSubIdStatement
section
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_inf_comap_sub_id' : ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  first | exact @GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | exact GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | (intros; apply GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddLeFinrankRangeAddOfComapLeStatement
section
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  first | exact @GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | exact GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | (intros; apply GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInvariantsEqOfInvertiblePeriodMatrixStatement
section
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by
  first | exact @GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | exact GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | (intros; apply GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKerMapLeOfFirstOrderKernelExtStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_ker_map_le_of_first_order_kernel_ext : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (a e : ℕ) (Φ : Matrix (Fin a) (Fin a) k) (U : Type) [AddCommGroup U] [Module k U] [Module.Finite k U] (t u : LinearMap.ker Φ.mulVecLin →ₗ[k] U), (∀ x0 x1 : Fin (e + 1) → LinearMap.ker Φ.mulVecLin, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → Module.finrank K (LinearMap.ker (Φ.map (algebraMap k K)).mulVecLin) ≤ Module.finrank k U + e := by
  first | exact @GlobalTheory.finrank_ker_map_le_of_first_order_kernel | exact GlobalTheory.finrank_ker_map_le_of_first_order_kernel | (intros; apply GlobalTheory.finrank_ker_map_le_of_first_order_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSpanImageEqCard
section
open Module

namespace GlobalTheory.Per.Sen

theorem finrank_span_image_eq_card {L M : Type} [Field L] [AddCommGroup M] [Module L M] {m : ℕ}
    (d : Fin m → M) (hd : LinearIndependent L d) (p : Fin m → Prop) [DecidablePred p] :
    Module.finrank L (Submodule.span L (d '' {i | p i})) = (Finset.univ.filter p).card := by
  have h := finrank_span_eq_card (hd.comp (Subtype.val : {i // p i} → Fin m) Subtype.val_injective)
  rw [Fintype.card_subtype] at h
  rw [show d '' {i | p i} = Set.range (d ∘ (Subtype.val : {i // p i} → Fin m)) by
    ext x; simp [Set.mem_image, Set.mem_range]]
  exact h

private theorem exists_eq_of_antitone_le_of_exhaustive {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M) (hA : Antitone A)
    (hAD : ∀ a, A a ≤ D) (hex : ∀ x ∈ D, ∃ a, x ∈ A a) : ∃ a, A a = D := by
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional D).mpr inferInstance
  have key : ∀ T : Finset M, (T : Set M) ⊆ D → ∃ a, ∀ x ∈ T, x ∈ A a := by
    intro T
    classical
    refine Finset.induction_on T ?_ ?_
    · intro _; exact ⟨0, by simp⟩
    · intro y T _ ih hT
      obtain ⟨a, ha⟩ := ih (fun z hz => hT (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hz)))
      obtain ⟨b, hb⟩ := hex y (hT (Finset.mem_coe.mpr (Finset.mem_insert_self y T)))
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hA (min_le_right a b) hb
      · exact hA (min_le_left a b) (ha x hx)
  obtain ⟨a, ha⟩ := key S (by rw [← hS]; exact Submodule.subset_span)
  refine ⟨a, le_antisymm (hAD a) ?_⟩
  rw [← hS, Submodule.span_le]
  exact fun x hx => ha x hx

private theorem exists_adapted_basis_of_finrank_jumps {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (r : ℕ) : ∀ (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M)
    (U : Multiset ℤ), Module.finrank L D = r → Antitone A → (∀ a, A a ≤ D) →
    (∀ x ∈ D, ∃ a, x ∈ A a) → (∀ x, (∀ a, x ∈ A a) → x = 0) →
    (∀ a : ℤ, (Module.finrank L (A a) : ℤ) - Module.finrank L (A (a + 1)) = (U.count a : ℤ)) →
    ∃ (u : Fin r → ℤ) (d : Fin r → M), Finset.univ.val.map u = U ∧ LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k}) := by
  induction r with
  | zero =>
    intro D _ A U hr hA hAD hex hsep hU
    have hD : D = ⊥ := Submodule.finrank_eq_zero.mp hr
    have hA0 : ∀ a, A a = ⊥ := fun a => le_bot_iff.mp (hD ▸ hAD a)
    have hU0 : U = 0 := by
      ext a
      have h := hU a
      rw [hA0 a, hA0 (a + 1), finrank_bot] at h
      rw [Multiset.count_zero]
      push_cast at h
      omega
    refine ⟨Fin.elim0, Fin.elim0, by simp [hU0], linearIndependent_empty_type, fun a => ?_⟩
    rw [hA0 a]; symm
    rw [Submodule.span_eq_bot]
    rintro x ⟨k, -, -⟩
    exact k.elim0
  | succ r ih =>
    intro D _ A U hr hA hAD hex hsep hU
    classical
    obtain ⟨a0, ha0⟩ := exists_eq_of_antitone_le_of_exhaustive D A hA hAD hex
    have hDne : D ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hr; omega
    obtain ⟨w, hwD, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hDne
    obtain ⟨b, hb⟩ : ∃ b, w ∉ A b := by
      by_contra h; push Not at h; exact hw0 (hsep w h)
    have hbd : ∀ a, A a = D → a < b := by
      intro a ha; by_contra h; push Not at h
      exact hb (hA h (by rw [ha]; exact hwD))
    obtain ⟨s, hs, hsmax⟩ :=
      Int.exists_greatest_of_bdd ⟨b, fun z hz => (hbd z hz).le⟩ ⟨a0, ha0⟩
    have hBD : A (s + 1) < D :=
      lt_of_le_of_ne (hAD _) (fun h => by have := hsmax _ h; omega)
    obtain ⟨v, hvD, hvB⟩ := SetLike.exists_of_lt hBD
    have hv0 : v ≠ 0 := fun h => hvB (by rw [h]; exact Submodule.zero_mem _)
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (A (s + 1) ⊔ Submodule.span L {v})
    obtain ⟨D', hD'⟩ : ∃ D' : Submodule L M, D' = A (s + 1) ⊔ (C ⊓ D) := ⟨_, rfl⟩
    have hED : A (s + 1) ⊔ Submodule.span L {v} ≤ D :=
      sup_le (hAD _) ((Submodule.span_singleton_le_iff_mem _ _).mpr hvD)
    have hD'D : D' ≤ D := by rw [hD']; exact sup_le (hAD _) inf_le_right
    have hBD' : A (s + 1) ≤ D' := by rw [hD']; exact le_sup_left
    have hvD' : v ∉ D' := by
      intro hv
      rw [hD'] at hv
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
      have hzE : z ∈ A (s + 1) ⊔ Submodule.span L {v} := by
        have : z = v - y := by rw [← hyz]; abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
          (Submodule.mem_sup_left hy)
      have hz0 : z = 0 := (Submodule.disjoint_def.mp hC.disjoint) z hzE hz.1
      apply hvB; rw [← hyz, hz0, add_zero]; exact hy
    have hsup : D' ⊔ Submodule.span L {v} = D := by
      rw [hD', sup_right_comm, ← sup_inf_assoc_of_le _ hED, hC.sup_eq_top, top_inf_eq]
    have hinf : D' ⊓ Submodule.span L {v} = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx2
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd ((Submodule.smul_mem_iff _ hc).mp hx1) hvD'
    have : FiniteDimensional L D' := Submodule.finiteDimensional_of_le hD'D
    have : FiniteDimensional L (Submodule.span L {v}) :=
      FiniteDimensional.span_of_finite L (Set.finite_singleton v)
    have hrD' : Module.finrank L D' = r := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq D' (Submodule.span L {v})
      rw [hsup, hinf, finrank_bot, finrank_span_singleton hv0, hr] at h
      omega
    have hlow : ∀ a, a ≤ s → A a = D := fun a ha =>
      le_antisymm (hAD a) (by rw [← hs]; exact hA ha)
    have hs_mem : 0 < U.count s := by
      have h := hU s
      rw [hs, hr] at h
      have := Submodule.finrank_lt_finrank_of_lt hBD
      rw [hr] at this
      omega
    have hU' : ∀ a : ℤ, (Module.finrank L ↥(A a ⊓ D') : ℤ) -
        Module.finrank L ↥(A (a + 1) ⊓ D') = ((U.erase s).count a : ℤ) := by
      intro a
      rcases lt_trichotomy a s with h | h | h
      · have h0 := hU a
        rw [hlow a h.le, hlow (a + 1) (by omega)] at h0
        rw [hlow a h.le, hlow (a + 1) (by omega), inf_eq_right.mpr hD'D,
          Multiset.count_erase_of_ne h.ne]
        omega
      · rw [h]
        have h0 := hU s
        rw [hs, hr] at h0
        rw [hs, inf_eq_right.mpr hD'D, inf_eq_left.mpr hBD', Multiset.count_erase_self, hrD',
          Nat.cast_sub hs_mem, Nat.cast_one]
        push_cast at h0 ⊢
        omega
      · rw [inf_eq_left.mpr ((hA (show s + 1 ≤ a by omega)).trans hBD'),
          inf_eq_left.mpr ((hA (show s + 1 ≤ a + 1 by omega)).trans hBD'),
          Multiset.count_erase_of_ne h.ne']
        exact hU a
    obtain ⟨u', d', hu', hd', hspan'⟩ := ih D' (fun a => A a ⊓ D') (U.erase s) hrD'
      (fun a b h => inf_le_inf_right _ (hA h)) (fun a => inf_le_right)
      (fun x hx => by obtain ⟨a, ha⟩ := hex x (hD'D hx); exact ⟨a, Submodule.mem_inf.mpr ⟨ha, hx⟩⟩)
      (fun x hx => hsep x (fun a => (Submodule.mem_inf.mp (hx a)).1)) hU'
    have hd'D' : ∀ k, d' k ∈ D' := by
      intro k
      have h := hspan' (u' k)
      have hk : d' k ∈ Submodule.span L (d' '' {j | u' k ≤ u' j}) :=
        Submodule.subset_span ⟨k, le_refl (u' k), rfl⟩
      rw [← h] at hk
      exact (Submodule.mem_inf.mp hk).2
    refine ⟨Fin.cons s u', Fin.cons v d', ?_, ?_, ?_⟩
    · rw [Fin.univ_val_map, List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Multiset.cons_coe, ← Fin.univ_val_map, hu']
      exact Multiset.cons_erase (Multiset.count_pos.mp hs_mem)
    · refine linearIndependent_finCons.mpr ⟨hd', fun hv => hvD' ?_⟩
      exact (Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hd'D' k)) hv
    · intro a
      by_cases has : a ≤ s
      · rw [hlow a has]
        apply le_antisymm
        · rw [← hsup, sup_le_iff]
          constructor
          · have h := hspan' a
            rw [hlow a has, inf_eq_right.mpr hD'D] at h
            rw [h]
            apply Submodule.span_mono
            rintro _ ⟨j, hj, rfl⟩
            exact ⟨j.succ, by simpa using hj, by simp⟩
          · rw [Submodule.span_le, Set.singleton_subset_iff]
            exact Submodule.subset_span ⟨0, by simpa using has, by simp⟩
        · rw [Submodule.span_le]
          rintro _ ⟨k, -, rfl⟩
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simpa using hvD
          · simpa using hD'D (hd'D' j)
      · push Not at has
        have h := hspan' a
        rw [inf_eq_left.mpr ((hA (show s + 1 ≤ a by omega)).trans hBD')] at h
        rw [h]
        congr 1
        ext x
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.succ, by simpa using hj, by simp⟩
        · rintro ⟨k, hk, rfl⟩
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simp at hk; omega
          · exact ⟨j, by simpa using hk, by simp⟩

theorem adapted_basis_jumps : ∀ {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M) (U : Multiset ℤ) (r : ℕ),
    Module.finrank L D = r → Antitone A → (∀ a, A a ≤ D) → (∀ x ∈ D, ∃ a, x ∈ A a) →
    (∀ x, (∀ a, x ∈ A a) → x = 0) →
    (∀ a : ℤ, (Module.finrank L (A a) : ℤ) - Module.finrank L (A (a + 1)) = (U.count a : ℤ)) →
    ∃ (u : Fin r → ℤ) (d : Fin r → M), Finset.univ.val.map u = U ∧ LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k}) := by
  intro L M _ _ _ D _ A U r hr hA hAD hex hsep hU
  exact exists_adapted_basis_of_finrank_jumps r D A U hr hA hAD hex hsep hU

end GlobalTheory.Per.Sen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumOrbitsCountingPrincipleFiniteFibresStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  first | exact @GlobalTheory.OrbitCounting.counting_principle | exact GlobalTheory.OrbitCounting.counting_principle | (intros; apply GlobalTheory.OrbitCounting.counting_principle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProdStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_finsupp_compl_prod_eq : ∀ {I : Type} (S : Finset I) (n : ℕ),
    ∃ e : {l : I →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0} ≃ ({i : I // i ∉ S} →₀ (Fin n → ℤ)),
      ∀ (M : Type) [CommMonoid M] (r : I → (Fin n → ℤ) → M), (∀ i, r i 0 = 1) →
        ∀ l, (e l).prod (fun i v => r i.1 v) = l.1.prod r := by
  first | exact @GlobalTheory.finsupp_vanishing_on_equiv_compl_prod | exact GlobalTheory.finsupp_vanishing_on_equiv_compl_prod | (intros; apply GlobalTheory.finsupp_vanishing_on_equiv_compl_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameTranslateLatticeCosetSubsetStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_translate_lattice_coset_subset : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g g' : GL (Fin r) K) (z z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → x * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) → ∀ (y : Matrix (Fin r ⊕ Fin t) (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), y * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) → ∃ w' : Matrix (Fin r ⊕ Fin t) (Fin r) O, y * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w').map (algebraMap O K) := by
  first | exact @GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset | exact GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset | (intros; apply GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeModuleAdicCompleteSeparatedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_finite_module_adicComplete_and_separated : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → (∀ a : R, (∀ n : ℕ, ∃ b : R, a = ϖ ^ n * b) → a = 0) → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M], (∀ x : ℕ → M, ∃ y : M, ∀ n : ℕ, ∃ z : M, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) ∧ (∀ m : M, (∀ n : ℕ, ∃ z : M, m = ϖ ^ n • z) → m = 0) := by
  first | exact @GlobalTheory.freeModule_adicComplete_separated | exact GlobalTheory.freeModule_adicComplete_separated | (intros; apply GlobalTheory.freeModule_adicComplete_separated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefectStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect : ∀ (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R) (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R), (∀ x : R, lr * x = 0 → x = 0) → (∃ v : Rˣ, e = lr * v) → (∃ v : Rˣ, e₀ = lr * v) → (∀ x, φ (σ x) = σ (φ x)) → φ lr = lr → σ lr = lr → σ e₀ = e₀ → A₀.map σ = A₀ → Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) → B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ) → e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ) → e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) = A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  first | (exact @GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (exact GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (intros; apply GlobalTheory.FrobeniusDefect.frobenius_defect_eq  <;> assumption)
end

