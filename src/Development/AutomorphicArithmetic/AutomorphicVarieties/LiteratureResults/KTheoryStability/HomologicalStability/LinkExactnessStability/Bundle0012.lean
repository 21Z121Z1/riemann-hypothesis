import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0011

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkNilCoordSubspaceUnionTranslate
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem exactAt_uniM_low_union_aff : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactLow R s n →
    ∀ j : ℕ, n ≤ j → ∀ p : ℕ, p + s ≤ n + 1 →
      ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) []) p := by
  intro R _ s n h j hj p hp
  have hsub := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1
  have hlow : ∀ x ∈ low R n, x j = 0 := by
    intro x hx
    have h' : ∀ i, n ≤ i → x i = 0 := hx
    exact h' j hj
  have haff : ∀ x ∈ aff R n j, x j = 1 := by
    intro x hx
    have h' : ∀ i, n ≤ i → (x - Finsupp.single j (1 : R)) i = 0 := hx
    simpa [sub_eq_zero] using h' j hj
  have hφ : ∀ x : ℕ →₀ R, (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) x = x j := fun x => rfl
  refine exactAt_of_links_cone (ℕ →₀ R) (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) [])
    (low R n) (Finsupp.single j 1) ?_ ?_ p ?_
  · intro l hl l' hl'
    obtain ⟨hl1, hl2⟩ := hl
    refine ⟨fun x hx => hl1 x (hl'.subset hx), ?_⟩
    have hl2' : l ∈ uniM R (ℕ →₀ R) := hl2
    exact hsub l hl2' l' hl'
  · intro l hl
    obtain ⟨hl1, hl2, hl3⟩ := hl
    have hl3' : l ∈ uniM R (ℕ →₀ R) := hl3
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · right
        show (Finsupp.single j (1 : R) - Finsupp.single j 1) ∈ low R n
        rw [sub_self]
        exact fun i _ => Finsupp.zero_apply
      · exact hl2 x hx
    · show Finsupp.single j (1 : R) :: l ∈ uniM R (ℕ →₀ R)
      rw [T.cons_mem_uniM_iff_map_sub_smul R (ℕ →₀ R) (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) _ (by rw [hφ]; simp)]
      convert hl3' using 2
      conv_rhs => rw [← List.map_id l]
      apply List.map_congr_left
      intro x hx
      rw [hφ, hlow x (hl1 x hx), zero_smul, sub_zero]
      rfl
  · intro τ hτ x hlast hx hlen
    obtain ⟨hτS, hτU⟩ := hτ
    have hτU' : τ ∈ uniM R (ℕ →₀ R) := hτU
    have hxτ : x ∈ τ := List.mem_of_getLast? hlast
    have hxaff : x ∈ aff R n j := (hτS x hxτ).resolve_left hx
    have hx1 : (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) x = 1 := by rw [hφ]; exact haff x hxaff
    obtain ⟨τ', hτ'U, hlen', heq⟩ := T.linkIn_uniM_eq_shorter_of_form_eq_one R (ℕ →₀ R) (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) (low R n)
      (fun y hy => by rw [hφ]; exact hlow y hy) τ hτU' x hxτ hx1
    have hL : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) []) (low R n) τ
        = linkIn (uniM R (ℕ →₀ R)) (low R n) τ := by
      ext w
      constructor
      · rintro ⟨h1, _, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨h1, ?_, h3⟩
        intro y hy
        have hy' : y ∈ τ ++ w := hy
        rcases List.mem_append.mp hy' with hy | hy
        · exact hτS y hy
        · exact Or.inl (h1 y hy)
    rw [hL, heq]
    exact h τ' hτ'U (p - τ.length) (by omega)

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exactAt_link_nil_coordSubspace_union_translate : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactLow R s n → ∀ j : ℕ, n ≤ j → ∀ p : ℕ, p + s ≤ n + 1 → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) []) p := by
  first
  | exact @GlobalTheory.exactAt_uniM_low_union_aff
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkSuccUnionTranslateOfCoordOne
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem low_aff_subset_succ (R : Type) [CommRing R] (n j : ℕ) :
    low R n ∪ aff R n j ⊆ low R (n + 1) ∪ aff R (n + 1) j := by
  rintro x (hx | hx)
  · exact Or.inl fun i hi => hx i (by omega)
  · exact Or.inr fun i hi => hx i (by omega)

theorem coord_vanish_low_aff (R : Type) [CommRing R] (n j : ℕ) (hj : n + 1 ≤ j) :
    ∀ x ∈ low R n ∪ aff R n j, (Finsupp.lapply n : (ℕ →₀ R) →ₗ[R] R) x = 0 := by
  intro x hx
  rw [Finsupp.lapply_apply]
  rcases hx with hx | hx
  · exact hx n le_rfl
  · have := hx n le_rfl
    simpa [Finsupp.single_apply, show j ≠ n by omega] using this

theorem linkIn_exactAt_of_coord_one : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactAff R s n →
    ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), ∀ v ∈ τ, v n = 1 → ∀ p : ℕ,
    p + s + τ.length ≤ n + 2 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  intro R _ s n h j hj τ hτ v hv hvn p hp
  have hsub : SubClosed (uniM R (ℕ →₀ R)) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1
  have hlenpos := List.length_pos_of_mem hv
  apply exactAt_of_links (ℕ →₀ R) _ (low R n ∪ aff R n j)
  · intro l hl l' hl'
    refine ⟨fun x hx => hl.1 x (hl'.subset hx), hsub _ hl.2 _ ?_⟩
    simpa using hl'
  · intro τ1 hτ1 hlen
    have heq : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ)
        (low R n ∪ aff R n j) τ1 = linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) (τ ++ τ1) := by
      ext w
      constructor
      · rintro ⟨hw, -, h2⟩
        refine ⟨hw, ?_⟩
        rw [List.append_assoc]
        exact h2
      · rintro ⟨hw, h2⟩
        refine ⟨hw, fun x hx => ?_, ?_⟩
        · rcases List.mem_append.mp hx with hx | hx
          · exact hτ1.1 x hx
          · exact low_aff_subset_succ R n j (hw x hx)
        · rw [← List.append_assoc]
          exact h2
    rw [heq]
    obtain ⟨τ', hτ', hl', heq'⟩ := T.linkIn_uniM_eq_shorter_of_form_eq_one R (ℕ →₀ R) (Finsupp.lapply n) (low R n ∪ aff R n j)
      (coord_vanish_low_aff R n j hj) (τ ++ τ1) hτ1.2 v (List.mem_append_left _ hv)
      (by rw [Finsupp.lapply_apply]; exact hvn)
    rw [heq']
    rw [List.length_append] at hl'
    exact h j (by omega) τ' hτ' (p - τ1.length) (by omega)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exactAt_link_succ_union_translate_of_coord_one : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), ∀ v ∈ τ, v n = 1 → ∀ p : ℕ, p + s + τ.length ≤ n + 2 → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  first
  | exact @GlobalTheory.SeqCx.linkIn_exactAt_of_coord_one
  | exact @GlobalTheory.SeqCx.coord_vanish_low_aff
  | exact @GlobalTheory.SeqCx.low_aff_subset_succ
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.LinkExactLowAddOneOfLinkExactAff
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem low_union_aff_subset_low_succ (R : Type) [CommRing R] (n : ℕ) :
    low R n ∪ aff R n n ⊆ low R (n + 1) := by
  intro x hx
  rcases hx with hx | hx
  · intro i hi
    exact hx i (by omega)
  · intro i hi
    have := hx i (by omega)
    simpa [Finsupp.single_apply, show n ≠ i by omega] using this

theorem linkExactLow_succ_of_linkExactAff : ∀ (R : Type) [CommRing R] (s n : ℕ),
    LinkExactAff R s n → LinkExactLow R s (n + 1) := by
  intro R _ s n h τ hτ p hp
  have hsub : SubClosed (uniM R (ℕ →₀ R)) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1
  apply exactAt_of_links (ℕ →₀ R) _ (low R n ∪ aff R n n)
  · intro l hl l' hl'
    refine ⟨fun x hx => hl.1 x (hl'.subset hx), hsub _ hl.2 _ ?_⟩
    simpa using hl'
  · intro τ1 hτ1 hlen
    have heq : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1)) τ) (low R n ∪ aff R n n) τ1 =
        linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n n) (τ ++ τ1) := by
      ext w
      constructor
      · rintro ⟨hw, -, h2⟩
        refine ⟨hw, ?_⟩
        rw [List.append_assoc]
        exact h2
      · rintro ⟨hw, h2⟩
        refine ⟨hw, fun x hx => ?_, ?_⟩
        · rcases List.mem_append.mp hx with hx | hx
          · exact hτ1.1 x hx
          · exact low_union_aff_subset_low_succ R n (hw x hx)
        · rw [← List.append_assoc]
          exact h2
    rw [heq]
    exact h n le_rfl (τ ++ τ1) hτ1.2 (p - τ1.length) (by rw [List.length_append]; omega)

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.linkExactLow_add_one_of_linkExactAff : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactAff R s n → LinkExactLow R s (n + 1) := by
  first
  | exact @GlobalTheory.linkExactLow_succ_of_linkExactAff
  | exact @GlobalTheory.low_union_aff_subset_low_succ
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSeqFormsKillUniSeqExactAt
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx

theorem exactAt_split_kill_uni : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ,
    (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') →
    ∀ (a : ℕ) (w : List (Fin n → R)), w ∈ uniSeq R n → 1 ≤ w.length →
    2 * a + w.length + s + 1 ≤ n →
    ExactAt {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} a := by
  intro R _ s hs n hind a w hw hw1 hlen
  obtain ⟨hsubS, -, -, huni⟩ := T.subClosed_splitSeq_and_uniSeq_with_mem_iff R n
  obtain ⟨γ, hγ, hγw⟩ := (huni w).mp hw
  subst hγw
  rw [List.length_map] at hw1 hlen
  have hF : {σ : List ((Fin n → R) × (Fin n → R)) |
      σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ u ∈ List.map Prod.fst γ, y.2 ⬝ᵥ u = 0} =
      {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0} := by
    ext σ
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun y hy z hz => h2 y hy z.1 (List.mem_map.mpr ⟨z, hz, rfl⟩)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun y hy u hu => ?_⟩
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
      exact h2 y hy z hz
  rw [hF]
  refine T.seqComplex_exactAt_of_all_links_exactAt _ _ {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ γ, z.2 ⬝ᵥ y.1 = 0} ?_ a ?_
  · intro l hl l' hl'
    exact ⟨hsubS l hl.1 l' hl', fun y hy z hz => hl.2 y (hl'.subset hy) z hz⟩
  · intro σ hσ hσlen
    obtain ⟨ρ, hρ, hρlen, hlink⟩ := T.exists_splitSeq_linkIn_orthogonal_eq_linkIn R n γ σ hγ hσ.1 hσ.2
    rw [hlink]
    exact T.exactAt_linkIn_splitSeq_of_exactAt_splitSeq R s hs n (n - ρ.length) (a - σ.length) ρ hρ (by omega) (by omega)
      (hind (n - ρ.length) (by omega) (a - σ.length) (by omega))

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.splitSeq_forms_kill_uniSeq_exactAt : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') → ∀ (a : ℕ) (w : List (Fin n → R)), w ∈ uniSeq R n → 1 ≤ w.length → 2 * a + w.length + s + 1 ≤ n → ExactAt {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} a := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_split_kill_uni
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSequenceRepComplexExact
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab.SplitEx

theorem main : ∀ (R : Type) [CommRing R] (n : ℕ), (∀ p, splitD R n (p + 1) ≫ splitD R n p = 0) ∧
    (ExactAt (splitSeq R n) 0 → Function.Surjective (splitD R n 0).hom) ∧
    ∀ p, ExactAt (splitSeq R n) (p + 1) → Function.Exact (splitD R n (p + 1)).hom (splitD R n p).hom := by
  intro R _ n
  have key := T.splitSet_permRep_chains_iso_splitSeq_chains R n
  have hzero : ∀ p (x : SplitSet R n (p + 1 + 1) →₀ ℤ),
      (splitD R n p).hom ((splitD R n (p + 1)).hom x) = 0 := by
    intro p x
    apply (key p).1
    have h1 := (key p).2.2 ((splitD R n (p + 1)).hom x)
    have h2 := (key (p + 1)).2.2 x
    rw [h2, T.seqChain_boundary_comp_boundary_apply] at h1
    exact h1.trans (Finsupp.mapDomain_zero
      (f := (Subtype.val : SplitSet R n p → List ((Fin n → R) × (Fin n → R)))) (M := ℤ)).symm
  refine ⟨fun p => ?_, fun h0 => ?_, fun p hp => ?_⟩
  · ext c a
    simp [hzero]
  · intro (y : SplitSet R n 0 →₀ ℤ)
    have hy : Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y
        ∈ chains (splitSeq R n) 0 := by
      rw [← (key 0).2.1]
      exact LinearMap.mem_range.mpr ⟨y, rfl⟩
    have hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y) = 0 := by
      have hsup : ↑(Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y).support
          ⊆ {l | l ∈ splitSeq R n ∧ l.length = 0} := (Finsupp.mem_supported ℤ _).mp hy
      rw [bd, Finsupp.linearCombination_apply, Finsupp.sum]
      apply Finset.sum_eq_zero
      intro l hl
      have hlen : l.length = 0 := (hsup hl).2
      simp [hlen]
    obtain ⟨b, hb, hbeq⟩ := h0 _ hy hbd
    have hb' : b ∈ LinearMap.range
        (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n 1 → List ((Fin n → R) × (Fin n → R)))) := by
      rw [(key 1).2.1]
      exact hb
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hb'
    refine ⟨x, (key 0).1 ?_⟩
    exact ((key 0).2.2 x).trans hbeq
  · intro (y : SplitSet R n (p + 1) →₀ ℤ)
    constructor
    · intro hy0
      have hy : Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y
          ∈ chains (splitSeq R n) (p + 1) := by
        rw [← (key (p + 1)).2.1]
        exact LinearMap.mem_range.mpr ⟨y, rfl⟩
      have hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y) = 0 := by
        have h1 := (key p).2.2 y
        rw [hy0] at h1
        exact h1.symm.trans Finsupp.mapDomain_zero
      obtain ⟨b, hb, hbeq⟩ := hp _ hy hbd
      have hb' : b ∈ LinearMap.range
          (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n (p + 1 + 1) → List ((Fin n → R) × (Fin n → R)))) := by
        rw [(key (p + 1 + 1)).2.1]
        exact hb
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hb'
      refine ⟨x, (key (p + 1)).1 ?_⟩
      exact ((key (p + 1)).2.2 x).trans hbeq
    · rintro ⟨x, rfl⟩
      exact hzero p x

end GlobalTheory.HomStab.SplitEx

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.splitSequence_rep_complex_exact : ∀ (R : Type) [CommRing R] (n : ℕ), (∀ p, splitD R n (p + 1) ≫ splitD R n p = 0) ∧ (ExactAt (splitSeq R n) 0 → Function.Surjective (splitD R n 0).hom) ∧ ∀ p, ExactAt (splitSeq R n) (p + 1) → Function.Exact (splitD R n (p + 1)).hom (splitD R n p).hom := by
  first
  | exact @GlobalTheory.HomStab.SplitEx.main
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.StandardSeqPointCompSplitSeqDifferential
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem altSum_neg_one (p : ℕ) : (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ)) = if Even p then 1 else 0 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    rcases Nat.even_or_odd p with hp | hp
    · have h2 : ¬ Even (p + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hp
      rw [if_pos hp, if_neg h2, pow_succ, hp.neg_one_pow]
      norm_num
    · have h2 : Even (p + 1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.mpr hp
      rw [if_neg (Nat.not_even_iff_odd.mpr hp), if_pos h2, pow_succ, hp.neg_one_pow]
      norm_num

theorem stab_comp_stab (R : Type) [CommRing R] (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (hac : a ≤ c) :
    (stab R b c hbc).comp (stab R a b hab) = stab R a c hac := by
  ext g i j
  simp only [MonoidHom.comp_apply, stab, Units.coe_map, padHom, MonoidHom.coe_mk, OneHom.coe_mk, padMat, Matrix.of_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> simp_all [Fin.ext_iff] <;> omega

theorem ptH_comp_hMap_splitD : ∀ (R : Type) [CommRing R] (n p q : ℕ) (h : p + 1 ≤ n) (h₁ : ∀ x, stab R (n - (p + 1)) n (Nat.sub_le _ _) x • stdSeq R n (p + 1) h = stdSeq R n (p + 1) h) (h₀ : ∀ x, stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p (by omega) = stdSeq R n p (by omega)), ptH ℤ (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stdSeq R n (p + 1) h) h₁ q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ ptH ℤ (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q else 0 := by
  intro R _ n p q h h₁ h₀
  have hσ : (stab R (n - p) n (Nat.sub_le _ _)).comp (stab R (n - (p + 1)) (n - p) (by omega)) =
      stab R (n - (p + 1)) n (Nat.sub_le _ _) := stab_comp_stab R _ _ _ _ _ _
  unfold splitD
  rw [(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.2 _ Finset.univ, Preadditive.comp_sum]
  rw [Finset.sum_congr rfl (g := fun i : Fin (p + 1) => ((-1 : ℤ) ^ (i : ℕ)) •
      (grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫
        ptH ℤ (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q)) ?_]
  · rw [← Finset.sum_smul, altSum_neg_one]
    split_ifs <;> simp
  · intro i _
    rw [(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.1, Preadditive.comp_zsmul]
    obtain ⟨g, hg, hc⟩ := GlobalTheory.T.face_stdSeq_GL_conjugate_commuting_stab R n p h i
    rw [GlobalTheory.HomStab.ptH_comp_permMap_eq ℤ _ _ _ _ _ (stab R (n - p) n (Nat.sub_le _ _))
      (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stab R (n - (p + 1)) (n - p) (by omega))
      _ h₁ _ h₀ (face R n p i) _ g hσ hg hc q]
    rfl

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.standardSeqPoint_comp_splitSeqDifferential : ∀ (R : Type) [CommRing R] (n p q : ℕ) (h : p + 1 ≤ n) (h₁ : ∀ x, stab R (n - (p + 1)) n (Nat.sub_le _ _) x • stdSeq R n (p + 1) h = stdSeq R n (p + 1) h) (h₀ : ∀ x, stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p (by omega) = stdSeq R n p (by omega)), ptH ℤ (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stdSeq R n (p + 1) h) h₁ q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ ptH ℤ (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q else 0 := by
  first
  | exact @GlobalTheory.HomStab.ptH_comp_hMap_splitD
  | exact @GlobalTheory.HomStab.stab_comp_stab
  | exact @GlobalTheory.HomStab.altSum_neg_one
end
end

