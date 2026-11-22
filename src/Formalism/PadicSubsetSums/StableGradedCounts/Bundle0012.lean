import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0011

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.FrobeniusDifferenceDividedPower
section
namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

theorem sqrt_neg_in_cyclotomic_field : SqrtNegInCyclotomic := by
  intro l hl h4 F _ ζ hζ
  have := Fact.mk hl
  by_cases h2 : (2 : F) = 0
  · have h1 : (l : F) = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, l = 2 * k + 1 := ⟨l / 2, by omega⟩
      rw [hk]; push_cast; rw [h2]; ring
    have hneg : (-1 : F) = 1 := by linear_combination -h2
    rw [h1, hneg]; exact IsSquare.one
  · have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
    have hm1 : quadraticChar (ZMod l) (-1) = -1 := by
      rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
    have hχm1 : ((quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F)) (-1) = -1 := by
      simp [MulChar.ringHomComp_apply, hm1]
    have hχ1 : (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F) ≠ 1 := by
      intro h
      rw [h, MulChar.one_apply (isUnit_one.neg)] at hχm1
      apply h2; linear_combination hχm1
    have hq : ((quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F)).IsQuadratic :=
      (quadraticChar_isQuadratic (ZMod l)).comp _
    have hψ := AddChar.zmodChar_primitive_of_primitive_root l hζ
    have hsq := gaussSum_sq hχ1 hq hψ
    rw [hχm1, ZMod.card] at hsq
    exact ⟨gaussSum _ _, by rw [← sq, hsq]; ring⟩

end Formalism.IrreducibleCountingLemmas.WindowSums
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.PropositionOneCentralCount
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem proposition_one_central_count : Prop1Core := by
  classical
  intro N Y P hN hY hP hcard
  have hb0 : (0 : ℝ) ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    positivity
  have hne : P.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < P.card := lt_of_le_of_lt hb0 hcard
    exact_mod_cast this
  obtain ⟨g₁, hg₁⟩ := hne
  set S := P.filter (fun g => ¬ Disjoint (BB g₁ N) (BB g N)) with hSdef
  have hS := excluded_count_bound N g₁ Y S hN hY (hP g₁ hg₁).1 (by
    intro g hg
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hg
    exact ⟨(hP g h1).1, (hP g h1).2.1, (hP g h1).2.2, h2⟩)
  have hlt : S.card < P.card := by exact_mod_cast lt_of_le_of_lt hS hcard
  obtain ⟨g₂, hg₂, hn⟩ : ∃ g₂ ∈ P, g₂ ∉ S := by
    by_contra hcon
    push Not at hcon
    exact absurd (Finset.card_le_card (fun g hg => hcon g hg)) (not_le.mpr hlt)
  have hd : Disjoint (BB g₁ N) (BB g₂ N) := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hg₂, h⟩)
  refine ⟨g₁, hg₁, g₂, hg₂, ?_, hd⟩
  rintro rfl
  have hmem : g₁ ∈ BB g₁ N := by simp [BB]
  exact Finset.disjoint_left.mp hd hmem hmem

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TWExportTransfer
section
namespace Formalism.IrreducibleCountingLemmas.TW

theorem export_transfer_holds : ExportTransfer := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ M B N N' c e ε hM hB hN hN' hc he hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  rw [index_scaling O K V B N' ϖ u n hB hN' hϖ, index_scaling O K V B N ϖ u n hB hN hϖ]
    at hle
  have a := (index_additive O K V M N N' hM hN hN').2
  have b := (index_additive O K V B N N' hB hN hN').2
  have d : sIdx M N' - sIdx M N = sIdx B N' - sIdx B N := by omega
  have d' : (sIdx M N' : ℝ) - sIdx M N = sIdx B N' - sIdx B N := by exact_mod_cast d
  push_cast at hle
  rw [add_div, add_div] at hle
  have h1 : (sIdx M N' : ℝ) / e - sIdx M N / e = sIdx B N' / e - sIdx B N / e := by
    rw [← sub_div, ← sub_div, d']
  linarith

end Formalism.IrreducibleCountingLemmas.TW
end

