import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.Bundle0001
import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.ToolsB
import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.Bundle0001
import Mathlib
import Formalism.GaloisIrreducibility.NoSolvableTransitive
import Formalism.ResultantValuation.ResultantAdjugateProofs.Bundle0001
import Formalism.ResultantValuation.ResultantAdjugateProofs.Bundle0002
import Formalism.ResultantValuation.Bundle0001
import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
import Formalism.ResultantValuation.PrimePairDyadicDisjointAlt
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0010
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0003

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
section
namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

theorem colength_bound_two_layers : ColengthTwoStep := Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts.lenBound2

theorem lagrange_resolvent_T : LagrangeT := by
  intro l _ D₁ D₂ ρ hd hρ
  have hass : ∀ a ∈ D₁, ∀ b ∈ D₁ ∪ D₂, a ≠ b →
      Associated (((a : ℤ) : ℤ_[l]) - ((b : ℤ) : ℤ_[l])) ((l : ℤ_[l]) ^ (0 + padicValInt l (a - b))) := by
    intro a _ b _ hab
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    set v := padicValInt l (a - b) with hv
    obtain ⟨c, hc⟩ : (l : ℤ) ^ v ∣ a - b := padicValInt_dvd (a - b)
    have hcn : ¬ (l : ℤ) ∣ c := by
      intro ⟨c', hc'⟩
      have : (l : ℤ) ^ (v + 1) ∣ a - b := ⟨c', by rw [hc, hc']; ring⟩
      have h2 := (padicValInt_dvd_iff (p := l) _ (a - b)).mp this
      rcases h2 with h2 | h2
      · exact hne h2
      · omega
    have hu : IsUnit ((c : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_intCast_eq_one_iff]
      exact ((Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).coprime_iff_not_dvd.mpr hcn).symm
    rw [zero_add, ← Int.cast_sub, hc]
    push_cast
    exact (associated_mul_unit_left _ _ hu)
  have h := Formalism.ZetaNonvanishing.LIFTV.lagrangeIdealSg_proof l ℤ_[l] 0 D₁ D₂ (fun a => ((a : ℤ) : ℤ_[l])) hd hass
  set E := D₁.sup fun a => (∑ b ∈ D₂, (0 + padicValInt l (a - b))) +
    ∑ a' ∈ D₁.erase a, (0 + padicValInt l (a - a')) with hE
  have hle : E ≤ ρ := by
    rw [hE]; apply Finset.sup_le; intro a ha
    simpa using hρ a ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [pow_add, mul_comm, C_mul]
  exact Ideal.mul_mem_left _ _ h

theorem filtered_product : FiltProd := by
  intro R V _ _ _ T F c k a
  induction a with
  | zero => intro _ x hx; simpa using hx
  | succ a ih =>
    intro h x hx
    have hy := ih (fun i h1 h2 => h i h1 (by omega)) x hx
    rw [← add_assoc, Finset.prod_Ico_succ_top (by omega), mul_comm, map_mul, Module.End.mul_apply]
    have := h (k + a) (by omega) (by omega) _ hy
    simpa [Module.algebraMap_end_apply] using this

theorem aeval_mapQ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (W : Submodule R V) (hW : W ≤ W.comap T) (P : R[X]) (y : V) :
    aeval (W.mapQ W T hW : Module.End R (V ⧸ W)) P (W.mkQ y) = W.mkQ (aeval T P y) := by
  have hpow : ∀ (n : ℕ) (z : V),
      ((W.mapQ W T hW : Module.End R (V ⧸ W)) ^ n) (W.mkQ z) = W.mkQ ((T ^ n) z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have : (W.mapQ W T hW : Module.End R (V ⧸ W)) (W.mkQ z) = W.mkQ (T z) := rfl
      rw [this, ih]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow,
      map_smul]

end Formalism.IrreducibleCountingLemmas.WindowSums
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRExcludedCount
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem card_class_le (S : Finset ℕ) (Y : ℝ) (M r : ℕ) (hM : 0 < M) (hY : 0 ≤ Y)
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ g % M = r) :
    (S.card : ℝ) ≤ Y / M + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]; positivity
  set g0 := S.min' hne with hg0def
  have hg0 : g0 ∈ S := S.min'_mem hne
  have hdvd : ∀ a ∈ S, g0 ≤ a ∧ M ∣ a - g0 := by
    intro a ha
    have ha0 : g0 ≤ a := S.min'_le a ha
    refine ⟨ha0, (Nat.modEq_iff_dvd' ha0).mp ?_⟩
    unfold Nat.ModEq
    rw [(hS g0 hg0).2.2, (hS a ha).2.2]
  have hinj : Set.InjOn (fun g => (g - g0) / M) (S : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨ha0, s, hs⟩ := hdvd a ha
    obtain ⟨hb0, t, ht⟩ := hdvd b hb
    simp only at hab
    rw [hs, ht, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM] at hab
    subst hab
    omega
  have himg : S.image (fun g => (g - g0) / M) ⊆ Finset.range (⌊Y / M⌋₊ + 1) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    have ha0 : g0 ≤ a := (hdvd a ha).1
    have h1 : (((a - g0) / M : ℕ) : ℝ) ≤ ((a - g0 : ℕ) : ℝ) / M := Nat.cast_div_le
    have h2 : ((a - g0 : ℕ) : ℝ) = (a : ℝ) - g0 := Nat.cast_sub ha0
    have h3 : (a : ℝ) - g0 ≤ Y := by linarith [(hS a ha).2.1, (hS g0 hg0).1]
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    calc (((a - g0) / M : ℕ) : ℝ) ≤ ((a - g0 : ℕ) : ℝ) / M := h1
      _ ≤ Y / M := by rw [h2]; exact div_le_div_of_nonneg_right h3 hM'.le
  have hc : S.card ≤ ⌊Y / M⌋₊ + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    simpa using Finset.card_le_card himg
  have hfl : ((⌊Y / M⌋₊ : ℕ) : ℝ) ≤ Y / M := Nat.floor_le (by positivity)
  calc (S.card : ℝ) ≤ ((⌊Y / M⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ Y / M + 1 := by push_cast; linarith

theorem div_le_rpow (Y M : ℝ) (hY : 1 ≤ Y) (hM : 0 < M) (h : Y < M ^ 4) :
    Y / M ≤ Y ^ ((3 : ℝ) / 4) := by
  have hY0 : 0 < Y := by linarith
  have h1 : Y ^ ((1 : ℝ) / 4) ≤ M := by
    by_contra hcon
    push Not at hcon
    have h4 := pow_le_pow_left₀ hM.le hcon.le 4
    have h5 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num
    rw [h5] at h4
    linarith
  have h2 : Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hY0]; norm_num
  rw [div_le_iff₀ hM]
  calc Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := h2
    _ ≤ Y ^ ((3 : ℝ) / 4) * M := by
        exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hY0.le _)

theorem card_pow_class_le (S : Finset ℕ) (Y : ℝ) (l j d : ℕ) (hl : l.Prime) (hd : 1 ≤ d)
    (hY : 1 ≤ Y) (hj : Y < (l : ℝ) ^ (4 * j))
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ l ^ j ∣ g ^ d - 1) :
    (S.card : ℝ) ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  set M := l ^ j with hMdef
  have hM : 0 < M := pow_pos hl.pos j
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set R := (Finset.range M).filter (fun x => x ^ d ≡ 1 [MOD M]) with hR
  have hRcard : R.card ≤ 2 * d := Formalism.GaloisIrreducibility.residuesLe l j d hl hd
  have hmaps : ∀ g ∈ S, g % M ∈ R := by
    intro g hg
    obtain ⟨h1, _, h3⟩ := hS g hg
    have hg1 : 1 ≤ g := by
      have : (1 : ℝ) ≤ (g : ℝ) := hY.trans h1
      exact_mod_cast this
    have hgd : 1 ≤ g ^ d := Nat.one_le_pow _ _ hg1
    have hmod : 1 ≡ g ^ d [MOD M] := (Nat.modEq_iff_dvd' hgd).mpr h3
    rw [hR, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hM, ?_⟩
    exact ((Nat.mod_modEq g M).pow d).trans hmod.symm
  have hcard : S.card = ∑ r ∈ R, (S.filter (fun g => g % M = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ r ∈ R, ((S.filter (fun g => g % M = r)).card : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    intro r _
    have h1 := card_class_le (S.filter (fun g => g % M = r)) Y M r hM (by linarith) (by
      intro g hg
      obtain ⟨hgS, hgr⟩ := Finset.mem_filter.mp hg
      exact ⟨(hS g hgS).1, (hS g hgS).2.1, hgr⟩)
    have h2 : Y / (M : ℝ) ≤ Y ^ ((3 : ℝ) / 4) := by
      apply div_le_rpow Y M hY hM'
      have : ((M : ℝ)) ^ 4 = (l : ℝ) ^ (4 * j) := by
        rw [hMdef]; push_cast; rw [← pow_mul, mul_comm]
      rw [this]; exact hj
    linarith
  have hc0 : (0 : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    linarith
  calc (S.card : ℝ) = ∑ r ∈ R, ((S.filter (fun g => g % M = r)).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ _r ∈ R, (Y ^ ((3 : ℝ) / 4) + 1) := Finset.sum_le_sum hfib
    _ = (R.card : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
        apply mul_le_mul_of_nonneg_right _ hc0
        exact_mod_cast hRcard

theorem excluded_count_bound : ExcludedCount := by
  classical
  intro N g₁ Y S hN hY hg₁ hS
  set c : ℝ := Y ^ ((3 : ℝ) / 4) + 1 with hc
  have hc0 : (0 : ℝ) ≤ c := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    linarith
  have hcover : S ⊆ (BB g₁ N).biUnion (fun l => S.filter (fun g => l ∈ BB g N)) := by
    intro g hg
    obtain ⟨_, _, _, hnd⟩ := hS g hg
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨l, h1, h2⟩ := hnd
    exact Finset.mem_biUnion.mpr ⟨l, h1, Finset.mem_filter.mpr ⟨hg, h2⟩⟩
  have hper : ∀ l ∈ BB g₁ N,
      ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c := by
    intro l hlB
    have hl : l.Prime := by
      simp only [BB, Finset.mem_insert, Finset.mem_filter] at hlB
      rcases hlB with rfl | ⟨_, h2, _⟩
      · exact hg₁
      · exact h2
    have hex : ∃ j : ℕ, Y < (l : ℝ) ^ (4 * j) := by
      have h1 : (1 : ℝ) < (l : ℝ) ^ 4 := by
        have : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.one_lt
        exact one_lt_pow₀ this (by norm_num)
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt Y h1
      exact ⟨n, by rw [pow_mul]; exact hn⟩
    set j := Nat.find hex with hjdef
    have hj : Y < (l : ℝ) ^ (4 * j) := Nat.find_spec hex
    have hmin : ∀ i < j, (l : ℝ) ^ (4 * i) ≤ Y := fun i hi => not_lt.mp (Nat.find_min hex hi)
    set F : ℕ → Finset ℕ := fun d => S.filter (fun g => l ^ j ∣ g ^ d - 1) with hF
    have hsub : S.filter (fun g => l ∈ BB g N) ⊆ insert l ((Finset.Icc 1 N).biUnion F) := by
      intro g hg
      obtain ⟨hgS, hlg⟩ := Finset.mem_filter.mp hg
      obtain ⟨hgp, hYg, _, _⟩ := hS g hgS
      simp only [BB, Finset.mem_insert, Finset.mem_filter] at hlg
      rcases hlg with rfl | ⟨_, _, d, hd, h3⟩
      · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩)
        rw [hF]
        refine Finset.mem_filter.mpr ⟨hgS, ?_⟩
        exact bad_primes_divides l g d j Y hl (Finset.mem_Icc.mp hd).1 hgp.two_le hYg h3 hj hmin
    have hFd : ∀ d ∈ Finset.Icc 1 N, ((F d).card : ℝ) ≤ 2 * N * c := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have h1 := card_pow_class_le (F d) Y l j d hl hd1 hY hj (by
        intro g hg
        obtain ⟨hgS, hdv⟩ := Finset.mem_filter.mp hg
        exact ⟨(hS g hgS).2.1, (hS g hgS).2.2.1, hdv⟩)
      have hdN' : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
      calc ((F d).card : ℝ) ≤ 2 * d * c := h1
        _ ≤ 2 * N * c := by
            apply mul_le_mul_of_nonneg_right _ hc0
            linarith
    have h1 : (S.filter (fun g => l ∈ BB g N)).card ≤
        (∑ d ∈ Finset.Icc 1 N, (F d).card) + 1 :=
      calc (S.filter (fun g => l ∈ BB g N)).card
          ≤ (insert l ((Finset.Icc 1 N).biUnion F)).card := Finset.card_le_card hsub
        _ ≤ ((Finset.Icc 1 N).biUnion F).card + 1 := Finset.card_insert_le _ _
        _ ≤ (∑ d ∈ Finset.Icc 1 N, (F d).card) + 1 :=
            Nat.add_le_add_right Finset.card_biUnion_le 1
    have h2 : ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤
        (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) + 1 := by exact_mod_cast h1
    have h3 : (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) ≤ ∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c :=
      Finset.sum_le_sum hFd
    have h4 : (∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c) = 2 * (N : ℝ) ^ 2 * c := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp only [Nat.add_sub_cancel]
      ring
    linarith
  have hB0 : (0 : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c := by positivity
  have hBB : ((BB g₁ N).card : ℝ) ≤ 3 * N + 1 := by
    exact_mod_cast bad_primes_cardinality g₁ N hg₁.two_le
  have h1 : S.card ≤ ∑ l ∈ BB g₁ N, (S.filter (fun g => l ∈ BB g N)).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have h2 : (S.card : ℝ) ≤ ∑ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ) := by
    exact_mod_cast h1
  calc (S.card : ℝ) ≤ ∑ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ) := h2
    _ ≤ ∑ _l ∈ BB g₁ N, (1 + 2 * (N : ℝ) ^ 2 * c) := Finset.sum_le_sum hper
    _ = ((BB g₁ N).card : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * c) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * c) := mul_le_mul_of_nonneg_right hBB hB0

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TWIndexScale
section
open Module

namespace Formalism.IrreducibleCountingLemmas.TW

theorem index_scaling : IndexScale := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ M N ϖ u n hM hN hϖ
  have hinj := IsFractionRing.injective O K
  have hc : algebraMap O K ((u : O) * ϖ ^ n) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ.ne_zero))
  obtain ⟨d, β, rfl⟩ := Idx.exists_basis hN
  have hd : Module.finrank K V = d := by
    simpa using Module.finrank_eq_card_basis β
  let wb : Basis (Fin d) K V :=
    β.isUnitSMul (w := fun _ => algebraMap O K ((u : O) * ϖ ^ n)) (fun _ => isUnit_iff_ne_zero.2 hc)
  have hspan : scaleLat ((u : O) * ϖ ^ n) (Submodule.span O (Set.range β))
      = Submodule.span O (Set.range wb) := by
    unfold scaleLat
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp only [Function.comp_apply, LinearMap.lsmul_apply, wb, Basis.isUnitSMul_apply,
      algebraMap_smul]
  have hdet : β.det wb = algebraMap O K ((u ^ d : Oˣ) : O)
      * (algebraMap O K ϖ) ^ ((d : ℤ) * (n : ℤ)) := by
    rw [Basis.det_isUnitSMul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_mul,
      mul_pow, Units.val_pow_eq_pow_val, map_pow, map_pow, ← pow_mul, mul_comm n d]
    norm_cast
  have h1 := index_of_determinant O K V d β wb ϖ (u ^ d) ((d : ℤ) * (n : ℤ)) hϖ hdet
  have h2 := (index_additive O K V M _ _ hM hN (Idx.isLat_span_basis (O := O) wb)).2
  rw [hspan, hd, ← h2, h1]

end Formalism.IrreducibleCountingLemmas.TW
end

