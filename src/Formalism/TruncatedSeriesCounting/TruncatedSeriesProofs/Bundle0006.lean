import Formalism.TruncatedSeriesCounting.LemmaDetPoly
import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.TruncatedSeriesCounting.Bundle0001
import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.BridgeDet
section
open Formalism.NG

universe u v w

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem eta_determinant_comparison : BridgeDet.{u, v, w} := by
  intro hP hB O _ _ X' G _ T' d _ _ R' ρ hρ hR g _ _ Θ
  refine hB O X' T' d R' ?_ g Θ
  intro m a s
  exact hP O (FractionRing O) X' G d T' ρ hρ m (fun i => (a i : X' → Matrix d d (FractionRing O)))
    (fun i => hR _ (a i).2) s

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.FirstSigmaValuationBound
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Finset

private lemma sum_erase_union_le (f : ℤ → ℕ) (A B : Finset ℤ) :
    (∑ j ∈ (A ∪ B).erase 0, f j) ≤ (∑ j ∈ A.erase 0, f j) + ∑ j ∈ B.erase 0, f j := by
  classical
  rw [Finset.erase_union_distrib]
  have h := Finset.sum_union_inter (s₁ := A.erase 0) (s₂ := B.erase 0) (f := f)
  first
  | omega
  | (rw [← h]; exact Nat.le_add_right _ _)

private lemma sum_Icc_padicValNat_add_factorial_eq (ℓ : ℕ) [Fact ℓ.Prime] (m L : ℕ) :
    (∑ n ∈ Finset.Icc (m + 1) (m + L), padicValNat ℓ n) + padicValNat ℓ m.factorial =
      padicValNat ℓ (m + L).factorial := by
  induction L with
  | zero =>
    simp only [add_zero]
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ L ih =>
    rw [show m + (L + 1) = m + L + 1 by omega, Finset.sum_Icc_succ_top (by omega), Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _), ← ih]
    omega

private lemma sub_one_mul_padicValNat_factorial_le' (ℓ : ℕ) [Fact ℓ.Prime] (N : ℕ) :
    (ℓ - 1) * padicValNat ℓ N.factorial ≤ N := by
  rw [sub_one_mul_padicValNat_factorial]
  omega

private lemma padicValNat_factorial_add_le_add_log (ℓ : ℕ) [Fact ℓ.Prime] (m L : ℕ) :
    padicValNat ℓ (m + L).factorial ≤
      padicValNat ℓ m.factorial + padicValNat ℓ L.factorial + Nat.log ℓ (m + L) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial m L
  have hc : (m + L).choose L ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hlog : padicValNat ℓ ((m + L).choose L) ≤ Nat.log ℓ (m + L) := by
    rw [← Nat.factorization_def _ (Fact.out : ℓ.Prime)]
    exact Nat.factorization_choose_le_log
  rw [← h, padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
    padicValNat.mul hc (Nat.factorial_ne_zero _)]
  omega

private lemma sum_Icc_one_padicValNat_eq_factorial (ℓ : ℕ) [Fact ℓ.Prime] (L : ℕ) :
    (∑ n ∈ Finset.Icc 1 L, padicValNat ℓ n) = padicValNat ℓ L.factorial := by
  have h := sum_Icc_padicValNat_add_factorial_eq ℓ 0 L
  simpa using h

theorem first_sigma_valuation_bound : TwoIntervalValuationSumBound := by
  intro ℓ _ h η S b a hab hbS
  have hℓ : ℓ.Prime := Fact.out
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have step1 := sum_erase_union_le (padicValInt ℓ) (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a))
    (Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b))
  have hI1 : (∑ j ∈ (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)).erase 0, padicValInt ℓ j) ≤
      padicValNat ℓ (η - 1).factorial + padicValNat ℓ (η + a).factorial := by
    have hsub : (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)).erase 0 ⊆
        Finset.Icc (1 - (η : ℤ)) (-1) ∪ Finset.Icc 1 ((η : ℤ) + a) := by
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union] at hj ⊢
      omega
    have hdisj : Disjoint (Finset.Icc (1 - (η : ℤ)) (-1)) (Finset.Icc 1 ((η : ℤ) + a)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega
    have hneg : (∑ j ∈ Finset.Icc (1 - (η : ℤ)) (-1), padicValInt ℓ j) =
        ∑ n ∈ Finset.Icc 1 (η - 1), padicValNat ℓ n := by
      apply Finset.sum_nbij' (fun j : ℤ => ((-j).toNat : ℕ)) (fun n : ℕ => -(n : ℤ))
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        omega
      · intro n hn
        try dsimp only
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        rw [padicValInt]
        congr 1
        omega
    have hpos : (∑ j ∈ Finset.Icc 1 ((η : ℤ) + a), padicValInt ℓ j) =
        ∑ n ∈ Finset.Icc 1 (η + a), padicValNat ℓ n := by
      apply Finset.sum_nbij' (fun j : ℤ => (j.toNat : ℕ)) (fun n : ℕ => (n : ℤ))
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        omega
      · intro n hn
        try dsimp only
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        rw [padicValInt]
        congr 1
        omega
    calc _ ≤ ∑ j ∈ Finset.Icc (1 - (η : ℤ)) (-1) ∪ Finset.Icc 1 ((η : ℤ) + a), padicValInt ℓ j :=
          Finset.sum_le_sum_of_subset hsub
      _ = _ := by rw [Finset.sum_union hdisj, hneg, hpos, sum_Icc_one_padicValNat_eq_factorial, sum_Icc_one_padicValNat_eq_factorial]
  have hI2 : (∑ j ∈ (Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b)).erase 0, padicValInt ℓ j) ≤
      padicValNat ℓ (a + S).factorial + Nat.log ℓ (b - a - 1 + (a + S)) := by
    have heq : (∑ j ∈ Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b), padicValInt ℓ j) =
        ∑ n ∈ Finset.Icc (b - a - 1 + 1) (b - a - 1 + (a + S)), padicValNat ℓ n := by
      apply Finset.sum_nbij' (fun j : ℤ => ((-j).toNat : ℕ)) (fun n : ℕ => -(n : ℤ))
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        omega
      · intro n hn
        try dsimp only
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        rw [padicValInt]
        congr 1
        omega
    have h1 := sum_Icc_padicValNat_add_factorial_eq ℓ (b - a - 1) (a + S)
    have h2 := padicValNat_factorial_add_le_add_log ℓ (b - a - 1) (a + S)
    calc _ ≤ ∑ j ∈ Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b), padicValInt ℓ j :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      _ = _ := heq
      _ ≤ _ := by omega
  have tot : (∑ j ∈ (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) ∪
        Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b)).erase 0, padicValInt ℓ j) ≤
      padicValNat ℓ (η - 1).factorial + padicValNat ℓ (η + a).factorial +
        padicValNat ℓ (a + S).factorial + Nat.log ℓ (b - a - 1 + (a + S)) := by
    omega
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (show 1 < ℓ by omega)
  have hpos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hsubℓ : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have r : ∀ N : ℕ, ((ℓ : ℝ) - 1) * (padicValNat ℓ N.factorial : ℝ) ≤ (N : ℝ) := by
    intro N
    have c := sub_one_mul_padicValNat_factorial_le' ℓ N
    have c' : ((ℓ - 1 : ℕ) : ℝ) * (padicValNat ℓ N.factorial : ℝ) ≤ (N : ℝ) := by exact_mod_cast c
    rwa [hsubℓ] at c'
  have hsum : (padicValNat ℓ (η - 1).factorial : ℝ) + (padicValNat ℓ (η + a).factorial : ℝ) +
      (padicValNat ℓ (a + S).factorial : ℝ) ≤ (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) := by
    rw [le_div_iff₀ hpos]
    have e1 := r (η - 1)
    have e2 := r (η + a)
    have e3 := r (a + S)
    have e4 : ((η - 1 : ℕ) : ℝ) ≤ (η : ℝ) := by exact_mod_cast Nat.sub_le η 1
    push_cast at e2 e3
    nlinarith [e1, e2, e3, e4]
  have hlam0 : 0 ≤ lam ℓ (h + η) := by
    unfold lam
    by_cases h0 : h + η = 0
    · rw [h0]
      simp
    · have h1 : (1 : ℝ) ≤ ((h + η : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      have h2 : (1 : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) := by linarith
      have := Real.logb_nonneg hℓR h2
      linarith
  have hk : ((Nat.log ℓ (b - a - 1 + (a + S)) : ℕ) : ℝ) ≤ lam ℓ (h + η) := by
    by_cases hN : b - a - 1 + (a + S) = 0
    · rw [hN, Nat.log_zero_right]
      simpa using hlam0
    · have hpow : ℓ ^ Nat.log ℓ (b - a - 1 + (a + S)) ≤ b - a - 1 + (a + S) :=
        Nat.pow_log_le_self ℓ hN
      have hNh : b - a - 1 + (a + S) ≤ 2 * (h + η) := by omega
      have hNpos : (0 : ℝ) < ((b - a - 1 + (a + S) : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hN
      have h1 : ((Nat.log ℓ (b - a - 1 + (a + S)) : ℕ) : ℝ) ≤
          Real.logb ℓ ((b - a - 1 + (a + S) : ℕ) : ℝ) := by
        rw [Real.le_logb_iff_rpow_le hℓR hNpos, Real.rpow_natCast]
        exact_mod_cast hpow
      have h2 : Real.logb ℓ ((b - a - 1 + (a + S) : ℕ) : ℝ) ≤
          Real.logb ℓ (2 * ((h + η : ℕ) : ℝ)) := by
        apply Real.logb_le_logb_of_le hℓR hNpos
        exact_mod_cast hNh
      unfold lam
      linarith
  refine le_trans (Nat.cast_le.mpr tot) ?_
  push_cast
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.KapWin
section
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

open Finset

private lemma sum_le_sum_cover {K : ℕ} (W : Fin K → Finset ℤ) (S : Finset ℤ)
    (hS : ∀ i ∈ S, ∃ k, i ∈ W k) (g : ℤ → ℕ) :
    ∑ i ∈ S, g i ≤ ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
  calc ∑ i ∈ S, g i ≤ ∑ i ∈ S, ∑ k, if i ∈ W k then g i else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨k, hk⟩ := hS i hi
        calc g i = (fun k' => if i ∈ W k' then g i else 0) k := by simp [hk]
          _ ≤ ∑ k', if i ∈ W k' then g i else 0 :=
            Finset.single_le_sum (f := fun k' => if i ∈ W k' then g i else 0) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
    _ = ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter]

theorem kappa_window_bound : KapWin := by
  intro ℓ _ hℓ χ hχ ell K D a L JJ hJJ hD
  obtain ⟨hne, hv⟩ := Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ
  refine ⟨hne, ?_⟩
  rw [hv]
  set S := JJ.erase 0 with hSdef
  set W : Fin K → Finset ℤ := fun k => Finset.Ico (a k) (a k + (L k : ℤ)) with hWdef
  have hcov : ∀ i ∈ S, ∃ k, i ∈ W k := by
    intro i hi
    have := hJJ (Finset.mem_of_mem_erase hi)
    simpa [Finset.mem_biUnion, hWdef] using this
  have hcard : S.card ≤ ∑ k, L k := by
    have h := sum_le_sum_cover W S hcov (fun _ => 1)
    rw [Finset.card_eq_sum_ones]
    refine h.trans (Finset.sum_le_sum fun k _ => ?_)
    rw [← Finset.card_eq_sum_ones]
    calc (S.filter (fun i => i ∈ W k)).card ≤ (W k).card := by
          apply Finset.card_le_card
          intro i hi
          exact (Finset.mem_filter.mp hi).2
      _ = L k := by simp [hWdef]
  have hsumv : ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) ≤
      ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D) := by
    calc ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ)
        ≤ ((∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
          exact_mod_cast sum_le_sum_cover W S hcov (fun i => padicValInt ℓ i)
      _ = ∑ k, ((∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D) := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine Formalism.WindowSums.arc_WindowSum ℓ (a k) (L k) D _ ?_ ?_ ?_
          · intro i hi
            exact (Finset.mem_filter.mp hi).2
          · intro h0
            have := (Finset.mem_filter.mp h0).1
            simp [hSdef] at this
          · intro i hi
            exact hD i (Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1)
  have hsplit : ∑ i ∈ S, (1 + ell + padicValInt ℓ i) =
      S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  rw [hsplit]
  have hcardR : (S.card : ℝ) ≤ ((∑ k, L k : ℕ) : ℝ) := by exact_mod_cast hcard
  have hmul : (S.card : ℝ) * (1 + ell) ≤ ((∑ k, L k : ℕ) : ℝ) * (1 + ell) :=
    mul_le_mul_of_nonneg_right hcardR (by positivity)
  have hgoal : ((S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i + ell : ℕ) : ℝ) =
      (S.card : ℝ) * (1 + ell) + ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) + ell := by
    push_cast; ring
  rw [hgoal]
  linarith

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGIdeal
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Polynomial

private theorem winDiff (ℓ : ℕ) [Fact ℓ.Prime] (j₀ lo : ℤ) (L D : ℕ) (T : Finset ℤ)
    (hT : ∀ j ∈ T, lo ≤ j₀ - j ∧ j₀ - j < lo + L) (h0 : j₀ ∉ T)
    (hD : ∀ j ∈ T, |j₀ - j| ≤ (D : ℤ)) :
    ((∑ j ∈ T, padicValInt ℓ (j₀ - j) : ℕ) : ℝ) ≤
      (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb (ℓ : ℝ) (D : ℝ) := by
  have hinj : Set.InjOn (fun j : ℤ => j₀ - j) (T : Set ℤ) := by
    intro x _ y _ h
    simp only at h
    omega
  have hre : ∑ j ∈ T, padicValInt ℓ (j₀ - j) =
      ∑ i ∈ T.image (fun j : ℤ => j₀ - j), padicValInt ℓ i :=
    (Finset.sum_image hinj).symm
  rw [hre]
  apply Formalism.WindowSums.arc_WindowSum ℓ lo L D
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    have := hT j hj
    rw [Finset.mem_Ico]
    omega
  · intro hi
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.1 hi
    have : j = j₀ := by omega
    exact h0 (this ▸ hj)
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    exact hD j hj

theorem g_ideal_valuation_statement : LemmaGIdeal := by
  intro ℓ _ R _ _ c hc h η S b a S₂ hb hbS hS₂
  have hℓ2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Fact.out : ℓ.Prime).two_le
  set S₁ := Finset.Icc ((b : ℤ) - a + 1) (b : ℤ) with hS₁def
  have m2 : ∀ r ∈ S₂, ((b : ℤ) + 1 ≤ r ∧ r ≤ b + S + a) ∨ (1 - (η : ℤ) ≤ r ∧ r ≤ η + a) := by
    intro r hr
    simpa only [Finset.mem_union, Finset.mem_Icc] using hS₂ hr
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    rw [hS₁def, Finset.mem_Icc] at hr1
    have := m2 r hr2
    omega
  have hlag := Formalism.LIFT.lift_LagrangeIdealInt ℓ R S₁ S₂ c hdisj
    (fun x _ y _ hxy => hc x y hxy)
  refine ⟨S₁.sup fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j), ?_, hlag⟩

  have hH1 : (1 : ℝ) ≤ ((h + η : ℕ) : ℝ) := by
    have : 1 ≤ h + η := by omega
    exact_mod_cast this
  have hlog : Real.logb (ℓ : ℝ) ((h + η : ℕ) : ℝ) ≤ lam ℓ (h + η) := by
    unfold lam
    have := Real.logb_le_logb_of_le (b := (ℓ : ℝ)) (by linarith) (by linarith)
      (show ((h + η : ℕ) : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)
    linarith
  have hlam0 : 0 ≤ lam ℓ (h + η) := by
    unfold lam
    have := Real.logb_nonneg (b := (ℓ : ℝ)) (by linarith)
      (show (1 : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)
    linarith
  have hden : 0 < (ℓ : ℝ) - 1 := by linarith
  have key : ∀ j₀ ∈ S₁, ((((∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j) : ℕ)) : ℝ) ≤
      (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) + 3 * lam ℓ (h + η) := by
    intro j₀ hj₀
    rw [hS₁def, Finset.mem_Icc] at hj₀
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun j => (b : ℤ) + 1 ≤ j)]
    push_cast
    have w1 := winDiff ℓ j₀ (j₀ - b) a (h + η) (S₁.erase j₀)
      (by
        intro j hj
        rw [Finset.mem_erase, hS₁def, Finset.mem_Icc] at hj
        omega)
      (by simp)
      (by
        intro j hj
        rw [Finset.mem_erase, hS₁def, Finset.mem_Icc] at hj
        rw [abs_le]
        push_cast
        constructor <;> omega)
    have w2 := winDiff ℓ j₀ (j₀ - b - S - a) (S + a) (h + η)
      (S₂.filter (fun j => (b : ℤ) + 1 ≤ j))
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        push_cast
        omega)
      (by
        rw [Finset.mem_filter]
        omega)
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        rw [abs_le]
        push_cast
        constructor <;> omega)
    have w3 := winDiff ℓ j₀ (j₀ - η - a) (2 * η + a) (h + η)
      (S₂.filter (fun j => ¬ (b : ℤ) + 1 ≤ j))
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        push_cast
        omega)
      (by
        rw [Finset.mem_filter]
        intro hh
        have := m2 j₀ hh.1
        omega)
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        rw [abs_le]
        push_cast
        constructor <;> omega)
    push_cast at w1 w2 w3
    have hsum : (a : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) +
        (2 * (η : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) =
        (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by ring
    push_cast at hlog
    linarith
  rcases S₁.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sup_empty]
    simp only [Nat.bot_eq_zero, Nat.cast_zero]
    have : 0 ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by positivity
    linarith
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup S₁ hne
      (fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) + ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j))
    rw [hjeq]
    exact key j hj

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

