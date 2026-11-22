import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubOnePowTotient
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.CycTrace
open Polynomial

theorem norm_root_eq_one {K : Type*} [NormedField K] {n : ℕ} (hn : n ≠ 0) {ζ : K}
    (hζ : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  have := congrArg norm hζ
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

theorem norm_pow_sub_one_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {ζ : K} (hz : ‖ζ‖ = 1) (a : ℕ) : ‖ζ ^ a - 1‖ ≤ ‖ζ - 1‖ := by
  first
  | exact @_root_.GlobalTheory.NormPowSubOne.main
  | exact _root_.GlobalTheory.NormPowSubOne.main
  | (apply _root_.GlobalTheory.NormPowSubOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormPowSubOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormPowSubOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormPowSubOne.main ..)

theorem norm_sub_one_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (hn : n ≠ 0) {ζ μ : K} (hζ : IsPrimitiveRoot ζ n) (hμ : μ ^ n = 1) :
    ‖μ - 1‖ ≤ ‖ζ - 1‖ := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨a, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  exact norm_pow_sub_one_le (norm_root_eq_one hn hζ.pow_eq_one) a

theorem norm_sub_one_pow_totient {K : Type*} [NormedField K] [IsUltrametricDist K]
    (l : ℕ) [hl : Fact l.Prime] (k : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ (k + 1))) :
    ‖ζ - 1‖ ^ (l ^ (k + 1)).totient = ‖(l : K)‖ := by
  have hp := hl.out
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 := Polynomial.eval_one_cyclotomic_prime_pow (R := K) (p := l) k
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
  have h2 := congrArg norm h1
  rw [norm_prod] at h2
  have h3 : ∀ μ ∈ primitiveRoots (l ^ (k + 1)) K,
      ‖Polynomial.eval 1 (Polynomial.X - Polynomial.C μ)‖ = ‖ζ - 1‖ := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).1 hμ
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_sub_rev]
    exact le_antisymm (norm_sub_one_le hn hζ hμ'.pow_eq_one)
      (norm_sub_one_le hn hμ' hζ.pow_eq_one)
  rwa [Finset.prod_congr rfl h3, Finset.prod_const, hζ.card_primitiveRoots] at h2

theorem norm_le_norm_sum {K ι : Type*} [NormedField K] [IsUltrametricDist K] (s : Finset ι)
    (f : ι → K) (h : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → ‖f i‖ = ‖f j‖ → i = j) {i : ι} (hi : i ∈ s) :
    ‖f i‖ ≤ ‖∑ j ∈ s, f j‖ := by
  classical
  obtain ⟨k, hk, hmax⟩ := s.exists_max_image (fun j => ‖f j‖) ⟨i, hi⟩
  refine (hmax i hi).trans ?_
  by_cases h0 : f k = 0
  · simp [h0]
  have hlt : ‖∑ j ∈ s.erase k, f j‖ < ‖f k‖ := by
    rcases (s.erase k).eq_empty_or_nonempty with he | hne
    · simpa [he] using h0
    · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
      refine hle.trans_lt (lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj)) ?_)
      intro e
      exact (Finset.ne_of_mem_erase hj) (h k hk j (Finset.mem_of_mem_erase hj) h0 e.symm).symm
  rw [← Finset.add_sum_erase s f hk, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne']
  exact le_max_left _ _

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_l : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  have h2 : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) l := by simp
  rw [h2, norm_algebraMap', Padic.norm_p]

theorem coeff_bound_unif (π : PadicAlgCl l) (e : ℕ) (hπ : ‖π‖ ^ e = (l : ℝ)⁻¹)
    (Q : ℚ_[l][X]) (hQ : Q.natDegree < e) (k : ℕ) :
    (l : ℝ)⁻¹ * ‖Q.coeff k‖ ≤ ‖aeval π Q‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have he : e ≠ 0 := by omega
  have hr0 : 0 < ‖π‖ := by
    rcases (norm_nonneg π).eq_or_lt with h | h
    · rw [← h, zero_pow he] at hπ
      exact absurd hπ (inv_pos.2 hl0).ne
    · exact h
  have hr1 : ‖π‖ < 1 := by
    by_contra h
    have := one_le_pow₀ (not_lt.1 h) (n := e)
    rw [hπ] at this
    exact absurd (inv_lt_one_of_one_lt₀ hl1) (not_lt.2 this)
  by_cases hk : k < e
  swap
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  rw [aeval_eq_sum_range' hQ]
  refine le_trans ?_ (norm_le_norm_sum (Finset.range e) (fun j => Q.coeff j • π ^ j) ?_
    (Finset.mem_range.2 hk))
  · simp only [norm_smul, norm_pow]
    rw [mul_comm, ← hπ]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hk.le) (norm_nonneg _)
  · intro i hi j hj h0 hij
    simp only [norm_smul, norm_pow] at hij
    have hi0 : Q.coeff i ≠ 0 := fun h => h0 (by simp [h])
    have hj0 : Q.coeff j ≠ 0 := by
      intro h
      rw [h, norm_zero, zero_mul] at hij
      exact (mul_pos (norm_pos_iff.2 hi0) (pow_pos hr0 _)).ne' hij
    rw [Padic.norm_eq_zpow_neg_valuation hi0, Padic.norm_eq_zpow_neg_valuation hj0,
      ← inv_zpow', ← inv_zpow', ← hπ, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne'] at hij
    have h3 := zpow_right_injective₀ hr0 hr1.ne hij
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have h4 : (e : ℤ) ∣ (i : ℤ) - j :=
      ⟨(Q.coeff j).valuation - (Q.coeff i).valuation, by linear_combination h3⟩
    have h5 := Int.eq_zero_of_abs_lt_dvd h4 (by rw [abs_lt]; constructor <;> omega)
    omega

theorem coeff_bound (N : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (N + 1)))
    (P : ℚ_[l][X]) (hP : P.natDegree < (l ^ (N + 1)).totient) (k : ℕ) :
    (l : ℝ)⁻¹ * ‖P.coeff k‖ ≤ ‖aeval z P‖ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hπ := norm_sub_one_pow_totient l N z hz
  rw [norm_l] at hπ
  have hQ := coeff_bound_unif (z - 1) _ hπ (taylor 1 P) (by rwa [natDegree_taylor])
  have e1 : aeval (z - 1) (taylor 1 P) = aeval z P := by
    rw [taylor_apply, aeval_comp]; simp
  rw [e1] at hQ
  have e2 : P = taylor (-1) (taylor 1 P) := by rw [taylor_taylor]; simp
  generalize taylor 1 P = Q at hQ e2
  have : ‖P.coeff k‖ ≤ l * ‖aeval z P‖ := by
    conv_lhs => rw [e2, taylor_coeff, eval_eq_sum_range]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro j _
    rw [hasseDeriv_coeff, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    have h1 := IsUltrametricDist.norm_natCast_le_one ℚ_[l] ((j + k).choose k)
    have h2 := hQ (j + k)
    rw [inv_mul_le_iff₀ hl0] at h2
    calc _ ≤ 1 * ‖Q.coeff (j + k)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := by rwa [one_mul]
  rwa [inv_mul_le_iff₀ hl0]

theorem exists_poly (n : ℕ) (hn : 0 < n) (w : PadicAlgCl l) (hw : IsPrimitiveRoot w n)
    (a : PadicAlgCl l) (ha : a ∈ IntermediateField.adjoin ℚ_[l] {w}) :
    ∃ p : ℚ_[l][X], p.natDegree < n.totient ∧ aeval w p = a := by
  have hint : IsIntegral ℚ_[l] w := (hw.isIntegral hn).tower_top
  have h1 : a ∈ (IntermediateField.adjoin ℚ_[l] {w}).toSubalgebra := ha
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at h1
  obtain ⟨q, rfl⟩ := h1
  have hm : (cyclotomic n ℚ_[l]).Monic := cyclotomic.monic n _
  have hroot : aeval w (cyclotomic n ℚ_[l]) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hw.isRoot_cyclotomic hn
  refine ⟨q %ₘ cyclotomic n ℚ_[l], ?_, aeval_modByMonic_eq_self_of_root hroot⟩
  rw [← natDegree_cyclotomic n ℚ_[l]]
  refine natDegree_modByMonic_lt q hm ?_
  intro h
  have := natDegree_cyclotomic n ℚ_[l]
  rw [h, natDegree_one] at this
  exact (Nat.totient_pos.2 hn).ne this

end GlobalTheory.CycTrace

open Polynomial GlobalTheory.CycTrace in

theorem GlobalTheory.CycTrace.normalised_trace_bound (l : ℕ) [hl : Fact l.Prime] (n m : ℕ) (z : Om l)
    (hn : 1 ≤ n) (hz : IsPrimitiveRoot z (l ^ (n + m))) (a : Fin (l ^ m) → Om l)
    (ha : ∀ i, a i ∈ IntermediateField.adjoin ℚ_[l] {z ^ (l ^ m)}) :
    ‖(l : Om l)‖ * ‖a ⟨0, pow_pos (Fact.out : l.Prime).pos m⟩‖ ≤ ‖∑ i, a i * z ^ (i : ℕ)‖ := by
  have hp := hl.out
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hp.pos
  have hM : 0 < l ^ m := pow_pos hp.pos m
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hw : IsPrimitiveRoot (z ^ (l ^ m)) (l ^ (n + 1)) :=
    hz.pow (pow_pos hp.pos _) (by rw [pow_add, mul_comm])
  choose p hp1 hp2 using fun i => exists_poly _ (pow_pos hp.pos _) _ hw (a i) (ha i)
  have hN : n + 1 + m = (n + m) + 1 := by ring
  rw [hN] at hz
  set P : ℚ_[l][X] := ∑ i : Fin (l ^ m), expand ℚ_[l] (l ^ m) (p i) * X ^ (i : ℕ) with hPdef
  have htot : (l ^ (n + m + 1)).totient = (l ^ (n + 1)).totient * l ^ m := by
    rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]; ring
  have hdeg : P.natDegree < (l ^ (n + m + 1)).totient := by
    have hpos : 0 < (l ^ (n + m + 1)).totient := Nat.totient_pos.2 (pow_pos hp.pos _)
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n := (l ^ (n + m + 1)).totient - 1) _ _ ?_) (by omega)
    intro i _
    refine natDegree_mul_le.trans ?_
    rw [natDegree_expand, natDegree_X_pow]
    have h1 := hp1 i
    have h2 := i.2
    have h3 : ((p i).natDegree + 1) * l ^ m ≤ (l ^ (n + 1)).totient * l ^ m :=
      Nat.mul_le_mul_right _ h1
    rw [add_mul] at h3
    omega
  have hev : aeval z P = ∑ i, a i * z ^ (i : ℕ) := by
    rw [hPdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, expand_aeval, hp2]; simp
  have hco : ∀ j, P.coeff (j * l ^ m) = (p ⟨0, hM⟩).coeff j := by
    intro j
    rw [hPdef, finset_sum_coeff, Finset.sum_eq_single ⟨0, hM⟩]
    · simp [coeff_expand_mul hM]
    · intro i _ hi
      rw [coeff_mul_X_pow']
      split_ifs with h
      · rw [coeff_expand hM, if_neg]
        intro hd
        have : l ^ m ∣ (i : ℕ) := by
          have := (Nat.dvd_sub_iff_right h (Dvd.intro_left j rfl)).1 hd
          exact this
        exact hi (Fin.ext (Nat.eq_zero_of_dvd_of_lt this i.2))
      · rfl
    · simp
  have hb := fun j => coeff_bound (n + m) z hz P hdeg (j * l ^ m)
  simp only [hco, hev] at hb
  have hw1 : ‖z ^ (l ^ m)‖ = 1 := norm_root_eq_one (pow_pos hp.pos _).ne' hw.pow_eq_one
  rw [norm_l, inv_mul_le_iff₀ hl0, ← hp2, aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
  intro j _
  rw [norm_smul, norm_pow, hw1, one_pow, mul_one, ← inv_mul_le_iff₀ hl0]
  exact hb j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimesAPIntervalOfTzRat
section
open Finset Formalism.HermitianLattices.GL2PrimeSums

namespace GlobalTheory.Mem.An

theorem tzRat_class_bound (h : TZRat) :
    ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧
      ∀ (M b : ℕ) (B : ℝ), 3 ≤ M → M % 4 ≠ 2 → Nat.Coprime b M → (M : ℝ) ≤ B →
        ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
          (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) ∧
          ∀ Y : ℝ, B ^ C₀ ≤ Y →
            |(M.totient : ℝ) * (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ)
              - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y := by
  obtain ⟨c₂, c₃, CA, cS, h2, h3, hA, hS, H⟩ := h
  have hs3 : 0 < Real.sqrt c₃ := Real.sqrt_pos.2 h3
  refine ⟨c₂, CA, min c₃ (Real.sqrt c₃), cS, h2, hA, lt_min h3 hs3, hS, ?_⟩
  intro M b B hM hM4 hb hMB
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨-, HS, HC⟩ := H M hM hM4
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlM : 1 / 4 ≤ Real.log M := by
    have h1 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    linarith
  have hlMB : Real.log M ≤ Real.log B := Real.log_le_log hM0 hMB

  have key : ∀ (θ : ℤ) (β : ℝ),
      ((θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M) (β' : ℝ), ¬ IsExcRat χ β') ∨
        ∃ χ : DirichletCharacter ℂ M, IsExcRat χ β ∧ χ (b : ZMod M) = (θ : ℂ)) →
      ∀ Y : ℝ, B ^ c₂ ≤ Y →
        |(M.totient : ℝ) * (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ)
          - Emain θ β Y| ≤ rhoErr CA (min c₃ (Real.sqrt c₃)) B Y * Emain θ β Y := by
    intro θ β hθ Y hY
    have hMY : (M : ℝ) ^ c₂ ≤ Y := le_trans (Real.rpow_le_rpow hM0.le hMB h2.le) hY
    have hY1 : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) h2.le) hMY
    have hL : 0 ≤ Real.log Y := Real.log_nonneg hY1
    have hq := HC b θ β hb hθ Y hMY
    have hpos : 0 < CA * (Real.exp (-c₃ * Real.log Y / Real.log M) +
        Real.exp (-Real.sqrt (c₃ * Real.log Y))) := by positivity
    have hE : 0 ≤ Emain θ β Y := by
      have := le_trans (abs_nonneg _) hq
      exact (mul_nonneg_iff_of_pos_left hpos).1 this
    refine le_trans hq (mul_le_mul_of_nonneg_right ?_ hE)
    unfold rhoErr
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hA.le
    · apply Real.exp_le_exp.2
      rw [neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
      have hm0 : 0 ≤ min c₃ (Real.sqrt c₃) := (lt_min h3 hs3).le
      calc min c₃ (Real.sqrt c₃) * Real.log Y / Real.log B
          ≤ min c₃ (Real.sqrt c₃) * Real.log Y / Real.log M :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hlMB
        _ ≤ c₃ * Real.log Y / Real.log M :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hL) (by linarith)
    · apply Real.exp_le_exp.2
      rw [neg_mul, neg_le_neg_iff, Real.sqrt_mul h3.le]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
  by_cases hex : ∃ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExcRat χ β
  · obtain ⟨χ, β, hχ⟩ := hex
    have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
    have hsq : χ (b : ZMod M) ^ 2 = 1 := by
      have h1 : (χ ^ 2) (b : ZMod M) = 1 := by
        rw [hχ.1]; exact MulChar.one_apply hu
      rwa [MulChar.pow_apply' χ (by norm_num)] at h1
    have hβ : 1 / 2 ≤ β ∧ β < 1 ∧ cS / (B ^ 2 * Real.log B) ≤ 1 - β := by
      refine ⟨?_, hχ.2.2.1, le_trans ?_ (HS χ β hχ)⟩
      · have h1 := hχ.2.1
        have h2 : 1 / (8 * Real.log M) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
        linarith
      · have hl0 : 0 < Real.log M := by linarith
        apply div_le_div_of_nonneg_left hS.le (by positivity)
        have hB0 : 0 < B := by linarith
        gcongr
    rcases sq_eq_one_iff.1 hsq with h1 | h1
    · exact ⟨1, β, by simp, fun _ => hβ, key 1 β (Or.inr ⟨χ, hχ, by simpa using h1⟩)⟩
    · exact ⟨-1, β, by simp, fun _ => hβ, key (-1) β (Or.inr ⟨χ, hχ, by simpa using h1⟩)⟩
  · push_neg at hex
    exact ⟨0, 0, by simp, fun h => absurd rfl h, key 0 0 (Or.inl ⟨rfl, hex⟩)⟩

theorem card_primes_mod_half (n a N : ℕ) (hn : Odd n) (ha : Nat.Coprime a (2 * n)) :
    ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card ≤
      ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card ∧
    ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card ≤
      ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card + 1 := by
  constructor
  · apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.of_mul_left 2⟩
  · refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le 2 _)
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_insert, Finset.mem_filter]
    by_cases h2 : p = 2
    · exact Or.inl h2
    · right
      refine ⟨hp.1, hp.2.1, ?_⟩
      have hc : Nat.Coprime 2 n := (Nat.coprime_two_left).2 hn
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hc]
      refine ⟨?_, hp.2.2⟩
      have hpo : Odd p := hp.2.1.odd_of_ne_two h2
      have hao : Odd a := (Nat.coprime_two_right).1 (Nat.Coprime.coprime_mul_right_right ha)
      unfold Nat.ModEq
      rw [Nat.odd_iff.1 hpo, Nat.odd_iff.1 hao]

theorem tzRat_ratClass (h : TZRat) :
    ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧ Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions C₀ Cr cr cb := by
  obtain ⟨C₀, Cr, cr, cb, h0, h1, h2, h3, H⟩ := tzRat_class_bound h
  refine ⟨C₀, Cr, cr, cb, h0, h1, h2, h3, ?_⟩
  intro m a hm ha
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hl : 1 ≤ 3 * Real.log (4 * (m : ℝ)) := by
    have h1 : Real.log 2 ≤ Real.log (4 * (m : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    linarith
  by_cases h4 : m % 4 = 2
  · obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n := ⟨m / 2, by omega⟩
    have hn : Odd n := Nat.odd_iff.2 (by omega)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    obtain ⟨θ, β, hθ, hβ, hE⟩ := H n a (4 * ((2 * n : ℕ) : ℝ)) (by omega) (by omega)
      (Nat.Coprime.coprime_mul_left_right ha) (by push_cast; linarith)
    refine ⟨θ, β, fun Y => (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card : ℝ) -
      (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card : ℝ), hθ, hβ, ?_, ?_⟩
    · intro Y
      obtain ⟨k1, k2⟩ := card_primes_mod_half n a ⌊Y⌋₊ hn ha
      have k1' := (Nat.cast_le (α := ℝ)).2 k1
      have k2' := (Nat.cast_le (α := ℝ)).2 k2
      rw [Nat.cast_add, Nat.cast_one] at k2'
      constructor <;> linarith
    · intro Y hY
      rw [Nat.totient_two_mul_of_odd hn, add_sub_cancel]
      exact hE Y hY
  · obtain ⟨θ, β, hθ, hβ, hE⟩ := H m a (4 * (m : ℝ)) hm h4 ha (by linarith)
    refine ⟨θ, β, fun _ => 0, hθ, hβ, fun _ => ⟨le_rfl, by linarith⟩, ?_⟩
    intro Y hY
    rw [add_zero]
    exact hE Y hY

theorem primesAPInterval_of_tzRat (h : TZRat) :
    ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ PrimesAPInterval C₀ Cr cr c := by
  obtain ⟨C₀, Cr, cr, cb, h0, h1, h2, h3, H⟩ := tzRat_ratClass h
  obtain ⟨C₀', c, hC, hc, H'⟩ :=
    Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalImpliesProgressions_statement Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound C₀ Cr cr cb h0 h1 h2 h3 H
  exact ⟨C₀', Cr, cr, c, hC, h1, h2, hc, H'⟩

end GlobalTheory.Mem.An
end

