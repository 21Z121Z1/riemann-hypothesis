import Mathlib
import Formalism.PairingDivisors.StatementN
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesExponentLogSumLe
section
open Finset

namespace GlobalTheory

theorem ceSum_val_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (X : ℕ) :
    ∑ l ∈ S, (padicValNat l X : ℝ) * Real.log l ≤ Real.log X := by
  have h1 : ∑ l ∈ S, (padicValNat l X : ℝ) * Real.log l
      = ∑ l ∈ S, (X.factorization l : ℝ) * Real.log l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def X (hS l hl)]
  rw [h1, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have hsub : S ⊆ S ∪ X.factorization.support := Finset.subset_union_left
  calc ∑ l ∈ S, (X.factorization l : ℝ) * Real.log l
      ≤ ∑ l ∈ S ∪ X.factorization.support, (X.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun l hl _ => ?_
        rcases Finset.mem_union.1 hl with h | h
        · exact mul_nonneg (Nat.cast_nonneg _)
            (Real.log_nonneg (by exact_mod_cast (hS l h).one_lt.le))
        · have hp : l.Prime := Nat.prime_of_mem_primeFactors (by simpa using h)
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    _ = ∑ l ∈ X.factorization.support, (X.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_subset Finset.subset_union_right fun l _ hl => ?_).symm
        rw [Finsupp.notMem_support_iff.1 hl]
        simp

theorem ceSum_small_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (n : ℕ) :
    ∑ l ∈ S, (if l ≤ n then Real.log l else 0) ≤ n * Real.log 4 := by
  rw [← Finset.sum_filter]
  calc ∑ l ∈ S.filter (· ≤ n), Real.log (l : ℝ)
      ≤ ∑ l ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (l : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun l hl _ => ?_
        · intro l hl
          rcases Finset.mem_filter.1 hl with ⟨hlS, hln⟩
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hS l hlS⟩
        · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.1 hl).2.one_lt.le)
    _ = Real.log (primorial n : ℝ) := by
        rw [primorial, Nat.cast_prod, Real.log_prod]
        intro l hl
        exact_mod_cast (Finset.mem_filter.1 hl).2.ne_zero
    _ ≤ Real.log ((4 : ℝ) ^ n) := by
        apply Real.log_le_log (by exact_mod_cast primorial_pos n)
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]

end GlobalTheory

namespace GlobalTheory

open Formalism.PairingDivisionLocalBalance in

theorem ceSum_term_le (f X l : ℕ) (hX : X ≠ 0) (hp : l.Prime) :
    ((f * padicValNat l 2 + mE l X : ℕ) : ℝ) * Real.log l ≤
      (padicValNat l X : ℝ) * Real.log l + (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0)
        + (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
        + (if l ≤ X / 2 + 1 then Real.log l else 0) := by
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hv : (0 : ℝ) ≤ padicValNat l X := Nat.cast_nonneg _
  have hvl : 0 ≤ (padicValNat l X : ℝ) * Real.log l := mul_nonneg hv hlog
  have hB : 0 ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0) := by
    split_ifs
    · exact Real.log_nonneg (by have : (0 : ℝ) ≤ X := Nat.cast_nonneg _; linarith)
    · exact le_rfl
  have hC : 0 ≤ (if l ≤ X / 2 + 1 then Real.log l else 0) := by
    split_ifs
    · exact hlog
    · exact le_rfl
  by_cases h2 : l = 2
  · subst h2
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hm : mE 2 X = 2 + padicValNat 2 X := by simp [mE]
    have h22 : padicValNat 2 2 = 1 := by simp
    have e : ((f * padicValNat 2 2 + mE 2 X : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ)
        = (padicValNat 2 X : ℝ) * Real.log ((2 : ℕ) : ℝ) + ((f : ℝ) + 2) * Real.log 2 := by
      rw [hm, h22]; push_cast; ring
    rw [if_pos rfl, e]
    linarith
  · have hA : (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0) = 0 := if_neg h2
    have hv2 : padicValNat l 2 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    rw [hA, hv2]
    by_cases hd : (l - 1) ∣ X
    · have hm : mE l X = 1 + padicValNat l X := by simp [mE, h2, hd]
      rw [hm]
      push_cast
      have key : Real.log (l : ℝ) ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
          + (if l ≤ X / 2 + 1 then Real.log l else 0) := by
        by_cases hXl : l = X + 1
        · rw [if_pos hXl]
          have : (l : ℝ) = (X : ℝ) + 1 := by exact_mod_cast hXl
          have e : Real.log (l : ℝ) = Real.log ((X : ℝ) + 1) := by rw [this]
          linarith
        · rw [if_neg hXl]
          have hl3 : 3 ≤ l := by have := hp.two_le; omega
          obtain ⟨k, hk⟩ := hd
          have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hX hk
          have hk1 : k ≠ 1 := by rintro rfl; apply hXl; omega
          have hk2 : (l - 1) * 2 ≤ (l - 1) * k := Nat.mul_le_mul_left _ (by omega)
          have hle : l - 1 ≤ X / 2 := by
            rw [Nat.le_div_iff_mul_le (by norm_num)]
            rw [hk]; exact hk2
          rw [if_pos (by omega)]
          linarith
      nlinarith
    · have hm : mE l X = 0 := by simp [mE, h2, hd]
      rw [hm]
      simp only [mul_zero, add_zero, Nat.cast_zero, zero_mul]
      linarith

end GlobalTheory

namespace GlobalTheory

theorem dividedPowerValuations_cESum : Formalism.PairingDivisionLocalBalance.CESum := by
  intro f X S hX hfX hS
  have hX0 : X ≠ 0 := by omega
  have hsum := Finset.sum_le_sum fun l hl => ceSum_term_le f X l hX0 (hS l hl)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hv := ceSum_val_le S hS X
  have hs := ceSum_small_le S hS (X / 2 + 1)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hXr : (16 : ℝ) ≤ X := by exact_mod_cast hX
  have hL0 : 0 ≤ Real.log ((X : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hA : ∑ l ∈ S, (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0)
      ≤ ((f : ℝ) + 2) * Real.log 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hB : ∑ l ∈ S, (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
      ≤ Real.log ((X : ℝ) + 1) := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hL0
  have hlogX : Real.log (X : ℝ) ≤ Real.log ((X : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL4 : 4 * Real.log 2 ≤ Real.log ((X : ℝ) + 1) := by
    have : Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← this]
    exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; norm_num
  have hn : (((X / 2 + 1 : ℕ)) : ℝ) * 2 ≤ X + 2 := by
    have : (X / 2 + 1) * 2 ≤ X + 2 := by omega
    exact_mod_cast this
  have hf : (f : ℝ) * 2 ≤ X := by exact_mod_cast (by omega : f * 2 ≤ X)
  rw [h4] at hs
  have p1 : 0 ≤ ((X : ℝ) - 2 * f) * Real.log 2 := mul_nonneg (by linarith) hlog2
  have p2 : 0 ≤ ((X : ℝ) + 2 - ((X / 2 + 1 : ℕ) : ℝ) * 2) * Real.log 2 :=
    mul_nonneg (by linarith) hlog2
  have p3 : 0 ≤ ((X : ℝ) - 2) * (Real.log ((X : ℝ) + 1) - 4 * Real.log 2) :=
    mul_nonneg (by linarith) (by linarith)
  have p4 : 0 ≤ ((X : ℝ) - 16) * Real.log 2 := mul_nonneg (by linarith) hlog2
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CochainCoboundaryProdHomIdentities
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem cochain_coboundary_prod_hom_identities :
    ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
    (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
    η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
    (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  intro Γ _ N x y η h
  refine ⟨?_, ?_, ?_⟩
  · have h0 := h 1 1
    simp only [map_one, toAdd_one, zero_mul, mul_one] at h0
    linear_combination -h0
  · intro g n
    have h1 := h g n
    have h2 := h (g * n * g⁻¹) g
    have e : g * n * g⁻¹ * g = g * n := by group
    have e2 : (x (g * n * g⁻¹)).toAdd = (x n).toAdd := by
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
      ring
    rw [e, e2] at h2
    linear_combination h1 - h2
  · intro m n hm
    have h3 := h m n
    rw [hm, zero_mul] at h3
    linear_combination h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfExpDecayOfIntegralIdentity
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
open Filter Topology Set MeasureTheory

namespace GlobalTheory

theorem ode_coeff_zero_of_decay_ends : ∀ (v : ℝ → ℂ) (K c : ℂ) (C α β : ℝ) (w : ℕ), 1 ≤ w → 0 < α → 0 < β → K ≠ 0 → (∀ y : ℝ, 0 < y → ‖v y‖ ≤ C * y ^ ((w : ℝ) / 2) * Real.exp (-α * y)) → (∀ a b : ℝ, 0 < a → a ≤ b → v b - v a = K * c * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-β * y) : ℂ)) → c = 0 := by
  intro v K c C α β w hw hα hβ hK hbound hdiff
  set g : ℝ → ℝ := fun y => y ^ w * Real.exp (-β * y) with hg
  have gcont : Continuous g := by fun_prop
  have hint : ∀ a b : ℝ, (∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-β * y) : ℂ)) = ((∫ y in a..b, g y : ℝ) : ℂ) := by
    intro a b
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    ext y
    simp [g]
  set I := ∫ y in (1:ℝ)..2, g y with hIdef
  have hI : 0 < I := intervalIntegral.intervalIntegral_pos_of_pos_on (gcont.intervalIntegrable _ _)
    (fun x hx => by
      have : 0 < x := by linarith [hx.1]
      simp only [g]; positivity) (by norm_num)
  have key : ∀ a b : ℝ, 0 < a → a ≤ 1 → 2 ≤ b → ‖K * c‖ * I ≤ ‖v b‖ + ‖v a‖ := by
    intro a b ha ha1 hb2
    have h1 := hdiff a b ha (by linarith)
    have hmono : I ≤ ∫ y in a..b, g y := by
      apply intervalIntegral.integral_mono_interval ha1 (by norm_num) hb2
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        have : 0 < y := lt_trans ha hy.1
        simp only [g, Pi.zero_apply]; positivity
      · exact gcont.intervalIntegrable _ _
    calc ‖K * c‖ * I ≤ ‖K * c‖ * ∫ y in a..b, g y := mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
      _ ≤ ‖K * c‖ * |∫ y in a..b, g y| := mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
      _ = ‖v b - v a‖ := by rw [h1, hint, norm_mul (K * c) _, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖v b‖ + ‖v a‖ := norm_sub_le _ _
  have hw2 : (0:ℝ) < (w:ℝ) / 2 := by
    have : (1:ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have h0 : Tendsto (fun a => ‖v a‖) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun a : ℝ => C * a ^ ((w:ℝ)/2) * Real.exp (-α * a)) (𝓝[>] 0) (𝓝 0) := by
      have hca : ContinuousAt (fun a : ℝ => C * a ^ ((w:ℝ)/2) * Real.exp (-α * a)) 0 := by
        apply ContinuousAt.mul
        · exact ContinuousAt.mul continuousAt_const (Real.continuousAt_rpow_const _ _ (Or.inr hw2.le))
        · fun_prop
      have h := hca.tendsto
      simp only [Real.zero_rpow hw2.ne', mul_zero, zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hc
    filter_upwards [self_mem_nhdsWithin] with a ha using hbound a ha
  have hinf : Tendsto (fun b => ‖v b‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun b : ℝ => C * (b ^ ((w:ℝ)/2) * Real.exp (-α * b))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((w:ℝ)/2) α hα).const_mul C
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hc
    filter_upwards [eventually_gt_atTop 0] with b hb
    rw [← mul_assoc]; exact hbound b hb
  have step : ∀ b : ℝ, 2 ≤ b → ‖K * c‖ * I ≤ ‖v b‖ := by
    intro b hb
    have ht : Tendsto (fun a => ‖v b‖ + ‖v a‖) (𝓝[>] 0) (𝓝 (‖v b‖ + 0)) := tendsto_const_nhds.add h0
    rw [add_zero] at ht
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))] with a ha ha1
    exact key a b ha (le_of_lt ha1) hb
  have hle : ‖K * c‖ * I ≤ 0 :=
    ge_of_tendsto hinf (by filter_upwards [eventually_ge_atTop 2] with b hb using step b hb)
  have hKc : ‖K * c‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (K * c)]) (norm_nonneg _)
  rw [norm_eq_zero, mul_eq_zero] at hKc
  exact hKc.resolve_left hK

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfSumPlusMinusRepsEqZero
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem coeff_eq_zero_of_sum_reps_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ))
    (b : SL(2, ℤ) → ℕ → ℂ), 0 < M → IsReps Γ s →
    (∀ (x : SL(2, ℤ)) (n : ℕ), b (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * b x n) →
    (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), b (γ * x) n = b x n) → (∀ (x : SL(2, ℤ)) (n : ℕ), b (-x) n = -b x n) →
    (∀ i, ∑ n ∈ Finset.range M, b (s i) n = 0) → ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → b x n = 0 := by
  intro M Γ r s b hM hs hT hΓ hneg hsum x n hn
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / M)) M :=
    Complex.isPrimitiveRoot_exp M hM.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / M) with hζ
  have hB : ∀ y : SL(2, ℤ), ∑ k ∈ Finset.range M, b y k = 0 := by
    intro y
    obtain ⟨i, γ, hγ, rfl | rfl⟩ := hs.1 y
    · simp only [hΓ γ hγ]; exact hsum i
    · simp only [hneg, hΓ γ hγ, Finset.sum_neg_distrib, hsum i, neg_zero]
  have hTm : ∀ (m : ℕ) (y : SL(2, ℤ)) (k : ℕ), b (y * ModularGroup.T ^ m) k = (ζ ^ k) ^ m * b y k := by
    intro m
    induction m with
    | zero => intro y k; simp
    | succ m ih => intro y k; rw [pow_succ, ← mul_assoc, hT, ih, pow_succ]; ring
  have hinj : Function.Injective (fun j : Fin M => ζ ^ (j : ℕ)) := by
    intro i j h
    exact Fin.ext (hprim.pow_inj i.2 j.2 h)
  have hv := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (R := ℂ)
    (f := fun j : Fin M => ζ ^ (j : ℕ)) (v := fun j : Fin M => b x j) hinj (by
      intro i
      have h0 := hB (x * ModularGroup.T ^ (i : ℕ))
      rw [← Fin.sum_univ_eq_sum_range] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hTm, mul_comm])
  have := congrFun hv ⟨n, hn⟩
  simpa using this

end GlobalTheory.OddFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedProperties
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem cosetTrace_fixed_props : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)], ∀ z ∈ Fix L N, (∀ g : G, g • cosetTrace N z = cosetTrace N z) ∧ (v z ≤ 1 → v (cosetTrace N z) ≤ 1) ∧ ∀ e : L, (∀ g : G, g • e = e) → cosetTrace N (e * z) = e * cosetTrace N z := by
  intro L _ v G _ _ hv N _ z hz
  have hfix : ∀ n : G, n ∈ N → n • z = z := fun n hn => hz ⟨n, hn⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g
    unfold cosetTrace
    rw [Finset.smul_sum]
    have key : ∀ q : G ⧸ N, g • q.out • z = (g • q).out • z := by
      intro q
      have h1 : (QuotientGroup.mk (g * q.out) : G ⧸ N) = g • q := by
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h2 : ((g • q).out)⁻¹ * (g * q.out) ∈ N := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', h1]
      have h3 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
      rw [smul_smul, h3, mul_smul, hfix _ h2]
    simp_rw [key]
    exact Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ N => q.out • z)
  · intro hz1
    unfold cosetTrace
    apply Valuation.map_sum_le
    intro q _
    rw [hv]; exact hz1
  · intro e he
    unfold cosetTrace
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [smul_mul', he]

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormGamma1InterGamma0SlashRatIsZeroAt
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.Hk

private theorem finiteIndex_lev_of_pos' (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

private theorem isCusp_SL2Z_ratGL_smul' (g : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem cuspForm_slash_rat_isZeroAt : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l →
    0 < (g.det : ℚ) → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ,
    IsCusp c (GlobalTheory.Hk.lev N l) →
    c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  intro N l k g hN hl _ f c hc
  haveI := finiteIndex_lev_of_pos' N l hN hl
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [← OnePoint.IsZeroAt.smul_iff]
  have h := isCusp_SL2Z_ratGL_smul' g hc
  rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((GlobalTheory.Hk.lev N l : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ))] at h
  exact f.zero_at_cusps' h

end GlobalTheory.Hk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormSlashHoloDecay
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
open scoped Manifold Pointwise

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_norm_le_exp_of_one_le_im (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] (k : ℤ)
    (g : CuspForm G k) :
    ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖g τ‖ ≤ C * Real.exp (-c * τ.im) := by
  obtain ⟨c, hc, hd⟩ := CuspFormClass.exp_decay_atImInfty' (Γ := G) (k := k) g
  obtain ⟨C₀, hC₀⟩ := CuspFormClass.petersson_bounded_left k G g g
  obtain ⟨D, hD, h⟩ := hd.exists_pos
  rw [Asymptotics.IsBigOWith, atImInfty, eventually_comap, eventually_atTop] at h
  obtain ⟨y, hy⟩ := h
  have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ UpperHalfPlane.I)
  set M : ℝ := 1 + C₀ * |y| ^ k.natAbs with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨max D (M * Real.exp (c * |y|)), c, hc, fun τ hτ => ?_⟩
  rcases le_total y τ.im with h1 | h1
  · have h2 := hy _ h1 τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · have hy' : τ.im ≤ |y| := h1.trans (le_abs_self y)
    have hp : ‖g τ‖ ^ 2 * τ.im ^ k ≤ C₀ := by
      have := hC₀ τ
      simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, norm_zpow,
        Complex.norm_real, Real.norm_of_nonneg τ.im_pos.le] at this
      calc _ = ‖g τ‖ * ‖g τ‖ * τ.im ^ k := by ring
        _ ≤ C₀ := this
    have hpos := τ.im_pos
    have hk : 1 ≤ τ.im ^ k * τ.im ^ k.natAbs := by
      rw [← zpow_natCast, ← zpow_add₀ hpos.ne']
      exact one_le_zpow₀ hτ (by omega)
    have h4 : ‖g τ‖ ^ 2 ≤ C₀ * |y| ^ k.natAbs :=
      calc ‖g τ‖ ^ 2 ≤ ‖g τ‖ ^ 2 * (τ.im ^ k * τ.im ^ k.natAbs) :=
            le_mul_of_one_le_right (by positivity) hk
        _ = ‖g τ‖ ^ 2 * τ.im ^ k * τ.im ^ k.natAbs := by ring
        _ ≤ C₀ * |y| ^ k.natAbs := by gcongr
    have h5 : ‖g τ‖ ≤ M := by nlinarith [sq_nonneg (‖g τ‖ - 1), norm_nonneg (g τ)]
    have h3 : 1 ≤ Real.exp (c * |y|) * Real.exp (-c * τ.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc ‖g τ‖ ≤ M := h5
      _ ≤ M * (Real.exp (c * |y|) * Real.exp (-c * τ.im)) := le_mul_of_one_le_right hM0 h3
      _ = M * Real.exp (c * |y|) * Real.exp (-c * τ.im) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem cuspForm_slash_holo_decay : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex →
    ∀ (f : CuspForm Γ k) (σ : SL(2, ℤ)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] σ) ∧
      ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(⇑f ∣[k] σ) τ‖ ≤ C * Real.exp (-c * τ.im) := by
  intro Γ k hΓ f σ
  have : ((ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹) • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Γ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ σ)⁻¹
  exact ⟨(CuspForm.translate f (σ : GL (Fin 2) ℝ)).holo',
    cuspForm_norm_le_exp_of_one_le_im _ k (CuspForm.translate f (σ : GL (Fin 2) ℝ))⟩

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMatrixNormalizesGammaOneGammaZeroLevel
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem diam_conj_mem (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)) (hσ : IsDiam N l d σ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Lev N l) : σ * γ * σ⁻¹ ∈ Lev N l := by
  obtain ⟨hσ0, -⟩ := hσ
  rw [Lev, Subgroup.mem_inf] at hγ ⊢
  obtain ⟨hγ1, hγ0⟩ := hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hσ0
  have hσl : σ ∈ CongruenceSubgroup.Gamma0 l := by
    rw [CongruenceSubgroup.Gamma0_mem]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ0 ⊢
    exact dvd_trans (by exact_mod_cast Dvd.intro_left N rfl) hσ0
  have hσN : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ0 ⊢
    exact dvd_trans (by exact_mod_cast Dvd.intro l rfl) hσ0
  refine ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem] at hγ1 ⊢
    obtain ⟨h00, h11, h10⟩ := hγ1
    have hdet := σ.2
    rw [Matrix.det_fin_two] at hdet
    have hdet' : ((σ 0 0 : ℤ) : ZMod N) * ((σ 1 1 : ℤ) : ZMod N) - ((σ 0 1 : ℤ) : ZMod N) * ((σ 1 0 : ℤ) : ZMod N) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hdet
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_add, Int.cast_mul, Int.cast_neg]
    set a : ZMod N := ((σ 0 0 : ℤ) : ZMod N)
    set b : ZMod N := ((σ 0 1 : ℤ) : ZMod N)
    set c : ZMod N := ((σ 1 0 : ℤ) : ZMod N)
    set e : ZMod N := ((σ 1 1 : ℤ) : ZMod N)
    set p : ZMod N := ((γ 0 0 : ℤ) : ZMod N)
    set q : ZMod N := ((γ 0 1 : ℤ) : ZMod N)
    set r : ZMod N := ((γ 1 0 : ℤ) : ZMod N)
    set s : ZMod N := ((γ 1 1 : ℤ) : ZMod N)
    refine ⟨?_, ?_, ?_⟩
    · linear_combination hdet' + a * e * h00 + b * e * h10 - a * q * hσN - b * c * h11
    · linear_combination hdet' + a * e * h11 - b * c * h00 - b * e * h10 + a * q * hσN
    · linear_combination e * p * hσN + e * e * h10 - c * q * hσN - e * s * hσN
  · exact (CongruenceSubgroup.Gamma0 l).mul_mem ((CongruenceSubgroup.Gamma0 l).mul_mem hσl hγ0)
      ((CongruenceSubgroup.Gamma0 l).inv_mem hσl)

theorem diam_normalises_lev : ∀ (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    ∀ γ : Lev N l, ∃ γ' : Lev N l, mat σ * mat γ = mat γ' * mat σ := by
  intro N l d σ hσ γ
  refine ⟨⟨σ * (γ : SL(2, ℤ)) * σ⁻¹, diam_conj_mem N l d σ hσ γ γ.2⟩, ?_⟩
  simp only [mat, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

end GlobalTheory.HeckeFamilyMatrices
end

