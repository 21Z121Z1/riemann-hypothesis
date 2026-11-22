import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaHalfPeriodValueIsIntegral
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Topology
open Filter

namespace GlobalTheory.HalfPeriodValue

lemma second_order {f f' a s b : ℂ → ℂ} {c : ℂ} (hf : ∀ᶠ z in 𝓝 (0 : ℂ), HasDerivAt f (f' z) z)
    (hf' : HasDerivAt f' c 0) (h0 : f 0 = 0) (h0' : f' 0 = 0) (ha : Differentiable ℂ a)
    (hs : Differentiable ℂ s) (hb : Differentiable ℂ b) (hs0 : s 0 = 0) (hs1 : deriv s 0 = 1)
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), f z * a z = s z ^ 2 * b z) : c * a 0 = 2 * b 0 := by
  have d : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → Differentiable ℂ (deriv g) := fun hg =>
    differentiableOn_univ.1 (hg.differentiableOn.deriv isOpen_univ)
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), f' z * a z + f z * deriv a z =
      (2 * s z * deriv s z) * b z + (s z * s z) * deriv b z := by
    filter_upwards [hf, h.eventually_nhds] with z hz hz'
    have e1 := hz.mul (ha z).hasDerivAt
    have e2 := ((hs z).hasDerivAt.mul (hs z).hasDerivAt).mul (hb z).hasDerivAt
    have e3 := e1.unique (e2.congr_of_eventuallyEq (by
      filter_upwards [hz'] with w hw
      simpa [sq] using hw))
    simp only [Pi.mul_apply] at e3
    linear_combination e3
  have e1 := (hf'.mul (ha 0).hasDerivAt).add (hf.self_of_nhds.mul (d ha 0).hasDerivAt)
  have e2 := ((((hs 0).hasDerivAt.const_mul 2).mul (d hs 0).hasDerivAt).mul (hb 0).hasDerivAt).add
    (((hs 0).hasDerivAt.mul (hs 0).hasDerivAt).mul (d hb 0).hasDerivAt)
  have e3 := e1.unique (e2.congr_of_eventuallyEq (by
      filter_upwards [h1] with w hw
      simpa using hw))
  simp only [Pi.mul_apply, h0, h0', hs0, hs1] at e3
  linear_combination e3

lemma isIntegral_of_eq {u j : ℂ} (hj : IsIntegral ℤ j) (h : (u ^ 12 + 16) ^ 3 = j * u ^ 12) :
    IsIntegral ℤ u := by
  refine IsIntegral.of_pow (n := 12) (by norm_num) ?_
  let R := integralClosure ℤ ℂ
  refine isIntegral_trans (A := R) _ ?_
  refine ⟨(Polynomial.X + 16) ^ 3 - Polynomial.C (⟨j, hj⟩ : R) * Polynomial.X, by monicity!, ?_⟩
  rw [← Polynomial.aeval_def]
  simp only [map_sub, map_pow, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat]
  exact sub_eq_zero.2 h

theorem value_half_period : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → IsIntegral ℤ (1728 * g2 Λ ^ 3) → ∀ t, 2 * t ∈ Λ → t ∉ Λ → U1 Λ t (sgStar Λ) 0 ≠ 0 ∧ IsIntegral ℤ (U1 Λ t (sgStar Λ) 0) ∧ U1 Λ t (sgStar Λ) 0 ^ 8 = 16 * (g2 Λ - 3 * wpF Λ t ^ 2) ∧ 4 * wpF Λ t ^ 3 - g2 Λ * wpF Λ t - g3 Λ = 0 := by
  intro Λ hΛ hΔ hj t h2 ht
  obtain ⟨⟨hd, hd1, hodd, hU⟩, hzero, -, hwp, -⟩ := GlobalTheory.T.oddThetaFunction_existence_uniqueness Λ hΛ
  obtain ⟨w₁, w₂, hli, hΛ⟩ := hΛ
  let L : PeriodPair := ⟨w₁, w₂, hli⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by
    rw [hΛ, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp [L]
  obtain ⟨hg2, hg3, -, -, hw, -⟩ := GlobalTheory.T.latticeInvariants_periodPair_dictionary L Λ hL
  have htL : t ∉ L.lattice := fun h => ht ((hL t).2 h)
  have hP' : L.derivWeierstrassP t = 0 := by
    have e1 := L.derivWeierstrassP_add_coe (-t) ⟨2 * t, (hL _).1 h2⟩
    rw [L.derivWeierstrassP_neg] at e1
    have : -t + 2 * t = t := by ring
    simp only [this] at e1
    linear_combination e1 / 2
  have hcub : 4 * wpF Λ t ^ 3 - g2 Λ * wpF Λ t - g3 Λ = 0 := by
    rw [(hw t ht).1, hg2, hg3, ← L.derivWeierstrassP_sq t htL, hP']
    simp
  set k : ℂ := (Real.pi : ℂ) * (starRingEnd ℂ) t / (area Λ : ℂ) with hk
  have hsys := GlobalTheory.weierstrass_system_add_const L t (z := 0) (by simpa using htL)
  have key := second_order (f := fun z => L.weierstrassP (z + t) - L.weierstrassP t)
    (f' := fun z => L.derivWeierstrassP (z + t))
    (a := fun z => sgStar Λ (z + t) ^ 2 * sgStar Λ t ^ 2) (s := sgStar Λ)
    (b := fun z => Complex.exp (2 * k * z + 2 * k * t))
    (hsys.mono fun z hz => hz.1.sub_const _) hsys.self_of_nhds.2 (by simp) (by simpa using hP')
    (by fun_prop) hd (by fun_prop) ((hzero 0).2 Λ.zero_mem) hd1 (by
      filter_upwards [(continuous_add_const t).continuousAt.eventually
        (GlobalTheory.eventually_notMem_periodLattice L (z := 0 + t) (by simpa using htL))] with z hz
      have hz' : z + t ∉ Λ := fun h => hz ((hL _).1 h)
      have e1 := hwp (z + t) t hz' ht
      rw [(hw _ hz').1, (hw t ht).1] at e1
      have e2 := hU (2 * t) h2 z
      rw [if_neg (by simpa using ht)] at e2
      have e3 : -(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
          (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)) =
          -(2 * k * z + 2 * k * t) := by
        rw [hk, map_mul, map_ofNat]; ring
      simp only [U1] at e2
      rw [e3, Complex.exp_neg] at e2
      have e4 : z + t + t = z + 2 * t := by ring
      rw [e1, e4, add_sub_cancel_right]
      have e5 := Complex.exp_ne_zero (2 * k * z + 2 * k * t)
      rw [mul_inv_eq_iff_eq_mul₀ e5] at e2
      rw [e2]; ring)
  simp only [zero_add, mul_zero] at key
  rw [← (hw t ht).1, ← hg2] at key
  have hu : U1 Λ t (sgStar Λ) 0 ^ 4 * Complex.exp (2 * k * t) = sgStar Λ t ^ 4 := by
    simp only [U1, zero_add]
    rw [mul_pow, mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have : ((4 : ℕ) : ℂ) * (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) t / (area Λ : ℂ) -
      (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) + 2 * k * t = 0 := by
      rw [hk]; push_cast; ring
    rw [this, Complex.exp_zero, mul_one]
  set u := U1 Λ t (sgStar Λ) 0
  set e := wpF Λ t
  have h4 : (12 * e ^ 2 - g2 Λ) * u ^ 4 = 4 := by
    apply mul_right_cancel₀ (Complex.exp_ne_zero (2 * k * t))
    linear_combination 2 * key + (12 * e ^ 2 - g2 Λ) * hu
  have hD : (12 * e ^ 2 - g2 Λ) ^ 2 * (g2 Λ - 3 * e ^ 2) = 1 := by
    have h3 : g3 Λ = 4 * e ^ 3 - g2 Λ * e := by linear_combination -hcub
    rw [← hΔ, TaylorLogMetric.discr, h3]; ring
  have h8 : u ^ 8 = 16 * (g2 Λ - 3 * e ^ 2) := by
    linear_combination (-u ^ 8) * hD +
      (g2 Λ - 3 * e ^ 2) * ((12 * e ^ 2 - g2 Λ) * u ^ 4 + 4) * h4
  refine ⟨fun h => by simp [h] at h4, isIntegral_of_eq hj ?_, h8, hcub⟩
  have h5 : u ^ 12 + 16 = 12 * g2 Λ * u ^ 4 := by
    linear_combination u ^ 4 * h8 - 4 * h4
  rw [h5]; ring

end GlobalTheory.HalfPeriodValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.SerRing

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem norm_finsum_le {ι : Type*} (F : ι → K) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, ‖F i‖ ≤ B) :
    ‖∑ᶠ i, F i‖ ≤ B := by
  refine finsum_induction (p := fun x => ‖x‖ ≤ B) (by simpa using hB) (fun x y hx hy => ?_) h
  exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem norm_coeff_mul_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 0)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) hA

theorem norm_coeff_add_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f + g)‖ ≤ max A B := by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_sub_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f - g)‖ ≤ max A B := by
  rw [map_sub]
  exact (norm_sub_le_max' _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_C_le (c : K) (n : ℕ) : ‖PowerSeries.coeff n (PowerSeries.C c)‖ ≤ ‖c‖ := by
  rw [PowerSeries.coeff_C]
  split_ifs <;> simp

theorem intSer_mul {f g : PowerSeries K} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) := fun n => by
  simpa using norm_coeff_mul_le f g 1 1 hf hg n

theorem intSer_pow {f : PowerSeries K} (hf : IntSer f) (d : ℕ) : IntSer (f ^ d) := by
  induction d with
  | zero => intro n; simpa using norm_coeff_C_le (1 : K) n
  | succ d ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_inv {f : PowerSeries K} (hf : IntSer f) (h0 : ‖PowerSeries.constantCoeff f‖ = 1) :
    IntSer f⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · simp [h0]
    · rw [norm_mul, norm_neg, norm_inv, h0, inv_one, one_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
      split_ifs with hx
      · rw [norm_mul]
        exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hx)
      · simp

theorem norm_coeff_subst_le (f h : PowerSeries K) (B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B)
    (hh : IntSer h) (h0 : PowerSeries.constantCoeff h = 0) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries K)‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 0)
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' h0)]
  refine norm_finsum_le _ hB fun d => ?_
  rw [smul_eq_mul, norm_mul]
  simpa using mul_le_mul (hf d) (intSer_pow hh d n) (norm_nonneg _) hB

theorem series_ring_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  intro p _
  refine ⟨fun f g hf hg => ⟨fun n => ?_, fun n => ?_, intSer_mul hf hg⟩,
    fun f g ⟨A, hf⟩ ⟨B, hg⟩ => ⟨⟨_, norm_coeff_add_le f g A B hf hg⟩, ⟨_, norm_coeff_sub_le f g A B hf hg⟩,
      ⟨_, norm_coeff_mul_le f g A B hf hg⟩⟩,
    fun c => ⟨⟨_, norm_coeff_C_le c⟩, fun hc n => (norm_coeff_C_le c n).trans hc⟩, fun n => ?_,
    fun f => intSer_inv, norm_coeff_subst_le, norm_coeff_mul_le⟩
  · simpa using norm_coeff_add_le f g 1 1 hf hg n
  · simpa using norm_coeff_sub_le f g 1 1 hf hg n
  · rw [PowerSeries.coeff_X]
    split_ifs <;> simp

end GlobalTheory.EvenTheta.SerRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PairingNormalisingConstantLogLeBound
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem extNorm_eq_nat_log_le_bound : ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∃ s : ℕ, 0 < s ∧ extNorm K lam = (s : K) ∧ Real.log s ≤ bound (Fintype.card ι) n R := by
  intro K _ _ _ ι _ n lam R hR hS
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hw : ∀ τ i, (lam τ).natW i ≤ ⌊R⌋₊ := by
    intro τ i
    have hn : 0 < n := Fin.pos i
    have h := hS τ i ⟨n - 1, by omega⟩
    have h2 : (lam τ).w i - (lam τ).w ⟨n - 1, by omega⟩ ≤ (⌊R⌋₊ : ℤ) := by
      rw [Int.natCast_floor_eq_floor hR0]
      exact Int.le_floor.mpr h
    unfold DomWeight.natW DomWeight.detShift
    rw [dif_pos hn]
    omega
  choose s hs0 hs1 hs2 using fun τ => GlobalTheory.T.fockNorm_extremal_vector_eq_bounded_nat n (lam τ) ⌊R⌋₊ (hw τ)
  refine ⟨∏ τ, s τ, Finset.prod_pos fun τ _ => hs0 τ, ?_, ?_⟩
  · unfold extNorm
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl fun τ _ => hs2 τ K
  · rw [Nat.cast_prod, Real.log_prod (fun τ _ => by exact_mod_cast (hs0 τ).ne')]
    have hb := GlobalTheory.T.log_factorial_pow_mul_factorial_pow_le' n ⌊R⌋₊ R hR (Nat.floor_le hR0)
    have h1 : ∀ τ, Real.log (s τ) ≤ 4 * (n : ℝ) * R * Real.log (n * R) := fun τ =>
      le_trans (Real.log_le_log (by exact_mod_cast hs0 τ) (by exact_mod_cast hs1 τ)) hb
    calc ∑ τ, Real.log (s τ) ≤ ∑ _τ : ι, 4 * (n : ℝ) * R * Real.log (n * R) :=
          Finset.sum_le_sum fun τ _ => h1 τ
      _ = bound (Fintype.card ι) n R := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          unfold bound
          ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneFunctionalEquationPadic
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.FunEq

open PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem intSer_mul {f g : K⟦X⟧} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) := by
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

omit [IsUltrametricDist K] in
theorem intSer_C {c : K} (hc : ‖c‖ ≤ 1) : IntSer (C c : K⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · simp

theorem intSer_pow {f : K⟦X⟧} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => simpa using intSer_C (K := K) (c := 1) (by simp)
  | succ n ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_aeval {h : K⟦X⟧} (hh : IntSer h) (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    IntSer (Polynomial.aeval h P) := by
  intro n
  rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hP _) (norm_nonneg _) (intSer_pow hh i n)

theorem intSer_of_funEq (f h A B : K⟦X⟧) (N : ℕ) (hf : constantCoeff f = 1) (hh : IntSer h)
    (hh0 : constantCoeff h = 0) (hh1 : ‖coeff 1 h‖ = 1) (hN : ‖(N : K)‖ < 1) (hA : IntSer A)
    (hA0 : constantCoeff A = 1) (hB : IntSer B) (hB0 : constantCoeff B = 1)
    (e : (PowerSeries.subst h f : K⟦X⟧) * A = f ^ N * B) : IntSer f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf]
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  set P : Polynomial K := trunc n f with hP
  have hPi : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    intro i
    rw [hP, coeff_trunc]
    split_ifs with hi
    · exact ih i hi
    · simp
  have hPs : IntSer (P : K⟦X⟧) := fun i => by rw [Polynomial.coeff_coe]; exact hPi i
  have hP0 : constantCoeff (P : K⟦X⟧) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hn,
      coeff_zero_eq_constantCoeff_apply, hf]
  obtain ⟨Q, hQ⟩ : (X : K⟦X⟧) ^ n ∣ f - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hm, sub_self]
  have hX : ∀ g : K⟦X⟧, coeff n (X ^ n * g) = constantCoeff g := fun g => by
    simpa using coeff_X_pow_mul g n 0
  have hQ0 : constantCoeff Q = coeff n f := by
    rw [← hX, ← hQ, map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_neg (lt_irrefl n), sub_zero]
  obtain ⟨h', hh'⟩ : (X : K⟦X⟧) ∣ h := X_dvd_iff.2 hh0
  have h'0 : constantCoeff h' = coeff 1 h := by
    rw [hh', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hfe : f = (P : K⟦X⟧) + X ^ n * Q := by rw [← hQ]; ring
  have hsQ : constantCoeff (PowerSeries.subst h Q : K⟦X⟧) = constantCoeff Q := by
    obtain ⟨Q', hQ'⟩ : (X : K⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
    have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
    conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
    have hC : (PowerSeries.subst h (C (constantCoeff Q) : K⟦X⟧) : K⟦X⟧) = C (constantCoeff Q) := by
      rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp
    rw [hC]
    simp [hh0]
  have hL : (PowerSeries.subst h f : K⟦X⟧) * A =
      Polynomial.aeval h P * A + X ^ n * (h' ^ n * PowerSeries.subst h Q * A) := by
    conv_lhs => rw [hfe, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs]
    have : h ^ n = X ^ n * h' ^ n := by rw [hh', mul_pow]
    rw [this]; ring
  have hR : f ^ N * B = (P : K⟦X⟧) ^ N * B +
      X ^ n * (Q * (∑ i ∈ Finset.range N, f ^ i * (P : K⟦X⟧) ^ (N - 1 - i)) * B) := by
    have := geom_sum₂_mul f (P : K⟦X⟧) N
    rw [hQ] at this
    linear_combination (-B) * this
  have key := congrArg (coeff n) e
  rw [hL, hR, map_add, map_add, hX, hX] at key
  simp only [map_mul, map_pow, map_sum, hA0, hB0, hf, hP0, hsQ, hQ0, h'0, one_pow, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key
  have h1 := intSer_mul (intSer_aeval hh P hPi) hA n
  have h2 := intSer_mul (intSer_pow hPs N) hB n
  have k2 : (coeff 1 h ^ n - N) * coeff n f =
      coeff n ((P : K⟦X⟧) ^ N * B) - coeff n (Polynomial.aeval h P * A) := by
    linear_combination key
  have hu : ‖coeff 1 h ^ n - (N : K)‖ = 1 := by
    have hp : ‖coeff 1 h ^ n‖ = 1 := by rw [norm_pow, hh1, one_pow]
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hp, norm_neg]; exact hN.ne'), hp, norm_neg, max_eq_left hN.le]
  have := congrArg norm k2
  rw [norm_mul, hu, one_mul] at this
  rw [this, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rwa [norm_neg]))

theorem intSer_of_funEq_padic : ∀ (p : ℕ) [Fact p.Prime] (f h A B : PowerSeries ℂ_[p]) (N : ℕ), PowerSeries.constantCoeff f = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖(N : ℂ_[p])‖ < 1 → IntSer A → PowerSeries.constantCoeff A = 1 → IntSer B → PowerSeries.constantCoeff B = 1 → (PowerSeries.subst h f : PowerSeries ℂ_[p]) * A = f ^ N * B → IntSer f :=
  fun _ _ f h A B N => intSer_of_funEq f h A B N

end GlobalTheory.EvenTheta.FunEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneRootCoprimePadic
section
open scoped BigOperators

noncomputable section
namespace GlobalTheory.RootInt

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem intSer_mul {f g : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (hg : GlobalTheory.EvenTheta.IntSer g) :
    GlobalTheory.EvenTheta.IntSer (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem intSer_pow {f : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (N : ℕ) :
    GlobalTheory.EvenTheta.IntSer (f ^ N) := by
  induction N with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ N ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_of_pow {N : ℕ} (hN : ‖(N : K)‖ = 1) {s : PowerSeries K}
    (hs0 : PowerSeries.constantCoeff s = 1) (hsN : GlobalTheory.EvenTheta.IntSer (s ^ N)) :
    GlobalTheory.EvenTheta.IntSer s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0, norm_one]
  set a : PowerSeries K := PowerSeries.mk fun k => if k < n then PowerSeries.coeff k s else 0 with ha
  have hca : ∀ k, PowerSeries.coeff k a = if k < n then PowerSeries.coeff k s else 0 := fun k => by
    rw [ha, PowerSeries.coeff_mk]
  have hai : GlobalTheory.EvenTheta.IntSer a := fun k => by
    rw [hca]; split_ifs with h
    · exact ih k h
    · simp
  have hcb : ∀ k, PowerSeries.coeff k (s - a) = if k < n then 0 else PowerSeries.coeff k s := fun k => by
    rw [map_sub, hca]; split_ifs <;> simp
  set G : PowerSeries K := ∑ i ∈ Finset.range N, s ^ i * a ^ (N - 1 - i) with hG
  have hGN : G * (s - a) = s ^ N - a ^ N := geom_sum₂_mul s a N
  have ha0 : PowerSeries.constantCoeff a = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hca, if_pos hn,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0]
  have hG0 : PowerSeries.coeff 0 G = N := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hG, map_sum]
    simp [hs0, ha0]
  have key : PowerSeries.coeff n (G * (s - a)) = (N : K) * PowerSeries.coeff n s := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [hG0, hcb, if_neg (lt_irrefl n)]
    · rintro ⟨i, j⟩ hij hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      have hj : j < n := by
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact absurd (by simp at hij; simp [hij]) hne
        · omega
      simp only
      rw [hcb, if_pos hj, mul_zero]
    · intro h; exact absurd (by simp) h
  have h1 : ‖(N : K) * PowerSeries.coeff n s‖ ≤ 1 := by
    rw [← key, hGN, map_sub]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hsN n) ?_)
    rw [norm_neg]; exact intSer_pow hai N n
  rwa [norm_mul, hN, one_mul] at h1

end GlobalTheory.RootInt

theorem GlobalTheory.RootInt.intSer_root : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  intro p _ N _ hcop s hs0 hsN
  refine GlobalTheory.RootInt.intSer_of_pow ?_ hs0 hsN
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact hcop.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralCharImEqZeroStatement
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_cexp_im_herm_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ v : V, v ≠ 0 → (∀ y ∈ Λ, ∃ m : ℤ, (H v y).im = m) → ∫ z in Fd, cexp (2 * π * I * ((H v z).im : ℂ)) ∂μ = 0 := by
  first | exact @GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero | exact GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero | (intros; apply GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarValueLeMeanSquareGenusOneStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStar_value_le_meanSquare_genusOne : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t, ‖U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ)) 0‖ ^ 2 ≤ 3 * (2 * D.host.rdE + 1) * nrm1Sq (lamOf D cc δ) (sgStar (lamOf D cc δ)) := by
  first | exact @GlobalTheory.GenusOneSup.value_le_mean_square | exact GlobalTheory.GenusOneSup.value_le_mean_square | (intros; apply GlobalTheory.GenusOneSup.value_le_mean_square <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignedTranslationAddSelfDualLatticeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedTranslation_add_selfDual_lattice : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → (∀ x ∈ A, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A, w0 D • x ∈ A) → ∀ x ∈ A, ∀ y ∈ A, al D T (x + y) = al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) := by
  first | exact @GlobalTheory.GalTheta.al_add | exact GlobalTheory.GalTheta.al_add | (intros; apply GlobalTheory.GalTheta.al_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableExpNegHermStatement
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_exp_neg_herm_add_norm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (C : ℝ), Summable (fun x : Λ => Real.exp (-(π / 2) * (H x x).re + C * ‖(x : V)‖)) := by
  first | exact @GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm | exact GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm | (intros; apply GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm <;> assumption)
end

