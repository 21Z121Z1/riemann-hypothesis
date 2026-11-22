import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisTaylorSeriesCanonicalOddThetaAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneEvenNormUnitAtTwo
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem norm_eq_one_or_of_add_eq_one {L : Type*} [NormedField L] [IsUltrametricDist L] {b c : L}
    (h : b + c = 1) (hn : ‖b * c‖ < 1) : ‖b‖ = 1 ∨ ‖c‖ = 1 := by
  by_contra hne
  push_neg at hne
  obtain ⟨hb, hc⟩ := hne
  rw [norm_mul] at hn
  have h1 : ‖c‖ = max 1 ‖b‖ := by
    have : c = 1 + -b := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hb.symm)]
    simp
  have h2 : ‖b‖ = max 1 ‖c‖ := by
    have : b = 1 + -c := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hc.symm)]
    simp
  have h3 : 1 ≤ ‖c‖ := h1 ▸ le_max_left _ _
  have h4 : 1 ≤ ‖b‖ := h2 ▸ le_max_left _ _
  nlinarith

theorem norm_two_mul_natCast_lt_one (k : ℕ) : ‖((2 * k : ℕ) : ℂ_[2])‖ < 1 := by
  have h2 : ‖(2 : ℂ_[2])‖ < 1 := by
    have : (2 : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] ((2 : ℕ) : ℚ_[2]) := by simp [map_ofNat]
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hk : ‖(k : ℂ_[2])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
  push_cast
  rw [norm_mul]
  nlinarith [norm_nonneg (k : ℂ_[2]), norm_nonneg (2 : ℂ_[2])]

theorem exists_int_trace_one_unit_at_two :
    ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∃ (a : 𝓞 D.host.K) (β : ℂ) (k : ℕ), D.host.φ₀ (((a : D.host.K) : D.host.E)) = β ∧ β ∈ Qbar ∧ ‖lamC lam β‖ = 1 ∧ β + starRingEnd ℂ β = 1 ∧ β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) ∧ ∀ (Λ : AddSubgroup ℂ) (t₀ : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D Λ t₀ → β * t₀ ∉ Λ ∧ (1 - β) * t₀ ∉ Λ := by
  intro D lam
  have hm : ∀ x, D.host.φ₀ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k := ⟨(D.host.d + 1) / 8, by omega⟩
  have hk' : (D.host.d : ℂ) + 1 = 8 * (k : ℂ) := by exact_mod_cast hk
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hw : StandardLatticesGL3.w0 D = (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := rfl
  have hw' : 1 - StandardLatticesGL3.w0 D = (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := by
    rw [hw]; ring
  have hc : starRingEnd ℂ (StandardLatticesGL3.w0 D) = 1 - StandardLatticesGL3.w0 D := by
    rw [hw', hw, map_div₀, map_add, map_mul, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hp : StandardLatticesGL3.w0 D * (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ) := by
    rw [hw', hw]
    push_cast
    linear_combination (1 / 4 : ℂ) * hk' + (1 / 4 : ℂ) * hs
      - (1 / 4 : ℂ) * ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have hQ : StandardLatticesGL3.w0 D ∈ Qbar := ha ▸ hm _
  have hQ' : 1 - StandardLatticesGL3.w0 D ∈ Qbar := Qbar.sub_mem Qbar.one_mem hQ
  have hadd : lamC lam (StandardLatticesGL3.w0 D) + lamC lam (1 - StandardLatticesGL3.w0 D) = 1 := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_add, ← map_one lam]
    congr 1
    apply Subtype.ext
    simp
  have hmul : lamC lam (StandardLatticesGL3.w0 D) * lamC lam (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ_[2]) := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_mul, ← map_natCast lam]
    congr 1
    apply Subtype.ext
    exact hp.trans (by simp; exact Or.inl rfl)
  rcases norm_eq_one_or_of_add_eq_one hadd (hmul ▸ norm_two_mul_natCast_lt_one k) with h | h
  · refine ⟨a, StandardLatticesGL3.w0 D, k, ha, hQ, h, by rw [hc]; ring, by rw [hc, hp], ?_⟩
    intro Λ t ht
    exact ⟨ht.2.1, hw' ▸ ht.2.2⟩
  · refine ⟨1 - a, 1 - StandardLatticesGL3.w0 D, k, ?_, hQ', h, ?_, ?_, ?_⟩
    · rw [← ha]
      simp
    · rw [map_sub, map_one, hc]; ring
    · rw [map_sub, map_one, hc, ← hp]; ring
    · intro Λ t ht
      rw [sub_sub_cancel]
      exact ⟨hw' ▸ ht.2.2, ht.2.1⟩

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeTo
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TraceOne

theorem exists_of_sq (D : D7) (q n : ℕ) (hn : n % 4 = 3) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n + 1 = 4 * m := ⟨(n + 1) / 4, by omega⟩
  have hm' : (n : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
  have hint : IsIntegral ℤ ((1 + b) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, map_natCast]
      linear_combination (1 / 4 : D.host.E) * hb - (1 / 4 : D.host.E) * hm'
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  have hcw : D.host.conj ((1 + b) / 2) = (1 - b) / 2 := by
    rw [map_div₀, map_add, map_one, map_ofNat, hconj, sub_eq_add_neg]
  let w : 𝓞 D.host.E := ⟨(1 + b) / 2, hint⟩
  have hw : (w : D.host.E) = (1 + b) / 2 := rfl
  have hs : ((sgO D w : 𝓞 D.host.E) : D.host.E) = (1 - b) / 2 := by rw [sgO_coe, hw, hcw]
  refine ⟨w, ?_, fun P hP hq hmem => ?_⟩
  · apply RingOfIntegers.coe_injective
    rw [map_add, map_one]
    change (w : D.host.E) + ((sgO D w : 𝓞 D.host.E) : D.host.E) = 1
    rw [hw, hs]; ring
  · have hsq : (w - sgO D w) * -(w - sgO D w) = (n : 𝓞 D.host.E) := by
      apply RingOfIntegers.coe_injective
      rw [map_mul, map_neg, map_sub, map_natCast]
      change ((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) *
        -((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) = _
      rw [hw, hs]
      linear_combination (-1 : D.host.E) * hb
    have hnP : (n : 𝓞 D.host.E) ∈ P := hsq ▸ P.mul_mem_right _ hmem
    obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2
      (huv ▸ P.add_mem (P.mul_mem_left u hq) (P.mul_mem_left v hnP)))

theorem exists_trace_one : ∀ (D : D7) (q : ℕ), q.Prime → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  intro D q hq
  obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
  by_cases h : q = D.host.d
  · refine exists_of_sq D q D.host.q (by omega) ((Nat.coprime_primes hq hq₁).2 (by omega))
      (D.host.sqq) D.host.sqq_sq
  · exact exists_of_sq D q D.host.d (by omega) ((Nat.coprime_primes hq hd).2 h)
      (D.host.sqd) (D.host.sqd_sq)

end GlobalTheory.TraceOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeries
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpSeries

open PowerSeries

variable {K : Type} [Field K]

def euler (R : PowerSeries K) : PowerSeries K := X * derivativeFun R

theorem coeff_euler (R : PowerSeries K) (n : ℕ) : coeff n (euler R) = (n : K) * coeff n R := by
  cases n with
  | zero => simp [euler]
  | succ n =>
    rw [euler, coeff_succ_X_mul,
      show coeff n (derivativeFun R) = coeff (n + 1) R * ((n : K) + 1) from coeff_derivative R n]
    push_cast
    ring

theorem euler_one_add (R : PowerSeries K) : euler (1 + X * R) = X * (R + euler R) := by
  ext n
  cases n with
  | zero => simp [coeff_euler]
  | succ n =>
    simp only [coeff_euler, map_add, coeff_succ_X_mul, coeff_one]
    simp
    ring

def inv4 (R : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => coeff n R / (4 * ((n : K) + 2))

theorem inverseShiftedEulerOperatorFour_eq_iff [CharZero K] (R S : PowerSeries K) :
    inv4 S = R ↔ S = 4 * (2 * R + euler R) := by
  have h4 : (4 : PowerSeries K) = C 4 := (map_ofNat _ 4).symm
  have h2 : (2 : PowerSeries K) = C 2 := (map_ofNat _ 2).symm
  rw [PowerSeries.ext_iff, PowerSeries.ext_iff]
  refine forall_congr' fun n => ?_
  have hn : (4 * ((n : K) + 2)) ≠ 0 := by
    have : ((n : K) + 2) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    exact mul_ne_zero (by norm_num) this
  rw [inv4, coeff_mk, div_eq_iff hn, h4, h2, coeff_C_mul, map_add, coeff_C_mul, coeff_euler]
  constructor <;> intro h <;> rw [h] <;> ring

def rest (a b : K) (R : PowerSeries K) : PowerSeries K :=
  (euler R - R) ^ 2 - 12 * R ^ 2 - 4 * X * R ^ 3 + C a * X ^ 2 * (1 + X * R) + C b * X ^ 4

theorem contract (a b : K) (n : ℕ) (x y : PowerSeries K) (h : X ^ n ∣ x - y) :
    X ^ (n + 1) ∣ inv4 (X * rest a b x) - inv4 (X * rest a b y) := by
  have he : X ^ n ∣ euler x - euler y := by
    rw [X_pow_dvd_iff] at h ⊢
    intro m hm
    have := h m hm
    rw [map_sub, sub_eq_zero] at this
    rw [map_sub, coeff_euler, coeff_euler, this, sub_self]
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := he
  have hr : X ^ (n + 1) ∣ X * rest a b x - X * rest a b y := by
    refine ⟨(v - u) * (euler x - x + (euler y - y)) - 12 * u * (x + y)
      - 4 * X * u * (x ^ 2 + x * y + y ^ 2) + C a * X ^ 3 * u, ?_⟩
    unfold rest
    linear_combination X * (euler x - x + (euler y - y)) * hv +
      X * (-(euler x - x + (euler y - y)) - 12 * (x + y)
        - 4 * X * (x ^ 2 + x * y + y ^ 2) + C a * X ^ 3) * hu
  rw [X_pow_dvd_iff] at hr ⊢
  intro m hm
  have := hr m hm
  rw [map_sub, sub_eq_zero] at this
  rw [map_sub, inv4, inv4, coeff_mk, coeff_mk, this, sub_self]

theorem isWpSer_iff [CharZero K] (a b : K) (R : PowerSeries K) :
    IsWpSer a b (1 + X * R) ↔ inv4 (X * rest a b R) = R := by
  rw [inverseShiftedEulerOperatorFour_eq_iff]
  have he := euler_one_add R
  have hX : (X : PowerSeries K) ≠ 0 := X_ne_zero
  unfold IsWpSer
  change _ ∧ (euler (1 + X * R) - _) ^ 2 = _ ↔ _
  rw [he]
  unfold rest
  constructor
  · rintro ⟨-, h⟩
    apply mul_left_cancel₀ hX
    linear_combination h
  · intro h
    refine ⟨by simp, ?_⟩
    linear_combination X * h

theorem eq_one_add {P : PowerSeries K} (h : constantCoeff P = 1) : ∃ R, P = 1 + X * R := by
  obtain ⟨R, hR⟩ : X ∣ P - 1 := by rw [X_dvd_iff]; simp [h]
  exact ⟨R, by linear_combination hR⟩

theorem existsUnique_isWpSer :
    ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  intro K _ _ a b
  obtain ⟨R, hR⟩ := GlobalTheory.GenusOneDatum.exists_fixed_of_contract
    (fun R : PowerSeries K => inv4 (X * rest a b R)) (contract a b)
  refine ⟨1 + X * R, (isWpSer_iff a b R).2 hR, fun P hP => ?_⟩
  obtain ⟨S, rfl⟩ := eq_one_add hP.1
  have hS := (isWpSer_iff a b S).1 hP
  have hd : ∀ n : ℕ, X ^ n ∣ S - R := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := contract a b n S R ih
      rwa [hS, show inv4 (X * rest a b R) = R from hR] at this
  have : S = R := by
    ext n
    have := X_pow_dvd_iff.1 (hd (n + 1)) n (by omega)
    rwa [map_sub, sub_eq_zero] at this
  rw [this]

end GlobalTheory.WpSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPSeriesAndSigmaStarQuotientSeri
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

noncomputable section

namespace GlobalTheory.WpSeries

abbrev tay (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (coef1 f)

variable {f g : ℂ → ℂ}

lemma tay_congr (h : f =ᶠ[𝓝 0] g) : tay f = tay g := by
  ext n
  simp only [PowerSeries.coeff_mk, coef1, h.iteratedDeriv_eq n]

lemma tay_congr' (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (h : f =ᶠ[𝓝[≠] 0] g) :
    tay f = tay g :=
  tay_congr ((hf.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg.continuousAt).1 h)

lemma tay_add (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z + g z) = tay f + tay g := by
  ext n
  simp only [map_add, PowerSeries.coeff_mk, coef1, ← add_div]
  congr 1
  exact iteratedDeriv_add hf.contDiffAt hg.contDiffAt

lemma tay_sub (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z - g z) = tay f - tay g := by
  ext n
  simp only [map_sub, PowerSeries.coeff_mk, coef1, ← sub_div]
  congr 1
  exact iteratedDeriv_sub hf.contDiffAt hg.contDiffAt

lemma tay_mul (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z * g z) = tay f * tay g := by
  ext n
  have h : iteratedDeriv n (fun z => f z * g z) 0 = _ :=
    iteratedDeriv_mul (n := n) hf.contDiffAt hg.contDiffAt
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coef1, h]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e : ((n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ)) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (n - i).factorial_ne_zero
  have h3 : (n.choose i : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hi').ne'
  rw [← e]
  field_simp

lemma constantCoeff_tay (f : ℂ → ℂ) : PowerSeries.constantCoeff (tay f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  simp [coef1]

lemma tay_const (c : ℂ) : tay (fun _ => c) = PowerSeries.C c := by
  ext n
  rcases n with _ | n
  · simp [coef1]
  · simp [coef1, iteratedDeriv_const]

lemma tay_deriv (f : ℂ → ℂ) : tay (deriv f) = PowerSeries.derivativeFun (tay f) := by
  ext n
  refine Eq.trans ?_ (PowerSeries.coeff_derivativeFun (tay f) n).symm
  simp only [PowerSeries.coeff_mk, coef1, iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

lemma tay_id : tay (fun z => z) = PowerSeries.X := by
  ext n
  rcases n with _ | _ | n
  · simp [coef1]
  · simp [coef1]
  · simp [coef1, iteratedDeriv_succ', iteratedDeriv_const, PowerSeries.coeff_X]

lemma tay_pow (hf : AnalyticAt ℂ f 0) (n : ℕ) : tay (fun z => f z ^ n) = tay f ^ n := by
  induction n with
  | zero => simp [tay_const]
  | succ n ih =>
    simp only [pow_succ]
    rw [tay_mul (hf.fun_pow n) hf, ih]

def sqWp (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z

lemma analyticAt_sqWp (L : PeriodPair) : AnalyticAt ℂ (sqWp L) 0 := by
  have := L.analyticAt_weierstrassPExcept 0
  unfold sqWp
  fun_prop

lemma sqWp_eq (L : PeriodPair) {z : ℂ} (hz : z ≠ 0) : sqWp L z = z ^ 2 * L.weierstrassP z := by
  rw [← L.weierstrassPExcept_add 0, sqWp]
  simp
  field_simp
  ring

lemma eventually_notMem (L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  have h := L.compl_lattice_diff_singleton_mem_nhds 0
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z h1 h2 h3
  exact h1 ⟨h3, h2⟩

lemma deriv_sqWp (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (sqWp L) z = 2 * z * L.weierstrassP z + z ^ 2 * L.derivWeierstrassP z := by
  have h0 : z ≠ 0 := by rintro rfl; exact hz (zero_mem _)
  have h1 : sqWp L =ᶠ[𝓝 z] fun w => w ^ 2 * L.weierstrassP w := by
    filter_upwards [isOpen_ne.mem_nhds h0] with w hw using sqWp_eq L hw
  have h2 : DifferentiableAt ℂ L.weierstrassP z :=
    L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
  rw [h1.deriv_eq, deriv_fun_mul (by fun_prop) h2, L.deriv_weierstrassP]
  simp

lemma isWpSer_sqWp (L : PeriodPair) : IsWpSer L.g₂ L.g₃ (tay (sqWp L)) := by
  have hp := analyticAt_sqWp L
  have hd := hp.deriv
  have hi : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  refine ⟨by rw [constantCoeff_tay]; simp [sqWp], ?_⟩
  have key := tay_congr' (f := fun z => (z * deriv (sqWp L) z - 2 * sqWp L z) ^ 2)
    (g := fun z => 4 * sqWp L z ^ 3 - L.g₂ * z ^ 4 * sqWp L z - L.g₃ * z ^ 6)
    (by fun_prop) (by fun_prop) (by
      filter_upwards [eventually_notMem L, self_mem_nhdsWithin] with z h1 h2
      rw [deriv_sqWp L h1, sqWp_eq L h2]
      linear_combination z ^ 6 * L.derivWeierstrassP_sq z h1)
  rw [tay_pow (by fun_prop), tay_sub (by fun_prop) (by fun_prop),
    tay_sub (by fun_prop) (by fun_prop), tay_sub (by fun_prop) (by fun_prop),
    tay_mul hi hd, tay_mul analyticAt_const hp, tay_mul analyticAt_const (hp.fun_pow 3),
    tay_mul (by fun_prop) hp, tay_mul analyticAt_const (hi.fun_pow 4),
    tay_mul analyticAt_const (hi.fun_pow 6), tay_pow hp, tay_pow hi, tay_pow hi, tay_id,
    tay_deriv, tay_const, tay_const, tay_const, tay_const, map_ofNat, map_ofNat] at key
  exact key

theorem exists_wpSer : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∃ P : PowerSeries ℂ, IsWpSer (g2 Λ) (g3 Λ) P ∧ ∀ v, v ∉ Λ → PowerSeries.X ^ 2 * PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.mk (coef1 (sgStar Λ)) ^ 2 * lineSer P (wpF Λ v) := by
  intro Λ h
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  refine ⟨tay (sqWp L), ?_, fun v hv => ?_⟩
  · rw [GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL]
    exact isWpSer_sqWp L
  have hp := analyticAt_sqWp L
  have hi : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hs : AnalyticAt ℂ (sgStar Λ) 0 := h.differentiable.analyticAt 0
  have ht : AnalyticAt ℂ (sqTh Λ v) 0 := (h.differentiable_sqTh v).analyticAt 0
  have key := tay_congr' (f := fun z => z ^ 2 * sqTh Λ v z)
    (g := fun z => sgStar Λ z ^ 2 * (sqWp L z - wpF Λ v * z ^ 2))
    (by fun_prop) (by fun_prop) (by
      filter_upwards [eventually_notMem L, self_mem_nhdsWithin] with z h1 h2
      rw [h.sqTh_eq hv ((hL z).not.2 h1), sqWp_eq L h2, GlobalTheory.LatticeInvariants.wpF_eq hL z]
      ring)
  rw [tay_mul (hi.fun_pow 2) ht, tay_mul (hs.fun_pow 2) (by fun_prop), tay_sub hp (by fun_prop),
    tay_mul analyticAt_const (hi.fun_pow 2), tay_pow hi, tay_pow hs, tay_id, tay_const] at key
  exact key

end GlobalTheory.WpSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWpFEq
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem exists_wpF_eq : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ r : ℂ, ∃ Q, Q ∉ Λ ∧ wpF Λ Q = r := by
  intro Λ h r
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨z, hz, e⟩ := GlobalTheory.exists_weierstrassP_eq L r
  exact ⟨z, (hL z).not.2 hz, (GlobalTheory.OddTheta.wpF_eq L Λ hL z).trans e⟩

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galStar_complexMultiplication_points : ∀ D : D7, galStar D := by
  first | exact @GlobalTheory.ConjPoint.galStar_holds | exact GlobalTheory.ConjPoint.galStar_holds | (intros; apply GlobalTheory.ConjPoint.galStar_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisTaylorSeriesCanonicalOddThetaAllStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_taylorSeries_canonicalOddTheta_all : ∀ D : D7, galSg D := by
  first | exact @GlobalTheory.SigmaConj.galSg_all | exact GlobalTheory.SigmaConj.galSg_all | (intros; apply GlobalTheory.SigmaConj.galSg_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateIStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPeriodTheta_differentiable_and_signedTranslate_invariant : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z := by
  first | exact @GlobalTheory.HalfPeriodTheta.theta_signed_translation | exact GlobalTheory.HalfPeriodTheta.theta_signed_translation | (intros; apply GlobalTheory.HalfPeriodTheta.theta_signed_translation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructureStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_frame_var : ∀ (D : D7) (N N' : ℕ), ∃ (m r : ℕ) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b := by
  first | exact @GlobalTheory.FourCopies.exists_onB_four | exact GlobalTheory.FourCopies.exists_onB_four | (intros; apply GlobalTheory.FourCopies.exists_onB_four <;> assumption)
end

