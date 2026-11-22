import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceFinExt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesTransport
section
noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Matrix

section Cz

variable {L : Type} [Field L]

theorem cz_neg (f : PowerSeries L) {k : ℤ} (hk : k < 0) : cz f k = 0 := by
  simp [cz, not_le.mpr hk]

theorem cz_nat (f : PowerSeries L) (k : ℕ) : cz f (k : ℤ) = PowerSeries.coeff k f := by
  simp [cz]

theorem cz_add (f g : PowerSeries L) (k : ℤ) : cz (f + g) k = cz f k + cz g k := by
  unfold cz; split_ifs <;> simp

theorem cz_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries L) (k : ℤ) :
    cz (∑ i ∈ s, f i) k = ∑ i ∈ s, cz (f i) k := by
  unfold cz; split_ifs <;> simp

theorem cz_C_mul (c : L) (f : PowerSeries L) (k : ℤ) : cz (PowerSeries.C c * f) k = c * cz f k := by
  unfold cz; split_ifs <;> simp

theorem cz_rescale (c : L) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.rescale c f) k = c ^ k * cz f k := by
  rcases lt_or_ge k 0 with h | h
  · simp [cz_neg _ h]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [cz_nat, PowerSeries.coeff_rescale]

theorem cz_X_pow_mul (w : ℕ) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.X ^ w * f) (k + (w : ℤ)) = cz f k := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    rcases lt_or_ge (k + (w : ℤ)) 0 with h' | h'
    · exact cz_neg _ h'
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h'
      rw [hm, cz_nat, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [← Nat.cast_add, cz_nat, cz_nat, PowerSeries.coeff_X_pow_mul]

theorem cz_mul (g f : PowerSeries L) (k : ℤ) (N : ℕ) (hN : k < (N : ℤ)) :
    cz (g * f) k = ∑ i ∈ Finset.range N, PowerSeries.coeff i g * cz f (k - (i : ℤ)) := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [cz_neg _ (by omega), mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [cz_nat, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show m + 1 ≤ N by omega))]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
      rw [← Nat.cast_sub this, cz_nat]
    · intro i _ hi
      have : m < i := by simpa using hi
      rw [cz_neg _ (by omega), mul_zero]

theorem series_transport {M M' : Type} [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
    {r r' : ℕ} (w w' : ℕ) (A : Fin r' → PowerSeries L) (Bs : Fin r → PowerSeries L) (κ : L) (hκ : κ ≠ 0)
    (g : PowerSeries L) (c : Fin r' → Fin r → L)
    (hA : ∀ j, (PowerSeries.C κ * PowerSeries.X) ^ w * A j =
      PowerSeries.X ^ w' * (g * ∑ p, PowerSeries.C (c j p) * PowerSeries.rescale κ (Bs p)))
    (h : M →ₗ[L] M') (D : Fin r → M) (D' : Fin r' → M') (hD : ∀ p, h (D p) = ∑ j, c j p • D' j) (k : ℤ) :
    ∑ j, cz (A j) (k + (w' : ℤ)) • D' j = ∑ᶠ i : ℕ, PowerSeries.coeff i g •
      (κ ^ (k - (i : ℤ)) • h (∑ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) • D p)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k + (w : ℤ) < (N : ℤ) := ⟨(k + (w : ℤ)).toNat + 1, by omega⟩
  rw [finsum_eq_sum_of_support_subset (s := Finset.range N)]
  · have key : ∀ j, cz (A j) (k + (w' : ℤ)) = ∑ i ∈ Finset.range N, ∑ p, PowerSeries.coeff i g *
        (κ ^ (k - (i : ℤ)) * (cz (Bs p) (k - (i : ℤ) + (w : ℤ)) * c j p)) := by
      intro j
      have h1 := congrArg (fun f => cz f (k + (w : ℤ) + (w' : ℤ))) (hA j)
      rw [cz_X_pow_mul, mul_pow, ← map_pow, mul_assoc, cz_C_mul, add_right_comm, cz_X_pow_mul,
        cz_mul _ _ _ N hN] at h1
      apply mul_left_cancel₀ (pow_ne_zero w hκ)
      rw [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cz_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [cz_C_mul, cz_rescale, show k + (w : ℤ) - (i : ℤ) = k - (i : ℤ) + (w : ℤ) by ring, zpow_add₀ hκ,
        zpow_natCast]
      ring
    simp only [key, Finset.sum_smul, map_sum, map_smul, hD, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  · intro i hi
    by_contra hc
    apply hi
    have : N ≤ i := by simpa using hc
    have hz : ∀ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) = 0 := fun p => cz_neg _ (by omega)
    simp [hz]

end Cz

theorem basis_transport {C S : Type} [CommRing C] [CommRing S] (J : C →+* S) (σ : C →+* C) (σS : S →+* S)
    (hJ : ∀ a, J (σ a) = σS (J a)) {M M' : Type} [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
    (h : M →+ M') (hh : ∀ (a : S) m, h (a • m) = σS a • h m) (t q : C) (ht : IsUnit (J t)) (hq : IsUnit (J q))
    {r r' : ℕ} (w w' : ℕ) (bn d : Fin r → M) (bn' d' : Fin r' → M') (U : Fin r → Fin r → C)
    (U' : Fin r' → Fin r' → C) (H Cm : Fin r' → Fin r → C)
    (hd : ∀ j, J t ^ w • d j = ∑ i, J (U i j) • bn i) (hd' : ∀ j, J t ^ w' • d' j = ∑ i, J (U' i j) • bn' i)
    (hH : ∀ j, J q • h (bn j) = ∑ i, J (H i j) • bn' i)
    (hU : ∀ k p, t ^ w' * ∑ i, H k i * σ (U i p) = σ t ^ w * q * ∑ j, U' k j * Cm j p) (p : Fin r) :
    h (d p) = ∑ j, J (Cm j p) • d' j := by
  have hu : IsUnit (J t ^ w' * σS (J t) ^ w * J q) := ((ht.pow _).mul ((ht.map σS).pow _)).mul hq
  apply hu.smul_left_cancel.mp
  have e1 : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) =
      ∑ k, J (t ^ w' * ∑ i, H k i * σ (U i p)) • bn' k := by
    have : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) = J t ^ w' • J q • h (J t ^ w • d p) := by
      rw [hh, map_pow, smul_smul, smul_smul]
      congr 1
      ring
    rw [this, hd, map_sum, Finset.smul_sum, Finset.smul_sum]
    simp only [hh, smul_comm (J q), hH, Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
      Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have e2 : (J t ^ w' * σS (J t) ^ w * J q) • ∑ j, J (Cm j p) • d' j =
      ∑ k, J (σ t ^ w * q * ∑ j, U' k j * Cm j p) • bn' k := by
    have : ∀ j, (J t ^ w' * σS (J t) ^ w * J q) • J (Cm j p) • d' j =
        (σS (J t) ^ w * J q * J (Cm j p)) • J t ^ w' • d' j := by
      intro j
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [Finset.smul_sum]
    simp only [this, hd', Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
      Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  rw [e1, e2]
  simp only [hU]

theorem coord_transport {A : Type} [CommRing A] (σ : A →+* A) {r r' : ℕ} (U V : Matrix (Fin r) (Fin r) A)
    (U' V' : Matrix (Fin r') (Fin r') A) (H Cm : Matrix (Fin r') (Fin r) A) (q q' : A)
    (hq : ∀ a, q * a = 0 → a = 0) (hUV : U * V = 1) (hUV' : U' * V' = 1)
    (hU : H * U.map σ = q • (U' * Cm)) (c : Fin r → A) (c' : Fin r' → A)
    (hc : q • c' = q' • H *ᵥ (σ ∘ c)) : V' *ᵥ c' = q' • Cm *ᵥ (σ ∘ (V *ᵥ c)) := by
  have h1 : V' * H = q • (Cm * V.map σ) := by
    have h2 : U.map σ * V.map σ = 1 := by
      rw [← Matrix.map_mul, hUV, Matrix.map_one _ (map_zero σ) (map_one σ)]
    calc V' * H = V' * (H * U.map σ) * V.map σ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = q • (Cm * V.map σ) := by
          rw [hU, Matrix.mul_smul, ← Matrix.mul_assoc, mul_eq_one_comm.mp hUV', Matrix.one_mul, Matrix.smul_mul]
  have h3 : σ ∘ (V *ᵥ c) = V.map σ *ᵥ (σ ∘ c) := by
    funext i
    exact RingHom.map_mulVec σ V c i
  have h4 : q • (V' *ᵥ c') = q • (q' • Cm *ᵥ (σ ∘ (V *ᵥ c))) := by
    rw [← Matrix.mulVec_smul, hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1, h3, Matrix.mulVec_mulVec,
      Matrix.smul_mulVec, smul_comm]
  funext i
  have h5 := congrFun h4 i
  simp only [Pi.smul_apply, smul_eq_mul] at h5 ⊢
  exact sub_eq_zero.mp (hq _ (by rw [mul_sub, h5, sub_self]))

end GlobalTheory.HWL.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNorm
section
noncomputable section

namespace GlobalTheory.HWL.BanachEval

open PowerSeries Filter Finset GlobalTheory.HWL.Disc

variable {K : Type} [NormedField K] {N : Type} [NormedCommRing N]

def Small (ν : N) : Prop := ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖ν ^ k‖ ≤ C * r ^ k

def Bdd (c : K →+* N) : Prop := ∃ C : ℝ, ∀ x, ‖c x‖ ≤ C * ‖x‖

def ev (c : K →+* N) (ν : N) (a : K⟦X⟧) : N := ∑' k : ℕ, c (coeff k a) * ν ^ k

variable {c : K →+* N} {ν : N}

theorem Bdd.continuous (hc : Bdd c) : Continuous c := by
  obtain ⟨C, h⟩ := hc
  exact AddMonoidHomClass.continuous_of_bound c C h

theorem exists_bound (hc : Bdd c) (hν : Small ν) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ (x : K) (k : ℕ), ‖c x * ν ^ k‖ ≤ C * (‖x‖ * r ^ k) := by
  obtain ⟨C, h⟩ := hc
  obtain ⟨D, r, h0, h1, h2⟩ := hν
  refine ⟨|C| * |D|, r, by positivity, h0, h1, fun x k => (norm_mul_le _ _).trans ?_⟩
  have e1 : ‖c x‖ ≤ |C| * ‖x‖ := (h x).trans (by gcongr; exact le_abs_self C)
  have e2 : ‖ν ^ k‖ ≤ |D| * r ^ k := (h2 k).trans (by gcongr; exact le_abs_self D)
  calc _ ≤ (|C| * ‖x‖) * (|D| * r ^ k) := by gcongr
    _ = _ := by ring

theorem summable_norm (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    Summable fun k : ℕ => ‖c (coeff k a) * ν ^ k‖ := by
  obtain ⟨C, r, -, h0, h1, h⟩ := exists_bound hc hν
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => h _ k) ((ha r h0 h1).mul_left C)

theorem Small.tendsto (hν : Small ν) : Tendsto (fun k : ℕ => ν ^ k) atTop (nhds 0) := by
  obtain ⟨D, r, h0, h1, h2⟩ := hν
  refine squeeze_zero_norm h2 ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul D

theorem ev_C_mul (hc : Bdd c) (hν : Small ν) [CompleteSpace N] (x : K) {a : K⟦X⟧} (ha : SC a) :
    ev c ν (x • a) = c x * ev c ν a := by
  rw [ev, ev, ← (summable_norm hc hν ha).of_norm.tsum_mul_left]
  simp [mul_assoc]

theorem sum_range_eq (a : K⟦X⟧) (m : ℕ) :
    ∑ k ∈ range m, c (coeff k a) * ν ^ k = Polynomial.eval₂ c ν (trunc m a) := by
  rw [eval₂_trunc_eq_sum_range]

variable [CompleteSpace N]

theorem hasSum_ev (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    HasSum (fun k : ℕ => c (coeff k a) * ν ^ k) (ev c ν a) :=
  (summable_norm hc hν ha).of_norm.hasSum

theorem tendsto_ev (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    Tendsto (fun m : ℕ => Polynomial.eval₂ c ν (trunc m a)) atTop (nhds (ev c ν a)) := by
  simpa only [sum_range_eq] using (hasSum_ev hc hν ha).tendsto_sum_nat

theorem ev_add (hc : Bdd c) (hν : Small ν) {a b : K⟦X⟧} (ha : SC a) (hb : SC b) :
    ev c ν (a + b) = ev c ν a + ev c ν b := by
  refine HasSum.tsum_eq ?_
  simpa only [map_add, add_mul] using (hasSum_ev hc hν ha).add (hasSum_ev hc hν hb)

theorem ev_mul (hc : Bdd c) (hν : Small ν) {a b : K⟦X⟧} (ha : SC a) (hb : SC b) :
    ev c ν (a * b) = ev c ν a * ev c ν b := by
  rw [ev, ev, ev, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm hc hν ha)
    (summable_norm hc hν hb)]
  refine tsum_congr fun k => ?_
  rw [coeff_mul, map_sum, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [← mem_antidiagonal.1 hp, map_mul, pow_add]
  ring

theorem ev_one : ev c ν 1 = 1 := by
  rw [ev, tsum_eq_single 0 fun k hk => by simp [coeff_one, hk]]
  simp

theorem sc_pow {a : K⟦X⟧} (ha : SC a) (k : ℕ) : SC (a ^ k) := by
  induction k with
  | zero => simpa using sc_coe (1 : Polynomial K)
  | succ k ih => rw [pow_succ]; exact ih.mul ha

theorem ev_pow (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) (k : ℕ) :
    ev c ν (a ^ k) = ev c ν a ^ k := by
  induction k with
  | zero => simpa using ev_one
  | succ k ih => rw [pow_succ, pow_succ, ev_mul hc hν (sc_pow ha k) ha, ih]

theorem hasSum_map (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) (f : N →+* N) (hf : Continuous f)
    (hfc : ∀ x, f (c x) = c x) : HasSum (fun k : ℕ => c (coeff k a) * f ν ^ k) (f (ev c ν a)) := by
  have := (hasSum_ev hc hν ha).map f hf
  simpa only [Function.comp_def, map_mul, map_pow, hfc] using this

theorem ev_map {O : Type} [CommRing O] (j : O →+* K) (hν : Small ν) (hc : Bdd c) (f : O⟦X⟧ →+* N)
    (hC : ∀ o, f (C o) = c (j o)) (hX : f X = ν) (hf : ∀ a, ‖f a‖ ≤ 1) (a : O⟦X⟧) (ha : SC (map j a)) :
    ev c ν (map j a) = f a := by
  refine tendsto_nhds_unique (hasSum_ev hc hν ha).tendsto_sum_nat ?_
  have key : ∀ m : ℕ, ∑ k ∈ range m, c (coeff k (map j a)) * ν ^ k =
      f a - ν ^ m * f (mk fun i => coeff (i + m) a) := by
    intro m
    have e0 := congrArg f (eq_X_pow_mul_shift_add_trunc m a)
    rw [e0, map_add, map_mul, map_pow, hX, add_sub_cancel_left, trunc_apply, Polynomial.coe_def]
    have e : (mk (∑ k ∈ Ico 0 m, Polynomial.monomial k (coeff k a)).coeff : O⟦X⟧) =
        ∑ k ∈ range m, C (coeff k a) * X ^ k := by
      ext n
      simp [coeff_X_pow, Polynomial.coeff_monomial, Polynomial.finset_sum_coeff]
    rw [e, map_sum]
    simp only [map_mul, map_pow, hX, hC, coeff_map]
  simp only [key]
  conv => rhs; rw [← sub_zero (f a)]
  refine tendsto_const_nhds.sub (squeeze_zero_norm (a := fun m => ‖ν ^ m‖) (fun m => ?_) ?_)
  · exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hf _))
  · simpa using hν.tendsto.norm

theorem hasSum_subst [IsUltrametricDist K] (hc : Bdd c) (hν : Small ν) {y a : K⟦X⟧} (hy0 : constantCoeff y = 0)
    (hy : ∀ k, ‖coeff k y‖ ≤ 1) (ha : SC a) :
    HasSum (fun k : ℕ => c (coeff k a) * ev c ν y ^ k) (ev c ν (subst y a)) := by
  obtain ⟨C, r, hC, h0, h1, h⟩ := exists_bound hc hν
  have hy' : SC y := sc_of_le 0 fun k => by simpa using hy k
  have hp : ∀ k n, ‖coeff n (y ^ k)‖ ≤ 1 := fun k n => by
    simpa using norm_coeff_pow_le y n (r := 1) (R := 1) zero_le_one zero_le_one (fun i _ => by simpa using hy i) k n le_rfl
  have hz : ∀ k n, n < k → coeff n (y ^ k) = 0 := fun k n hn =>
    X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hy0) k) n hn
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ r = ρ * ρ :=
    ⟨√r, Real.sqrt_pos.2 h0, by rwa [Real.sqrt_lt' one_pos, one_pow], (Real.mul_self_sqrt h0.le).symm⟩
  let F : ℕ × ℕ → N := fun p => c (coeff p.1 a * coeff p.2 (y ^ p.1)) * ν ^ p.2
  have hF : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => (C * (‖coeff p.1 a‖ * ρ ^ p.1)) * ρ ^ p.2)
      (Summable.mul_of_nonneg ((ha ρ hρ0 hρ1).mul_left C) (summable_geometric_of_lt_one hρ0.le hρ1)
        (fun _ => by positivity) fun _ => by positivity) fun p => ?_
    by_cases hlt : p.2 < p.1
    · simp only [F, hz _ _ hlt, mul_zero, map_zero, zero_mul, norm_zero]
      positivity
    · refine (h _ _).trans ?_
      have e : ρ ^ p.2 ≤ ρ ^ p.1 := pow_le_pow_of_le_one hρ0.le hρ1.le (not_lt.1 hlt)
      rw [norm_mul, hρ, mul_pow]
      calc _ ≤ C * (‖coeff p.1 a‖ * 1 * (ρ ^ p.1 * ρ ^ p.2)) := by gcongr; exact hp _ _
        _ = _ := by ring
  have h2 : HasSum (fun n : ℕ => c (coeff n (subst y a)) * ν ^ n) (∑' p, F p) := by
    refine HasSum.prod_fiberwise ((Equiv.prodComm ℕ ℕ).hasSum_iff.2 hF.hasSum) fun n => ?_
    have e : coeff n (subst y a) = ∑ k ∈ range (n + 1), coeff k a * coeff n (y ^ k) := by
      rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hy0), finsum_eq_sum_of_support_subset (s := range (n + 1))]
      · simp
      · intro k hk
        by_contra hk'
        apply hk
        simp only [coe_range, Set.mem_Iio, not_lt] at hk'
        simp [hz k n hk']
    rw [e, map_sum, sum_mul]
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    simp [F, hz k n hk]
  rw [show ev c ν (subst y a) = _ from h2.tsum_eq]
  refine HasSum.prod_fiberwise hF.hasSum fun k => ?_
  rw [← ev_pow hc hν hy']
  simpa only [F, map_mul, mul_assoc] using (hasSum_ev hc hν (sc_pow hy' k)).mul_left (c (coeff k a))

end GlobalTheory.HWL.BanachEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentCharactersEqAndFrobeniusStable
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

end Descent

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma actD_apply_shift_eq_zero_of_apply_eq_zero {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (g : _root_.GlobalTheory.BK.TameGal K l e a) {x : P.D} {σ : ZMod a}
    (hx : x σ = 0) : Δ.actD g x (σ + g.shift) = 0 := by
  classical
  set f : ZMod a → K⟦X⟧ := fun ρ => if ρ = σ then 0 else 1 with hf
  have hfx : f • _root_.GlobalTheory.BK.cst x = _root_.GlobalTheory.BK.cst x := by
    apply funext; intro ρ; apply funext; intro i
    show f ρ * PowerSeries.C (x ρ i) = PowerSeries.C (x ρ i)
    by_cases h : ρ = σ
    · simp [h, hx]
    · simp [hf, h]
  have key : Δ.actD g x = _root_.GlobalTheory.BK.red (Δ.act g (_root_.GlobalTheory.BK.cst x)) := rfl
  rw [key, ← hfx, _root_.GlobalTheory.BK.Descent.act_smul_tot]
  funext i
  show constantCoeff ((_root_.GlobalTheory.BK.ringAct g f (σ + g.shift)) *
    (Δ.act g (_root_.GlobalTheory.BK.cst x)) (σ + g.shift) i) = 0
  rw [_root_.GlobalTheory.BK.ringAct_apply]
  simp [hf]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma actD_apply_shift_eq_of_apply_eq {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (g : _root_.GlobalTheory.BK.TameGal K l e a) {x y : P.D} {σ : ZMod a}
    (h : x σ = y σ) : Δ.actD g x (σ + g.shift) = Δ.actD g y (σ + g.shift) := by
  have hxy := actD_apply_shift_eq_zero_of_apply_eq_zero Δ g (x := x - y) (σ := σ) (by simp [h])
  rwa [map_sub, Pi.sub_apply, sub_eq_zero] at hxy

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma tameGal_inertia_root_pow (ζ : rootsOfUnity e K) (n : ℕ) (τ : ZMod a) :
    (_root_.GlobalTheory.BK.TameGal.inertia (l := l) (ζ ^ n)).root τ =
      (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, map_one, pow_zero]
    exact _root_.GlobalTheory.BK.TameGal.root_one τ
  | succ n ih =>
    rw [pow_succ, map_mul, _root_.GlobalTheory.BK.TameGal.root_mul,
      _root_.GlobalTheory.BK.TameGal.shift_inertia, sub_zero, ih, pow_succ]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma chars_succ_subset_chars {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (τ : ZMod a) :
    Δ.chars (τ + 1) ⊆ Δ.chars τ := by
  rintro c ⟨x, hx0, hx⟩
  set F : _root_.GlobalTheory.BK.TameGal K l e a := _root_.GlobalTheory.BK.TameGal.fr with hF
  have hFs : F.shift = 1 := _root_.GlobalTheory.BK.TameGal.shift_fr
  have hFis : (F⁻¹).shift = -1 := by
    have hs := _root_.GlobalTheory.BK.TameGal.shift_mul F⁻¹ F
    rw [inv_mul_cancel, _root_.GlobalTheory.BK.TameGal.shift_one, hFs] at hs
    linear_combination -hs
  refine ⟨Δ.actD F⁻¹ x, fun h => hx0 ?_, fun ζ => ?_⟩
  · have hb := actD_apply_shift_eq_of_apply_eq Δ F (x := Δ.actD F⁻¹ x) (y := 0) (σ := τ)
      (by rw [h]; rfl)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
      map_zero, hFs] at hb
  · have hcomm : _root_.GlobalTheory.BK.TameGal.inertia ζ * F⁻¹ =
        F⁻¹ * _root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hF,
        _root_.GlobalTheory.BK.TameGal.fr_mul_inertia, mul_assoc, mul_inv_cancel, mul_one]
    have hroot : (_root_.GlobalTheory.BK.TameGal.inertia (l := l) (ζ ^ l)).root (τ + 1) ^ c.val =
        (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val := by
      rw [tameGal_inertia_root_pow, ← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]
    have hb := actD_apply_shift_eq_of_apply_eq Δ F⁻¹ (σ := τ + 1)
      (x := Δ.actD (_root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l)) x)
      (y := (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val • x)
      (by rw [hx, hroot]; rfl)
    rw [hFis, add_neg_cancel_right, map_smul] at hb
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hb,
      Pi.smul_apply]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma prime_mul_mem_chars_succ_of_mem [NeZero e] {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) {τ : ZMod a} {c : ZMod e}
    (hc : c ∈ Δ.chars τ) :
    (l : ZMod e) * c ∈ Δ.chars (τ + 1) := by
  obtain ⟨d, hd0, hd⟩ := hc
  refine ⟨P.phiD d, fun h => hd0 ?_, fun ζ => ?_⟩
  · have heq : P.phiD (Function.update (0 : P.D) τ (d τ)) = P.phiD 0 := by
      funext σ
      rw [_root_.GlobalTheory.BK.PhiMod.phiD_apply, map_zero]
      by_cases hσ : σ - 1 = τ
      · obtain rfl := eq_add_of_sub_eq hσ
        rw [add_sub_cancel_right, Function.update_self, Pi.zero_apply]
        rw [_root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right] at h
        exact h
      · simp [Function.update_of_ne hσ]
    simpa using congrFun (P.phiD.injective heq) τ
  · rw [_root_.GlobalTheory.BK.Descent.actD_phiD, _root_.GlobalTheory.BK.PhiMod.phiD_apply,
      _root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right, hd, mulVec_smul]
    congr 1
    have hr : (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ =
        (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root (τ + 1) ^ l := by
      rw [← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]
    have he := _root_.GlobalTheory.BK.TameGal.root_pow
      (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ) (τ + 1)
    rw [hr, ← pow_mul, pow_eq_pow_mod _ he, pow_eq_pow_mod ((l : ZMod e) * c).val he,
      ZMod.val_mul, ZMod.val_natCast, Nat.mod_mod, Nat.mod_mul_mod]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in

theorem _root_.GlobalTheory.BK.chars_eq_and_mul_mem (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K]
    [_root_.GlobalTheory.BK.IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a]
    (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) (Δ : _root_.GlobalTheory.BK.Descent P) :
    (∀ τ σ, Δ.chars τ = Δ.chars σ) ∧
      ∀ τ, ∀ c ∈ Δ.chars τ,
        (l : ZMod e) * c ∈ Δ.chars τ := by
  have hle : ∀ (τ : ZMod a) (n : ℕ),
      Δ.chars (τ + n) ⊆ Δ.chars τ := by
    intro τ n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [← add_assoc]
      exact (chars_succ_subset_chars Δ _).trans ih
  have hsub : ∀ τ σ : ZMod a,
      Δ.chars τ ⊆ Δ.chars σ := by
    intro τ σ
    have hs := hle σ (τ - σ).val
    rwa [ZMod.natCast_zmod_val, add_sub_cancel] at hs
  exact ⟨fun τ σ => (hsub τ σ).antisymm (hsub σ τ),
    fun τ c hc => hsub (τ + 1) τ (prime_mul_mem_chars_succ_of_mem Δ hc)⟩

end GlobalTheory.BK
end
end

