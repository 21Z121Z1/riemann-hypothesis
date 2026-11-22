import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0013
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0010
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0011
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0012
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0008
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronSer

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonA
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

private theorem norm_finsum_le_of_forall_norm_le_univ_sort {α : Type*} (f : α → K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ a, ‖f a‖ ≤ C) :
    ‖∑ᶠ a, f a‖ ≤ C := by
  classical
  rw [finsum_def]
  split_ifs with hs
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ => h i
  · simpa using hC

private theorem mvPowerSeries_norm_coeff_mul_le_mul {ι : Type} {F G : MvPowerSeries ι K} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ a) (hG : ∀ e, ‖MvPowerSeries.coeff e G‖ ≤ b) :
    ∀ e, ‖MvPowerSeries.coeff e (F * G)‖ ≤ a * b := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun p _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) ha

private theorem mvPowerSeries_norm_coeff_pow_le_pow {ι : Type} {F : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ c) :
    ∀ (m : ℕ) (e : ι →₀ ℕ), ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ c ^ m := by
  classical
  intro m
  induction m with
  | zero =>
    intro e
    rw [pow_zero, pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc m) hc ih hF

private theorem mvPowerSeries_norm_coeff_pow_le_one {ι : Type} {F : MvPowerSeries ι K}
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ 1) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ 1 := by
  simpa using mvPowerSeries_norm_coeff_pow_le_pow zero_le_one hF m e

private theorem mvPowerSeries_norm_coeff_pow_sub_pow_le {ι : Type} {A B : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ e, ‖MvPowerSeries.coeff e A‖ ≤ 1) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ m - B ^ m)‖ ≤ c := by
  classical
  have hs : ∀ e, ‖MvPowerSeries.coeff e (∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i))‖ ≤ 1 := by
    intro e
    rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one zero_le_one (mvPowerSeries_norm_coeff_pow_le_one hA i) (mvPowerSeries_norm_coeff_pow_le_one hB (m - 1 - i)) e
  rw [← geom_sum₂_mul]
  simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one hc hs hAB e

private theorem mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {A B : MvPowerSeries ι K}
    {c : ℝ} (hc : 0 ≤ c) (hcl : c ≤ ‖(l : K)‖) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ l - B ^ l)‖ ≤ c * ‖(l : K)‖ := by
  classical
  obtain ⟨D, rfl⟩ : ∃ D, A = D + B := ⟨A - B, by ring⟩
  simp only [add_sub_cancel_right] at hAB
  have hc1 : c ≤ 1 := hcl.trans hl1.le
  have hl2 : 2 ≤ l := hl.two_le
  rw [add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    add_sub_cancel_right]
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc (norm_nonneg _))
    fun i hi => ?_
  have hi' : i < l := Finset.mem_range.mp hi
  rw [← Nat.cast_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, norm_mul]
  have hterm : ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖ ≤ c ^ (i + 1) := by
    simpa using mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc _) zero_le_one (mvPowerSeries_norm_coeff_pow_le_pow hc hAB (i + 1)) (mvPowerSeries_norm_coeff_pow_le_one hB _) e
  have hch : ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) ≤ c * ‖(l : K)‖ := by
    obtain h | h : i + 1 < l ∨ i + 1 = l := by omega
    · obtain ⟨q, hq⟩ := hl.dvd_choose_self (Nat.succ_ne_zero i) h
      rw [hq, Nat.cast_mul, norm_mul]
      have hq1 : ‖(q : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K q
      have hpc : c ^ (i + 1) ≤ c := pow_le_of_le_one hc hc1 (Nat.succ_ne_zero i)
      calc ‖(l : K)‖ * ‖(q : K)‖ * c ^ (i + 1) ≤ ‖(l : K)‖ * 1 * c := by
            gcongr
        _ = c * ‖(l : K)‖ := by ring
    · rw [h, Nat.choose_self, Nat.cast_one, norm_one, one_mul]
      obtain ⟨j, rfl⟩ : ∃ j, l = j + 2 := ⟨l - 2, by omega⟩
      have hpc : c ^ (j + 1) ≤ c := pow_le_of_le_one hc hc1 (Nat.succ_ne_zero j)
      calc c ^ (j + 2) = c * c ^ (j + 1) := by ring
        _ ≤ c * ‖((j + 2 : ℕ) : K)‖ := by gcongr; exact hpc.trans hcl
  calc ‖((l.choose (i + 1) : ℕ) : K)‖ * ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖
      ≤ ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) := by gcongr
    _ ≤ c * ‖(l : K)‖ := hch

private theorem mvPowerSeries_norm_coeff_pow_prime_pow_sub_le {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {P Q : MvPowerSeries ι K}
    (hQ : ∀ e, ‖MvPowerSeries.coeff e Q‖ ≤ 1)
    (hPQ : ∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖) :
    ∀ (v : ℕ) (e : ι →₀ ℕ), ‖MvPowerSeries.coeff e (P ^ (l ^ v) - Q ^ (l ^ v))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
  intro v
  induction v with
  | zero => simpa using hPQ
  | succ v ih =>
    intro e
    rw [pow_succ, pow_mul, pow_mul, pow_succ _ (v + 1)]
    exact mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm hl hl1 (pow_nonneg (norm_nonneg _) _)
      (pow_le_of_le_one (norm_nonneg _) hl1.le (Nat.succ_ne_zero v)) (mvPowerSeries_norm_coeff_pow_le_one hQ _) ih e

private theorem norm_natCast_eq_one_of_not_prime_dvd (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {m : ℕ} (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime l m := (Nat.coprime_or_dvd_of_prime hl m).resolve_right hm
  have h1 := Nat.gcd_eq_gcd_ab l m
  rw [hcop.gcd_eq_one] at h1
  have h2 : (1 : K) = (l : K) * (Nat.gcdA l m : K) + (m : K) * (Nat.gcdB l m : K) := by
    have h3 := congrArg (fun x : ℤ => (x : K)) h1
    push_cast at h3
    exact h3
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) (not_lt.mp fun hlt => ?_)
  have h4 : ‖(1 : K)‖ < 1 := by
    rw [h2]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖(l : K)‖ * ‖((Nat.gcdA l m : ℤ) : K)‖ ≤ ‖(l : K)‖ * 1 := by
            gcongr
            exact IsUltrametricDist.norm_intCast_le_one K _
        _ < 1 := by simpa using hl1
    · rw [norm_mul]
      calc ‖(m : K)‖ * ‖((Nat.gcdB l m : ℤ) : K)‖ ≤ ‖(m : K)‖ * 1 := by
            gcongr
            exact IsUltrametricDist.norm_intCast_le_one K _
        _ < 1 := by simpa using hlt
  simp at h4

theorem qls {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative K z)) (P Q : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hQ0 : MvPowerSeries.constantCoeff Q = 0)
    (hP : IntegralMv P) (hQ : IntegralMv Q) (hPQ : DivByMv (l : K) (P - Q)) :
    DivByMv (l : K) (z.subst P - z.subst Q) := by
  classical
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  have hQs : PowerSeries.HasSubst Q := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  have hPi : ∀ e, ‖MvPowerSeries.coeff e P‖ ≤ 1 := by
    unfold IntegralMv at hP
    exact hP
  have hQi : ∀ e, ‖MvPowerSeries.coeff e Q‖ ≤ 1 := by
    unfold IntegralMv at hQ
    exact hQ
  have hPQi : ∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖ := by
    unfold DivByMv at hPQ
    exact hPQ
  have hzi : ∀ n, ‖PowerSeries.coeff n (derivative K z)‖ ≤ 1 := by
    unfold IntegralPS at hz
    exact hz
  have hpow := mvPowerSeries_norm_coeff_pow_prime_pow_sub_le hl hl1 hQi hPQi
  have hterm : ∀ (d : ℕ) (e : ι →₀ ℕ),
      ‖PowerSeries.coeff d z • MvPowerSeries.coeff e (P ^ d) -
        PowerSeries.coeff d z • MvPowerSeries.coeff e (Q ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d e
    rw [← smul_sub, ← map_sub, norm_smul]
    rcases d with _ | k
    · have h0 : PowerSeries.coeff 0 z = 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hz0
      rw [h0, norm_zero, zero_mul]
      exact norm_nonneg _
    · obtain ⟨v, m, hm, hkm0⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero k) l hl.ne_one
      have hkm : k + 1 = l ^ v * m := hkm0
      have hz' : ‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖ ≤ 1 := by
        have h1 := hzi k
        rw [PowerSeries.coeff_derivative] at h1
        simpa [norm_mul] using h1
      have hn : ‖((k + 1 : ℕ) : K)‖ = ‖(l : K)‖ ^ v := by
        rw [hkm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, norm_natCast_eq_one_of_not_prime_dvd hl hl1 hm, mul_one]
      have hPQn : ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
        rw [hkm, pow_mul, pow_mul]
        exact mvPowerSeries_norm_coeff_pow_sub_pow_le (pow_nonneg (norm_nonneg _) _) (mvPowerSeries_norm_coeff_pow_le_one hPi _) (mvPowerSeries_norm_coeff_pow_le_one hQi _) (hpow v) m e
      calc ‖PowerSeries.coeff (k + 1) z‖ * ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖
          ≤ ‖PowerSeries.coeff (k + 1) z‖ * ‖(l : K)‖ ^ (v + 1) := by gcongr
        _ = (‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖) * ‖(l : K)‖ := by
          rw [hn, pow_succ, mul_assoc]
        _ ≤ 1 * ‖(l : K)‖ := by gcongr
        _ = ‖(l : K)‖ := one_mul _
  unfold DivByMv
  intro e
  rw [map_sub, PowerSeries.coeff_subst hPs, PowerSeries.coeff_subst hQs,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hPs z e)
      (PowerSeries.coeff_subst_finite hQs z e)]
  exact norm_finsum_le_of_forall_norm_le_univ_sort _ (norm_nonneg _) fun d => hterm d e

theorem qls1 (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative K z)) (P Q : PowerSeries K)
    (hP0 : constantCoeff P = 0) (hQ0 : constantCoeff Q = 0)
    (hP : IntegralPS P) (hQ : IntegralPS Q) (hPQ : DivBy (l : K) (P - Q)) :
    DivBy (l : K) (z.subst P - z.subst Q) := by
  have key : ∀ (F : PowerSeries K) (d : Unit →₀ ℕ),
      MvPowerSeries.coeff d F = PowerSeries.coeff (d ()) F := by
    intro F d
    conv_lhs => rw [Finsupp.unique_single d]
    rfl
  have hP' : IntegralMv P := by
    unfold IntegralMv
    intro d
    rw [key]
    exact hP _
  have hQ' : IntegralMv Q := by
    unfold IntegralMv
    intro d
    rw [key]
    exact hQ _
  have hPQ' : DivByMv (l : K) (P - Q) := by
    unfold DivByMv
    intro d
    rw [key]
    exact hPQ _
  have h := qls hl hl1 z hz0 hz P Q hP0 hQ0 hP' hQ' hPQ'
  unfold DivBy
  intro k
  have hk := h (Finsupp.single () k)
  rwa [key, Finsupp.single_eq_same] at hk

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt
section
noncomputable section
open Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem norm_le_one_of_root {l : ℕ} [Fact l.Prime] {x : ℂ_[l]} (P : Polynomial ℤ) (hm : P.Monic)
    (h : P.eval₂ (Int.castRingHom ℂ_[l]) x = 0) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  have hsum := hm.as_sum
  rw [hsum] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
  have hx1 : (1 : ℝ) ≤ ‖x‖ := hlt.le
  have hn0 : P.natDegree ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have hbound : ‖∑ i ∈ Finset.range P.natDegree, (Int.castRingHom ℂ_[l]) (P.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (P.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    have hc : ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ ≤ 1 := by
      rw [eq_intCast (Int.castRingHom ℂ_[l])]
      exact IsUltrametricDist.norm_intCast_le_one _ _
    calc ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (P.natDegree - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hx1 (by omega)) (by positivity) zero_le_one
      _ = ‖x‖ ^ (P.natDegree - 1) := one_mul _
  have heq := eq_neg_of_add_eq_zero_left h
  have h1 : ‖x‖ ^ P.natDegree ≤ ‖x‖ ^ (P.natDegree - 1) := by
    rw [← norm_pow, heq, norm_neg]
    exact hbound
  have h2 : ‖x‖ ^ (P.natDegree - 1) < ‖x‖ ^ P.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith

theorem jInt : JInt := by
  intro d L hsf hd hL l _ ι
  obtain ⟨P, hm, hP⟩ := cm1 d L hsf hd hL
  refine norm_le_one_of_root P hm ?_
  have h := congrArg (ι : ℂ →+* ℂ_[l]) hP
  rw [Polynomial.hom_eval₂, map_zero] at h
  rw [← h]
  congr 1
  exact Subsingleton.elim _ _

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronPt
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def kronFun (p : ℕ) (τ : ℍ) : ℂ := Gm p τ + (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2

theorem kronSq_isMF (p : ℕ) :
    IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (fun τ => (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2) := by
  have h1 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ * DD τ ^ p) := isMF_AA.mul (isMF_DD.pow p)
  have h2 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ ^ p * DD τ) :=
    ((isMF_AA.pow p).mul isMF_DD).congr_weight (by ring)
  have h3 := (h1.sub h2).pow 2
  exact h3.congr_weight (by push_cast; ring)

theorem Gm_isMF' {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (Gm p) := (gmForm hp.pos).congr_weight (by rw [card_Tm_prime hp]; push_cast; ring)

theorem kronFun_isMF {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (kronFun p) := (Gm_isMF' hp).add (kronSq_isMF p)

theorem aC_conv : Conv aC := convergesOnDisk_eisensteinFourCubeSeries
theorem dC_conv : Conv dC := convergesOnDisk_discriminantSeries
theorem aC_ev (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  exact evalSeries_eisensteinFourCubeSeries τ
theorem dC_ev (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  exact evalSeries_discriminantSeries τ

theorem kronFun_qExp {p : ℕ} (hp : p.Prime) :
    qExpansion 1 (kronFun p) = qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2 := by
  have hq : ∀ τ : ℍ, ‖qm 1 τ‖ < 1 := fun τ => by
    rw [qm_one_eq]
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hG := Gm_isMF' hp
  have c1 : Conv (aC * dC ^ p) := aC_conv.mul (dC_conv.pow p)
  have c2 : Conv (aC ^ p * dC) := (aC_conv.pow p).mul dC_conv
  have c3 : Conv (aC * dC ^ p - aC ^ p * dC) := c1.sub c2
  apply (kronFun_isMF hp).qExp_eq (hG.conv.add (c3.pow 2))
  intro τ
  rw [ev_add hG.conv (c3.pow 2) (hq τ), hG.ev_eq τ, ev_pow c3 2 (hq τ), ev_sub c1 c2 (hq τ),
    ev_mul aC_conv (dC_conv.pow p) (hq τ), ev_pow dC_conv p (hq τ), ev_mul (aC_conv.pow p) dC_conv (hq τ),
    ev_pow aC_conv p (hq τ), aC_ev, dC_ev]
  rfl

theorem kronFun_div {p : ℕ} (hp : p.Prime) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧ qExpansion 1 (kronFun p) = PowerSeries.C (1 - zetaC p) * w := by
  obtain ⟨w, hw, hk⟩ := kronSer hp
  have hp0 : 0 < p := hp.pos
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (p * n) w, fun n => by simpa using hw (p * n), ?_⟩
  rw [kronFun_qExp hp]
  ext n
  have key : PowerSeries.coeff (p * n) (xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2)) =
      PowerSeries.coeff n (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    simp [xp, PowerSeries.coeff_mk, Nat.mul_div_cancel_left n hp0]
  have hsum : xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) =
      prodSer p + xp p ((aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    rw [← gmQ_xp hp0]
    ext m
    simp only [xp, PowerSeries.coeff_mk, map_add]
    split_ifs <;> simp
  rw [← key, hsum, hk]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

theorem kronFun_poly {p : ℕ} (hp : p.Prime) :
    ∃ Q : Polynomial ℂ, (∀ i, Q.coeff i ∈ Rm p) ∧
      ∀ τ, kronFun p τ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * Q.eval (jT τ)) := by
  obtain ⟨w, hw, hqe⟩ := kronFun_div hp
  have hc0 : (1 - zetaC p) ≠ 0 := one_sub_zeta_ne_zero hp
  have hK := kronFun_isMF hp
  let f : ℍ → ℂ := fun τ => (1 - zetaC p)⁻¹ * kronFun p τ
  have hf : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) f := hK.const_mul (1 - zetaC p)⁻¹
  have hwq : qExpansion 1 f = w := by
    apply hf.qExp_eq
    · have e : w = PowerSeries.C (1 - zetaC p)⁻¹ * qExpansion 1 (kronFun p) := by
        rw [hqe, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [e]
      exact hK.conv.C_mul _
    · intro τ
      have hs := (hK.hasSum τ).mul_left (1 - zetaC p)⁻¹
      have hw' : ∀ n, PowerSeries.coeff n w * qm 1 τ ^ n =
          (1 - zetaC p)⁻¹ * (PowerSeries.coeff n (qExpansion 1 (kronFun p)) * qm 1 τ ^ n) := by
        intro n
        rw [hqe, PowerSeries.coeff_C_mul]
        field_simp
      unfold ev
      simp_rw [hw']
      exact hs.tsum_eq
  obtain ⟨P, hPc, -, hPe⟩ := qPrin (Rm p) (2 * (p + 1)) f hf (by rw [hwq]; exact hw)
  refine ⟨P, hPc, fun τ => ?_⟩
  calc kronFun p τ = (1 - zetaC p) * f τ := by
        rw [show f τ = (1 - zetaC p)⁻¹ * kronFun p τ from rfl, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    _ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * P.eval (jT τ)) := by rw [hPe τ]

theorem kronPt {p : ℕ} (hp : p.Prime) {τ : ℍ} (h : Gm p τ = 0) :
    ∃ r : ℂ, IsIntegral ℤ r ∧ (jT τ ^ p - jT τ) ^ 2 = (1 - zetaC p) * r := by
  obtain ⟨Q, hQ, hK⟩ := kronFun_poly hp
  have hD := DD_ne_zero τ
  have hsq : ¬ IsSquare p := Irreducible.not_isSquare hp
  have hj := jT_isIntegral hp.pos hsq h
  have hint : IsIntegral ℤ (Q.eval (jT τ)) := by
    rw [Polynomial.eval_eq_sum_range]
    exact IsIntegral.sum _ fun i _ => (Rm_isIntegral hp.pos (hQ i)).mul (hj.pow i)
  refine ⟨Q.eval (jT τ), hint, ?_⟩
  have e1 := hK τ
  unfold kronFun at e1
  rw [h, zero_add] at e1
  have hA : AA τ = jT τ * DD τ := by rw [jT, div_mul_cancel₀ _ hD]
  rw [hA] at e1
  have e2 : (jT τ ^ p - jT τ) ^ 2 * DD τ ^ (2 * (p + 1)) =
      (1 - zetaC p) * Q.eval (jT τ) * DD τ ^ (2 * (p + 1)) := by
    linear_combination e1
  exact mul_right_cancel₀ (pow_ne_zero _ hD) e2

end ReciprocityTheory.ChartRestriction.L1
end
end

