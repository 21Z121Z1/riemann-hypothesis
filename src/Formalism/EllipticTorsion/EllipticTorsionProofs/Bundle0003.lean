import Mathlib
import Formalism.EllipticTorsion.Bundle0003
import Formalism.EllipticTorsion.EllipticTorsionProofs.Bundle0002
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.CompExp
section
open PowerSeries IsUltrametricDist

universe u

namespace Formalism.ELL.MultiplicativeWeight

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)

def W (w : ℤ) (f : MvPowerSeries σ K) : Prop :=
  ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e f‖ ≤ c ^ (w - (e.degree : ℤ))

variable {c}

theorem W_one (hc : 0 < c) (_hc1 : c ≤ 1) : W c 0 (1 : MvPowerSeries σ K) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp only [norm_zero]; positivity

theorem W_mul (hc : 0 < c) {w₁ w₂ : ℤ} {f g : MvPowerSeries σ K} (hf : W c w₁ f) (hg : W c w₂ g) :
    W c (w₁ + w₂) (f * g) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
  have hp : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 f‖ * ‖MvPowerSeries.coeff p.2 g‖
      ≤ c ^ (w₁ - (p.1.degree : ℤ)) * c ^ (w₂ - (p.2.degree : ℤ)) :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
    _ = c ^ (w₁ + w₂ - (e.degree : ℤ)) := by
        rw [← zpow_add₀ hc.ne', ← hp, map_add]; push_cast; ring_nf

theorem W_pow (hc : 0 < c) (hc1 : c ≤ 1) {w : ℤ} {f : MvPowerSeries σ K} (hf : W c w f) (n : ℕ) :
    W c (n * w) (f ^ n) := by
  induction n with
  | zero => simpa using W_one hc hc1
  | succ n ih => rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact W_mul hc ih hf

theorem W_E (E : PowerSeries K) (hE : constantCoeff E = 0)
    (hb : ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) (hc : 0 < c) (i : σ) :
    W c 1 (E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0, coeff_zero_eq_constantCoeff_apply, hE, norm_zero]; positivity
    · conv_rhs => rw [h, Finsupp.degree_single]
      exact hb _ h0
  · rw [norm_zero]; positivity

theorem W_prod (hc : 0 < c) (hc1 : c ≤ 1) (a : σ → MvPowerSeries σ K) (ha : ∀ i, W c 1 (a i))
    (d : σ →₀ ℕ) : W c (d.degree : ℤ) (d.prod fun s n => a s ^ n) := by
  classical
  unfold Finsupp.prod
  have hdeg : (d.degree : ℤ) = ∑ s ∈ d.support, ((d s : ℕ) : ℤ) := by
    show (((∑ i ∈ d.support, d i : ℕ)) : ℤ) = _
    push_cast; rfl
  rw [hdeg]
  induction d.support using Finset.induction_on with
  | empty => simpa using W_one hc hc1
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs]
    have := W_pow hc hc1 (ha s) (d s)
    rw [mul_one] at this
    exact W_mul hc this ih

theorem comp_exp_coeff_weight_of : CompExpWeight.{u} := by
  intro K _ _ σ _ c hc hc1 E hE hb G hG α
  classical
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := σ) (S := K)
    (a := fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K))
    fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE
  rw [MvPowerSeries.coeff_subst ha]
  have hfin := MvPowerSeries.coeff_subst_finite ha G α
  rw [finsum_eq_sum _ hfin]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d _ => ?_
  rw [smul_eq_mul, norm_mul]
  have h1 := W_prod hc hc1 _ (W_E E hE hb hc) d α
  calc ‖MvPowerSeries.coeff d G‖ * ‖MvPowerSeries.coeff α
          (d.prod fun s e => (E.subst (MvPowerSeries.X s : MvPowerSeries σ K)) ^ e)‖
      ≤ 1 * c ^ ((d.degree : ℤ) - (α.degree : ℤ)) :=
        mul_le_mul (hG d) h1 (norm_nonneg _) zero_le_one
    _ ≤ c ^ (-(α.degree : ℤ)) := by
        rw [one_mul]; exact zpow_le_zpow_right_of_le_one₀ hc hc1 (by omega)

end Formalism.ELL.MultiplicativeWeight

namespace Formalism.ELL

theorem comp_exp_coeff_weight : Formalism.ELL.CompExpWeight := Formalism.ELL.MultiplicativeWeight.comp_exp_coeff_weight_of

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
section
namespace Formalism.ELL

namespace DeuringModel

open Polynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma norm_add_eq_left {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_nat_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

lemma exists_root_deuring [IsAlgClosed K] (j : K) :
    ∃ a : K, a ^ 3 * (a ^ 3 - 24) ^ 3 = j * (a ^ 3 - 27) := by
  let P : K[X] := X ^ 3 * (X ^ 3 - C 24) ^ 3 - C j * (X ^ 3 - C 27)
  have hdeg : P.degree = 12 := by
    simp only [P]
    compute_degree!
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P (by rw [hdeg]; norm_num)
  refine ⟨a, ?_⟩
  simp only [P, IsRoot, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at ha
  exact sub_eq_zero.mp ha

end DeuringModel

open DeuringModel in
theorem deuring_model : ModelDeuring := by
  intro K _ _ _ h3 j hj
  obtain ⟨a, ha⟩ := exists_root_deuring j
  have hc4 : (deuring a).c₄ = a * (a ^ 3 - 24) := by
    simp [deuring, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hΔ : (deuring a).Δ = a ^ 3 - 27 := by
    simp [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have h27 : ‖(27 : K)‖ = 1 := by
    have e : (27 : K) = 3 ^ 3 := by norm_num
    rw [e, norm_pow, h3, one_pow]
  have ha1 : ‖a‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hA3 : ‖a ^ 3‖ = ‖a‖ ^ 3 := norm_pow a 3
    have hbig : 1 < ‖a‖ ^ 3 := one_lt_pow₀ hlt (by norm_num)
    have h24 : ‖(24 : K)‖ ≤ 1 := by exact_mod_cast norm_nat_le_one (K := K) 24
    have hn1 : ‖a ^ 3 - 24‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hn2 : ‖a ^ 3 - 27‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = ‖a‖ ^ 12 := by
      rw [norm_mul, hA3, norm_pow, hn1]
      ring
    have hR : ‖j * (a ^ 3 - 27)‖ ≤ ‖a‖ ^ 3 := by
      rw [norm_mul, hn2]
      calc ‖j‖ * ‖a‖ ^ 3 ≤ 1 * ‖a‖ ^ 3 := by gcongr
        _ = ‖a‖ ^ 3 := one_mul _
    rw [ha] at hL
    have hlt2 : ‖a‖ ^ 3 < ‖a‖ ^ 12 := pow_lt_pow_right₀ hlt (by norm_num)
    linarith
  have hA3le : ‖a ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha1
  have hΔle : ‖a ^ 3 - 27‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA3le (by rw [norm_neg, h27]))
  have hΔ1 : ‖a ^ 3 - 27‖ = 1 := by
    by_contra hne
    have hlt : ‖a ^ 3 - 27‖ < 1 := lt_of_le_of_ne hΔle hne
    have e1 : a ^ 3 = 27 + (a ^ 3 - 27) := by ring
    have hA : ‖a ^ 3‖ = 1 := by
      rw [e1, norm_add_eq_left (by rw [h27]; exact hlt), h27]
    have e2 : a ^ 3 - 24 = 3 + (a ^ 3 - 27) := by ring
    have hB : ‖a ^ 3 - 24‖ = 1 := by
      rw [e2, norm_add_eq_left (by rw [h3]; exact hlt), h3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = 1 := by
      rw [norm_mul, hA, norm_pow, hB]
      norm_num
    rw [ha, norm_mul] at hL
    have h4 : ‖j‖ * ‖a ^ 3 - 27‖ < 1 := by
      calc ‖j‖ * ‖a ^ 3 - 27‖ ≤ 1 * ‖a ^ 3 - 27‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hlt
    linarith
  refine ⟨a, ha1, ?_, ?_⟩
  · rw [hc4, hΔ, ← ha]
    ring
  · rw [hΔ, hΔ1]

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.ExpWeight
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.ExponentialCoefficientWeight

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem mul_le {f g : PowerSeries K} {r A B : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {N : ℕ} (hf : ∀ d ≤ N, ‖coeff d f‖ ≤ A * r ^ d) (hg : ∀ d ≤ N, ‖coeff d g‖ ≤ B * r ^ d) :
    ∀ d ≤ N, ‖coeff d (f * g)‖ ≤ (A * B) * r ^ d := by
  intro d hd
  rw [coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro x hx
  have hx : x.1 + x.2 = d := by simpa using hx
  rw [norm_mul, ← hx, pow_add]
  have h1 := hf x.1 (by omega)
  have h2 := hg x.2 (by omega)
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ ≤ (A * r ^ x.1) * (B * r ^ x.2) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = A * B * (r ^ x.1 * r ^ x.2) := by ring

theorem pow_le {f : PowerSeries K} {r A : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) {N : ℕ}
    (hf : ∀ d ≤ N, ‖coeff d f‖ ≤ A * r ^ d) :
    ∀ m : ℕ, ∀ d ≤ N, ‖coeff d (f ^ m)‖ ≤ A ^ m * r ^ d := by
  intro m
  induction m with
  | zero =>
    intro d hd
    rw [pow_zero, pow_zero, one_mul, coeff_one]
    split_ifs with h
    · subst h; simp
    · rw [norm_zero]; positivity
  | succ k ih =>
    intro d hd
    rw [pow_succ, pow_succ]
    exact mul_le hr (by positivity) hA ih hf d hd

theorem mul_le_strict {f g : PowerSeries K} {r A B : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hB : 0 ≤ B) {n : ℕ} (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf : ∀ d < n, ‖coeff d f‖ ≤ A * r ^ d) (hg : ∀ d < n, ‖coeff d g‖ ≤ B * r ^ d) :
    ‖coeff n (f * g)‖ ≤ (A * B) * r ^ n := by
  rw [coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro x hx
  have hx : x.1 + x.2 = n := by simpa using hx
  rcases Nat.eq_zero_or_pos x.1 with h1 | h1
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hf0, zero_mul, norm_zero]; positivity
  rcases Nat.eq_zero_or_pos x.2 with h2 | h2
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hg0, mul_zero, norm_zero]; positivity
  rw [norm_mul, ← hx, pow_add]
  have e1 := hf x.1 (by omega)
  have e2 := hg x.2 (by omega)
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ ≤ (A * r ^ x.1) * (B * r ^ x.2) :=
        mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
    _ = A * B * (r ^ x.1 * r ^ x.2) := by ring

theorem inv_le {l E : PowerSeries K} {r : ℝ} (hr : 0 < r)
    (hE0 : constantCoeff E = 0) (hl1 : coeff 1 l = 1)
    (hl : ∀ m, 2 ≤ m → ‖coeff m l‖ ≤ r⁻¹ * r ^ m)
    (hsub : l.subst E = X) :
    ∀ n, 1 ≤ n → ‖coeff n E‖ ≤ r⁻¹ * r ^ n := by
  have hS : HasSubst E := HasSubst.of_constantCoeff_zero' hE0
  have hexp : ∀ n, coeff n (X : PowerSeries K) =
      ∑ m ∈ Finset.range (n + 1), coeff m l * coeff n (E ^ m) := by
    intro n
    rw [← hsub, coeff_subst' hS]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) ?_]
    · simp only [smul_eq_mul]
    · intro m hm
      simp only [Function.mem_support] at hm
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hm
      rw [coeff_of_lt_order n, smul_zero]
      exact lt_of_lt_of_le (by exact_mod_cast (by omega : n < m))
        (le_order_pow_of_constantCoeff_eq_zero m hE0)
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have hEb : ∀ d < k + 1, ‖coeff d E‖ ≤ r⁻¹ * r ^ d := by
    intro d hd
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, coeff_zero_eq_constantCoeff_apply, hE0, norm_zero]; positivity
    · exact ih d hd h0
  have hEb' : ∀ d ≤ k, ‖coeff d E‖ ≤ r⁻¹ * r ^ d := fun d hd => hEb d (by omega)
  have hE : coeff (k + 1) E = coeff (k + 1) (X : PowerSeries K) -
      ∑ i ∈ Finset.range k, coeff (i + 2) l * coeff (k + 1) (E ^ (i + 2)) := by
    have h := hexp (k + 1)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    rw [h]
    simp only [zero_add, pow_one, pow_zero, hl1, one_mul, coeff_one, Nat.add_one_ne_zero,
      if_false, mul_zero, add_zero]
    ring
  rw [hE]
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [coeff_X]
    split_ifs with h1
    · have : k = 0 := by omega
      subst this
      rw [norm_one, zero_add, pow_one, inv_mul_cancel₀ hr.ne']
    · rw [norm_zero]; positivity
  · rw [norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul]
    have hpow0 : constantCoeff (E ^ (i + 1)) = 0 := by
      rw [map_pow, hE0, zero_pow (Nat.succ_ne_zero _)]
    have hc : ‖coeff (k + 1) (E ^ (i + 2))‖ ≤ (r⁻¹ * r⁻¹ ^ (i + 1)) * r ^ (k + 1) := by
      rw [pow_succ' E (i + 1)]
      exact mul_le_strict hr.le hri.le (by positivity) hE0 hpow0 hEb
        (fun d hd => pow_le hr.le hri.le hEb' (i + 1) d (by omega))
    have ha := hl (i + 2) (by omega)
    have hone : r ^ (i + 2) * r⁻¹ ^ (i + 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
    calc ‖coeff (i + 2) l‖ * ‖coeff (k + 1) (E ^ (i + 2))‖
        ≤ (r⁻¹ * r ^ (i + 2)) * ((r⁻¹ * r⁻¹ ^ (i + 1)) * r ^ (k + 1)) :=
          mul_le_mul ha hc (norm_nonneg _) (by positivity)
      _ = r⁻¹ * r ^ (k + 1) * (r ^ (i + 2) * r⁻¹ ^ (i + 2)) := by ring
      _ = r⁻¹ * r ^ (k + 1) := by rw [hone, mul_one]

end Formalism.ELL.ExponentialCoefficientWeight

namespace Formalism.ELL

open Formalism.G

theorem expWeight_of (h : LogWeight.{u}) : ExpWeight.{u} := by
  intro K _ _ _ p q hp hp0 hp1 hq F e l E he hei he1 hegap hlog hE0 _hEl hlE n hn
  have hlw := h K p q hp hp0 hp1 hq F e l he hei he1 hegap hlog
  have hr0 : 0 < ‖(p : K)‖ ^ (-1 / ((q : ℝ) - 1)) := Real.rpow_pos_of_pos hp0 _
  have key : ∀ m : ℕ, (‖(p : K)‖ ^ (-1 / ((q : ℝ) - 1)))⁻¹ *
      (‖(p : K)‖ ^ (-1 / ((q : ℝ) - 1))) ^ m =
        ‖(p : K)‖ ^ (-((m : ℝ) - 1) / ((q : ℝ) - 1)) := by
    intro m
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_neg hp0.le,
      ← Real.rpow_add hp0]
    congr 1
    ring
  have := ExponentialCoefficientWeight.inv_le hr0 hE0 hlog.2.1
    (fun m hm => by rw [key m]; exact hlw m (by omega)) hlE n hn
  rwa [key n] at this

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.JetsOne
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.FormalGroupLinearJets

variable {K : Type u} [CommRing K]

theorem constantCoeff_pderiv_unit (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K () f) = coeff 1 f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp [PowerSeries.coeff]

theorem coeff_one_subst {φ a : PowerSeries K} (ha : constantCoeff a = 0) :
    coeff 1 (φ.subst a) = coeff 1 φ * coeff 1 a := by
  have h := Formalism.G.LogCR.pderiv_psubst (τ := Unit) (a := (a : MvPowerSeries Unit K)) ha φ ()
  have h2 := congrArg MvPowerSeries.constantCoeff h
  rw [constantCoeff_pderiv_unit, map_mul, constantCoeff_pderiv_unit] at h2
  rw [h2]
  congr 1
  rw [PowerSeries.subst_def,
    Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (τ := Unit) _ (fun _ => ha)]
  show PowerSeries.constantCoeff (PowerSeries.derivative K φ) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp

end Formalism.ELL.FormalGroupLinearJets

namespace Formalism.ELL

open Formalism.G Formalism.ELL.FormalGroupLinearJets

theorem jetsOne_of (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsOne.{u} := by
  intro K _ _ _ F φ a n ha hG
  have hP := hN K Unit _ hG ()
  have h0 := hP 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_pderiv_unit, map_sub,
    coeff_one_subst ha.1, map_smul, smul_eq_mul] at h0
  have hD : constantCoeff (invD F φ) = coeff 1 φ := by
    have hw : constantCoeff (omegaF F) = 1 := Formalism.G.LogP.constantCoeff_omega (FK F)
    rw [invD, map_mul, hw, one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative]
    simp
  rw [hD]
  convert h0 using 2
  ring

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt
section
universe u

noncomputable section

namespace Formalism.ELL.TorsionIntegralEllipticTorsion

open WeierstrassCurve Formalism.ELL

lemma y_int {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) :
    ‖y‖ ≤ 1 := by
  have hW' := hW
  unfold IntegralModel at hW'
  have h' := h
  rw [WeierstrassCurve.Affine.equation_iff] at h'
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW'
  have hadd : ∀ a b : K, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a + b‖ ≤ 1 := fun a b ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  have hmul : ∀ a b : K, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a * b‖ ≤ 1 := fun a b ha hb => by
    rw [norm_mul]
    first
    | exact mul_le_one₀ ha (norm_nonneg _) hb
    | nlinarith [norm_nonneg a, norm_nonneg b]
  have hx2 : ‖x ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | nlinarith [norm_nonneg x]
  have hx3 : ‖x ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | nlinarith [norm_nonneg x, hx2]
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 :=
    hadd _ _ (hadd _ _ (hadd _ _ hx3 (hmul _ _ h2 hx2)) (hmul _ _ h4 hx)) h6
  by_contra hy
  push_neg at hy
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hm : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖y‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖W.a₁ * x‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (hmul _ _ h1 hx) hy0
        _ = ‖y‖ := one_mul _
    · rw [norm_mul]
      calc ‖W.a₃‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h3 hy0
        _ = ‖y‖ := one_mul _
  have hy2 : y ^ 2 = (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) - (W.a₁ * x * y + W.a₃ * y) := by
    first
    | linear_combination h'
    | (rw [← h']; ring)
  have hsub : ‖(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) - (W.a₁ * x * y + W.a₃ * y)‖ ≤ ‖y‖ := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hR.trans hy.le) ?_)
    rw [norm_neg]
    exact hm
  have hn : ‖y‖ ^ 2 ≤ ‖y‖ := by
    rw [← norm_pow, hy2]
    exact hsub
  nlinarith

end Formalism.ELL.TorsionIntegralEllipticTorsion

namespace Formalism.ELL

open WeierstrassCurve

theorem torsionIntegral_of (h : Formalism.ELL.FormalGroupPointsTorsionFree.{u}) : Formalism.ELL.TorsionIntegral.{u} := by
  intro K _ _ W hW hΔ n hn x y hxy hnP
  have hx : ‖x‖ ≤ 1 := by
    by_contra hx
    push Not at hx
    exact Affine.Point.some_ne_zero hxy (h K W hW hΔ n hn _ hx hnP)
  exact ⟨hx, TorsionIntegralEllipticTorsion.y_int W hW hxy.1 hx⟩

end Formalism.ELL
end
end

