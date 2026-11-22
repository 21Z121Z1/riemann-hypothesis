import Formalism.TorsionNormIteration.InvIntegralOfClass
import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
import Formalism.TorsionNormIteration.Statement

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.CoeffSubstAddCMulXPow
section
noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.CongrP

open Formalism.G

section Ring

variable {R : Type*} [CommRing R]

lemma coeff_subst_range (f a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    coeff N (f.subst a) = ∑ n ∈ Finset.range (N + 1), coeff n f * coeff N (a ^ n) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' ha)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1))]
  · simp [smul_eq_mul]
  · intro n hn
    simp only [Function.mem_support] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    obtain ⟨b, rfl⟩ := X_dvd_iff.mpr ha
    rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

lemma constantCoeff_trunc_succ (a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    constantCoeff (trunc (N + 1) a : PowerSeries R) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_coe_trunc_of_lt (Nat.succ_pos N),
    coeff_zero_eq_constantCoeff_apply, ha]

lemma coeff_subst_trunc (f a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    coeff N (f.subst (trunc (N + 1) a : PowerSeries R)) = coeff N (f.subst a) := by
  rw [coeff_subst_range f _ (constantCoeff_trunc_succ a ha N), coeff_subst_range f a ha]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [← coeff_coe_trunc_of_lt (Nat.lt_succ_self N) (f := (trunc (N + 1) a : PowerSeries R) ^ n),
    trunc_trunc_pow, coeff_coe_trunc_of_lt (Nat.lt_succ_self N)]

lemma sum_zero_pow_mul (n : ℕ) :
    ∑ i ∈ Finset.range n, (0 : R) ^ i * (0 : R) ^ (n - 1 - i) = if n = 1 then 1 else 0 := by
  rcases n with _ | n
  · simp
  · rw [Finset.sum_range_succ']
    simp only [pow_succ, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, pow_zero, one_mul]
    rcases n with _ | n <;> simp

lemma coeff_subst_add_C_mul_X_pow (f b : PowerSeries R) (hb : constantCoeff b = 0) (c : R)
    {N : ℕ} (hN : 1 ≤ N) :
    coeff N (f.subst (b + C c * X ^ N)) = coeff N (f.subst b) + coeff 1 f * c := by
  have he : constantCoeff (C c * X ^ N : PowerSeries R) = 0 := by
    rw [map_mul, map_pow, constantCoeff_X, zero_pow (by omega), mul_zero]
  have hbe : constantCoeff (b + C c * X ^ N) = 0 := by rw [map_add, hb, he, add_zero]
  have key : ∀ n : ℕ, coeff N ((b + C c * X ^ N) ^ n) = coeff N (b ^ n) + if n = 1 then c else 0 := by
    intro n
    have hg := geom_sum₂_mul (b + C c * X ^ N) b n
    have hx : (b + C c * X ^ N) ^ n = b ^ n + X ^ N * (C c * ∑ i ∈ Finset.range n,
        (b + C c * X ^ N) ^ i * b ^ (n - 1 - i)) := by
      rw [← sub_eq_iff_eq_add', ← hg]
      ring
    rw [hx, map_add, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_C, map_sum]
    simp only [map_mul, map_pow, hbe, hb]
    rw [sum_zero_pow_mul]
    split_ifs <;> simp
  rw [coeff_subst_range f _ hbe, coeff_subst_range f b hb]
  simp_rw [key, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  congr 1
  rw [Finset.sum_eq_single 1]
  · simp
  · intro n _ hn; simp [hn]
  · intro h; exfalso; apply h; simp; omega

end Ring

section Norm

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma mv_coeff_eq (φ : PowerSeries K) (d : Unit →₀ ℕ) :
    MvPowerSeries.coeff d φ = coeff (d ()) φ := by
  conv_lhs => rw [Finsupp.unique_single d]
  rfl

lemma integralMv_of (φ : PowerSeries K) (h : IntegralPS φ) : IntegralMv φ := fun d => by
  rw [mv_coeff_eq]; exact h _

lemma divByMv_of (x : K) (φ : PowerSeries K) (h : DivBy x φ) : DivByMv x φ := fun d => by
  rw [mv_coeff_eq]; exact h _

lemma norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa using IsUltrametricDist.norm_add_le_max a (-b)

theorem fwd (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) [CharZero K]
    {p q : ℕ} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ) {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hfe : IsFunEqType p q σ f) {α β : PowerSeries K}
    (hα0 : constantCoeff α = 0) (hβ0 : constantCoeff β = 0) (hα : IntegralPS α)
    (hβ : IntegralPS β) {r : ℕ} (hr : 1 ≤ r) (hd : DivBy ((p : K) ^ r) (α - β)) :
    DivBy ((p : K) ^ r) (f.subst α - f.subst β) := by
  intro N
  rw [map_sub, coeff_subst_range f α hα0, coeff_subst_range f β hβ0, ← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
  intro n _
  rw [← mul_sub, ← map_sub, norm_mul]
  obtain ⟨k, ⟨m, hm⟩, hk⟩ := h5 K p q σ hS f hf0 hfe n
  obtain ⟨h, hh0, hq⟩ := hS.2.1
  have hp1 : ‖(p : K)‖ ≤ 1 := hS.2.2.1.le
  have hpc := h6 K Unit p hS.1 α β (integralMv_of α hα) (integralMv_of β hβ) r hr
    (divByMv_of _ _ hd) (h * k) m (Finsupp.single () N)
  have hn : n = p ^ (h * k) * m := by rw [hm, hq, pow_mul]
  rw [mv_coeff_eq, ← hn] at hpc
  simp only [Finsupp.single_eq_same, norm_pow] at hpc
  have hkk : ‖(p : K)‖ ^ (r + h * k) ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r := by
    rw [pow_add, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
    exact pow_le_pow_of_le_one (norm_nonneg _) hp1 (Nat.le_mul_of_pos_left k hh0)
  calc ‖coeff n f‖ * ‖coeff N (α ^ n - β ^ n)‖
      ≤ ‖coeff n f‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r) :=
        mul_le_mul_of_nonneg_left (hpc.trans hkk) (norm_nonneg _)
    _ = (‖coeff n f‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ ^ r := by ring
    _ ≤ 1 * ‖(p : K)‖ ^ r := mul_le_mul_of_nonneg_right hk (pow_nonneg (norm_nonneg _) _)
    _ = ‖(p : K) ^ r‖ := by rw [one_mul, norm_pow]

end Norm

section Back

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma integralPS_trunc {a : PowerSeries K} (ha : IntegralPS a) (M : ℕ) :
    IntegralPS (trunc M a : PowerSeries K) := fun n => by
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs
  · exact ha n
  · simp

theorem bwd (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) [CharZero K]
    {p q : ℕ} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ) {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hfe : IsFunEqType p q σ f)
    {α β : PowerSeries K}
    (hα0 : constantCoeff α = 0) (hβ0 : constantCoeff β = 0) (hα : IntegralPS α)
    (hβ : IntegralPS β) {r : ℕ} (hr : 1 ≤ r)
    (hd : DivBy ((p : K) ^ r) (f.subst α - f.subst β)) :
    DivBy ((p : K) ^ r) (α - β) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [coeff_zero_eq_constantCoeff_apply, map_sub, hα0, hβ0, sub_zero, norm_zero]
    exact norm_nonneg _
  set c := coeff N (α - β) with hc
  have hc1 : ‖c‖ ≤ 1 := by
    rw [hc, map_sub]; exact (norm_sub_le_max' _ _).trans (max_le (hα N) (hβ N))
  set β₁ : PowerSeries K := β + C c * X ^ N with hβ₁
  have hcoeffβ₁ : ∀ n, coeff n β₁ = coeff n β + if n = N then c else 0 := by
    intro n
    rw [hβ₁, map_add, coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp
  have hβ₁0 : constantCoeff β₁ = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hcoeffβ₁, if_neg (by omega), add_zero,
      coeff_zero_eq_constantCoeff_apply, hβ0]
  have hβ₁i : IntegralPS β₁ := fun n => by
    rw [hcoeffβ₁]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hβ n) ?_)
    split_ifs
    · exact hc1
    · simp
  have hdt : DivBy ((p : K) ^ r)
      ((trunc (N + 1) α : PowerSeries K) - (trunc (N + 1) β₁ : PowerSeries K)) := by
    intro n
    rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_trunc, coeff_trunc]
    by_cases hn : n < N + 1
    · rw [if_pos hn, if_pos hn, hcoeffβ₁]
      by_cases hnN : n = N
      · subst hnN
        rw [if_pos rfl, hc, map_sub]
        simp
      · rw [if_neg hnN, add_zero, ← map_sub]
        exact ih n (by omega)
    · rw [if_neg hn, if_neg hn, sub_zero, norm_zero]; exact norm_nonneg _
  have hf := fwd h5 h6 hS hf0 hfe (constantCoeff_trunc_succ α hα0 N)
    (constantCoeff_trunc_succ β₁ hβ₁0 N) (integralPS_trunc hα _) (integralPS_trunc hβ₁i _) hr
    hdt N
  rw [map_sub, coeff_subst_trunc f α hα0, coeff_subst_trunc f β₁ hβ₁0] at hf
  have hkey := coeff_subst_add_C_mul_X_pow f β hβ0 c (N := N) hN
  rw [← hβ₁, hf1, one_mul] at hkey
  have hA := hd N
  rw [map_sub] at hA
  have : c = (coeff N (f.subst α) - coeff N (f.subst β)) -
      (coeff N (f.subst α) - coeff N (f.subst β₁)) := by rw [hkey]; ring
  rw [this]
  exact (norm_sub_le_max' _ _).trans (max_le hA hf)

end Back

theorem funEqCongr (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) :
    Formalism.G.FunEqCongr.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfe α β hα0 hβ0 hα hβ r hr
  exact ⟨fwd h5 h6 hS hf0 hfe hα0 hβ0 hα hβ hr, bwd h5 h6 hS hf0 hf1 hfe hα0 hβ0 hα hβ hr⟩

end Formalism.LT.CongrP

theorem Formalism.LT.FunEqCongr_of (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) :
    Formalism.G.FunEqCongr.{u} := Formalism.LT.CongrP.funEqCongr h5 h6
end
end

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd
section
noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.ExpP

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_natCast_of_not_dvd {p m : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hm : ¬ p ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) ?_
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * m = 1 := by
    have h := Nat.gcd_eq_gcd_ab p m
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact ⟨Nat.gcdA p m, Nat.gcdB p m, by push_cast at h; linarith⟩
  have h1 : (1 : K) = (a : K) * (p : K) + (b : K) * (m : K) := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hle : (1 : ℝ) ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖(a : K) * p + (b : K) * m‖ := by rw [← h1]
      _ ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := IsUltrametricDist.norm_add_le_max _ _
  have ha := IsUltrametricDist.norm_intCast_le_one K a
  have hb := IsUltrametricDist.norm_intCast_le_one K b
  rcases le_max_iff.1 hle with h | h
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (p : K), norm_nonneg (a : K)]
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (m : K), norm_nonneg (b : K)]

lemma norm_natCast_eq {p n : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hn : n ≠ 0) :
    ‖(n : K)‖ = ‖(p : K)‖ ^ padicValNat p n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  haveI := Fact.mk hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero]
  push_cast
  rw [norm_mul, norm_pow, norm_natCast_of_not_dvd hp hp1 hm, mul_one]

theorem expIntegral : Formalism.LT.ExpIntegral.{u} := by
  intro K _ _ _ p hp hp1 c hc n
  haveI := Fact.mk hp
  rw [norm_div, norm_pow, norm_natCast_eq hp hp1 (Nat.factorial_ne_zero n)]
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpos : 0 < ‖(p : K)‖ ^ padicValNat p n.factorial := pow_pos (norm_pos_iff.2 hp0) _
  rw [div_le_one hpos]
  have hv : (p - 1) * padicValNat p n.factorial ≤ n := by
    have := sub_one_mul_padicValNat_factorial (p := p) n
    omega
  have hc1 : ‖c‖ ≤ 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := p - 1) h.le
    linarith
  calc ‖c‖ ^ n ≤ ‖c‖ ^ ((p - 1) * padicValNat p n.factorial) :=
        pow_le_pow_of_le_one (norm_nonneg _) hc1 hv
    _ = (‖c‖ ^ (p - 1)) ^ padicValNat p n.factorial := pow_mul _ _ _
    _ ≤ ‖(p : K)‖ ^ padicValNat p n.factorial := pow_le_pow_left₀ (by positivity) hc _

lemma norm_finsum_le {g : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  by_cases h : (Function.support g).Finite
  · rw [finsum_eq_sum g h]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support h, norm_zero]
    exact hC

lemma scalar_bound {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (c : K) (d m : ℕ) (hmd : m < d)
    (hc : ‖(d : K) * c‖ ≤ 1) :
    ‖c * ((p : K) ^ (d - m) * (d.choose m : K))‖ ≤ ‖(p : K)‖ := by
  haveI := Fact.mk hp
  have hP0 : 0 ≤ ‖(p : K)‖ := norm_nonneg _
  have hP1 : ‖(p : K)‖ ≤ 1 := hp1.le
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, n + 1 - m = j + 1 := ⟨n - m, by omega⟩
  have hsym : (n + 1).choose (j + 1) = (n + 1).choose m := by
    rw [← hj]
    exact Nat.choose_symm (by omega)
  have hN : (n + 1).choose m * (j + 1) = (n + 1) * n.choose j := by
    rw [← hsym, Nat.add_one_mul_choose_eq]
  have hnorm : ‖((n + 1).choose m : K)‖ * ‖((j + 1 : ℕ) : K)‖ ≤ ‖((n + 1 : ℕ) : K)‖ := by
    have h := congrArg (fun x : ℕ => ‖(x : K)‖) hN
    simp only [Nat.cast_mul, norm_mul] at h
    rw [h]
    exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _)
  have hkn : ‖((j + 1 : ℕ) : K)‖ = ‖(p : K)‖ ^ padicValNat p (j + 1) :=
    norm_natCast_eq hp hp1 (Nat.succ_ne_zero j)
  have hv : padicValNat p (j + 1) < j + 1 := by
    have h1 : p ^ padicValNat p (j + 1) ≤ j + 1 := Nat.le_of_dvd (Nat.succ_pos j) pow_padicValNat_dvd
    have h2 : j + 1 < p ^ (j + 1) := Nat.lt_pow_self hp.one_lt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 (lt_of_le_of_lt h1 h2)
  have hcd : ‖c‖ * ‖((n + 1 : ℕ) : K)‖ ≤ 1 := by
    rw [mul_comm, ← norm_mul]
    exact_mod_cast hc
  rw [hj, norm_mul, norm_mul, norm_pow]
  have key : ‖c‖ * ‖((n + 1).choose m : K)‖ * ‖(p : K)‖ ^ padicValNat p (j + 1) ≤ 1 := by
    calc ‖c‖ * ‖((n + 1).choose m : K)‖ * ‖(p : K)‖ ^ padicValNat p (j + 1)
        = ‖c‖ * (‖((n + 1).choose m : K)‖ * ‖((j + 1 : ℕ) : K)‖) := by rw [hkn]; ring
      _ ≤ ‖c‖ * ‖((n + 1 : ℕ) : K)‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ ≤ 1 := hcd
  have hk' : ‖(p : K)‖ ^ (j + 1) =
      ‖(p : K)‖ ^ padicValNat p (j + 1) * ‖(p : K)‖ ^ (j + 1 - padicValNat p (j + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  calc ‖c‖ * (‖(p : K)‖ ^ (j + 1) * ‖((n + 1).choose m : K)‖)
      = (‖c‖ * ‖((n + 1).choose m : K)‖ * ‖(p : K)‖ ^ padicValNat p (j + 1)) *
          ‖(p : K)‖ ^ (j + 1 - padicValNat p (j + 1)) := by rw [hk']; ring
    _ ≤ 1 * ‖(p : K)‖ ^ (j + 1 - padicValNat p (j + 1)) :=
        mul_le_mul_of_nonneg_right key (pow_nonneg hP0 _)
    _ ≤ ‖(p : K)‖ := by
        rw [one_mul]
        exact pow_le_of_le_one hP0 hP1 (by omega)

lemma norm_coeff_monomial_le (m k : ℕ) (e : Fin 2 →₀ ℕ) :
    ‖MvPowerSeries.coeff e
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * MvPowerSeries.X 1 ^ k)‖ ≤ 1 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one,
    MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

lemma term_eq (p c : K) (d m : ℕ) :
    c • ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * (p • MvPowerSeries.X 1) ^ (d - m) *
      (d.choose m : MvPowerSeries (Fin 2) K)) =
    (c * (p ^ (d - m) * (d.choose m : K))) •
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * MvPowerSeries.X 1 ^ (d - m)) := by
  simp only [MvPowerSeries.smul_eq_C_mul, mul_pow, map_mul, map_pow, map_natCast]
  ring

lemma term_bound {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (z : PowerSeries K)
    (hdz : IntegralPS (PowerSeries.derivative K z)) (d : ℕ) (e : Fin 2 →₀ ℕ) :
    ‖coeff d z • MvPowerSeries.coeff e
      (((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) + (p : K) • MvPowerSeries.X 1) ^ d -
        MvPowerSeries.X 0 ^ d)‖ ≤
        ‖(p : K)‖ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hc : ‖(d : K) * coeff d z‖ ≤ 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    have h := hdz n
    rw [PowerSeries.coeff_derivative] at h
    push_cast
    rw [mul_comm]
    exact h
  rw [add_pow, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right, map_sum,
    Finset.smul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun m hm => ?_
  have hmd : m < d := Finset.mem_range.1 hm
  rw [← map_smul (MvPowerSeries.coeff e), term_eq, map_smul, smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_coeff_monomial_le _ _ _)).trans
    (scalar_bound hp hp1 _ d m hmd hc)

theorem quasiLogShift : Formalism.LT.QuasiLogShift.{u} := by
  intro K _ _ p hp hp1 z hz0 hdz e
  have ha : PowerSeries.HasSubst
      (MvPowerSeries.X (0 : Fin 2) + (p : K) • MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hb : PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X 0
  unfold Formalism.G.atX
  rw [map_sub, PowerSeries.coeff_subst ha, PowerSeries.coeff_subst hb,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite ha z e) (PowerSeries.coeff_subst_finite hb z e)]
  refine norm_finsum_le (norm_nonneg _) fun d => ?_
  rw [← smul_sub, ← map_sub]
  exact term_bound hp hp1 z hdz d e

theorem Formalism.LT.ExpP.ExpIntegral_valid : Formalism.LT.ExpIntegral.{u} := expIntegral

theorem Formalism.LT.ExpP.QuasiLogShift_valid_direct : Formalism.LT.QuasiLogShift.{u} := quasiLogShift

end Formalism.LT.ExpP

theorem Formalism.LT.exp_integral : Formalism.LT.ExpIntegral.{u} := Formalism.LT.ExpP.expIntegral

theorem Formalism.LT.QuasiLogShift_valid : Formalism.LT.QuasiLogShift.{u} := Formalism.LT.ExpP.quasiLogShift
end
end

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.TorsionNormIterProof
section
noncomputable section

universe u

namespace Formalism.LT.TorsProof

open Polynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma norm_sum_lt {s : Finset ℕ} {f : ℕ → K} {c : ℝ} (hc : 0 < c)
    (h : ∀ i ∈ s, ‖f i‖ < c) : ‖∑ i ∈ s, f i‖ < c := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, hc]
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    exact hle.trans_lt (h i hi)

section LT

variable {π : K} {q : ℕ} {e : Polynomial K}

lemma eval_eq (e : Polynomial K) (x : K) :
    e.eval x = ∑ i ∈ Finset.range (e.natDegree + 1), e.coeff i * x ^ i :=
  Polynomial.eval_eq_sum_range x

lemma term_le (he : IsLTPoly q π e) {x : K} (hx : ‖x‖ ≤ 1) {i : ℕ} (hiq : i ≠ q) :
    ‖e.coeff i * x ^ i‖ ≤ ‖π‖ * ‖x‖ := by
  obtain ⟨h0, h1, -, hrest⟩ := he
  rcases Nat.lt_or_ge i 1 with hi | hi
  · have : i = 0 := by omega
    subst this; simp [h0, mul_nonneg (norm_nonneg π) (norm_nonneg x)]
  · rcases eq_or_ne i 1 with rfl | hi1
    · simp [h1]
    · rw [norm_mul, norm_pow]
      have hxi : ‖x‖ ^ i ≤ ‖x‖ := pow_le_of_le_one (norm_nonneg x) hx (by omega)
      exact mul_le_mul (hrest i hi1 hiq) hxi (by positivity) (norm_nonneg π)

lemma one_mem (hπ : 0 < ‖π‖) (he : IsLTPoly q π e) : 1 ∈ Finset.range (e.natDegree + 1) := by
  have : e.coeff 1 ≠ 0 := by
    rw [he.2.1]; intro h; rw [h, norm_zero] at hπ; exact lt_irrefl _ hπ
  exact Finset.mem_range.2 (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero this))

lemma norm_eval_le (hq : 2 ≤ q) (he : IsLTPoly q π e) {x : K} (hx : ‖x‖ < 1)
    (hsmall : ‖x‖ ^ (q - 1) ≤ ‖π‖) : ‖e.eval x‖ ≤ ‖π‖ * ‖x‖ := by
  rw [eval_eq]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg π) (norm_nonneg x))
  intro i _
  rcases eq_or_ne i q with rfl | hiq
  · rw [norm_mul, he.2.2.1, one_mul, norm_pow]
    have : ‖x‖ ^ i = ‖x‖ ^ (i - 1) * ‖x‖ := by rw [← pow_succ]; congr 1; omega
    rw [this]; exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg x)
  · exact term_le he hx.le hiq

end LT

end Formalism.LT.TorsProof

open Formalism.LT.TorsProof
end
end

