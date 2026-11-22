import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOps

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.CoeffOneLNeZero
section
noncomputable section

open Classical

namespace PI.BeDiagZp.IdentW

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_l {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have hex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have key := congrArg (PowerSeries.coeff 0) h
  rw [PowerSeries.coeff_subst' hex, finsum_eq_single _ 0] at key
  · simpa using key
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hex0, zero_pow hd, smul_zero]

theorem coeff_one_l_ne_zero {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.coeff 1 l ≠ 0 := by
  intro h1
  have hex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hXe : (PowerSeries.X : PowerSeries ℂ_[p]) ∣ ex := PowerSeries.X_dvd_iff.2 hex0
  have key := congrArg (PowerSeries.coeff 1) h
  rw [PowerSeries.coeff_subst' hex, finsum_eq_zero_of_forall_eq_zero] at key
  · simp at key
  · intro d
    rcases Nat.lt_or_ge d 2 with hd | hd
    · interval_cases d
      · simp
      · rw [h1, zero_smul]
    · have h0 : PowerSeries.coeff 1 (ex ^ d) = 0 :=
        PowerSeries.X_pow_dvd_iff.1 ((pow_dvd_pow PowerSeries.X hd).trans (pow_dvd_pow_of_dvd hXe d)) 1
          (by norm_num)
      rw [h0, smul_zero]

theorem subst_left_inv {K : Type*} [Field K] {l ex : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hu : IsUnit (PowerSeries.coeff 1 l)) (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  set Q := PowerSeries.substInvOfIsUnit l hu with hQ
  have hQl : PowerSeries.subst l Q = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left l hl0 hu
  have hl : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have key : PowerSeries.subst ex (PowerSeries.subst l Q) = PowerSeries.subst (PowerSeries.subst ex l) Q :=
    PowerSeries.subst_comp_subst_apply hl hex Q
  rw [hQl, h, PowerSeries.subst_X hex, PowerSeries.X_subst] at key
  rw [key, hQl]

theorem subst_l_ex {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X :=
  subst_left_inv (constantCoeff_l hex0 h) (isUnit_iff_ne_zero.2 (coeff_one_l_ne_zero hex0 h)) hex0 h

theorem l_ex_apply {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) (y : MvPowerSeries σ ℂ_[p])
    (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hy' := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hex hy' l, h, PowerSeries.subst_X hy']

theorem ex_l_apply {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) (y : MvPowerSeries σ ℂ_[p])
    (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y l) ex = y := by
  have hl := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_l hex0 h)
  have hy' := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hl hy' ex, subst_l_ex hex0 h, PowerSeries.subst_X hy']

theorem ident_holds : Ident := by
  intro p _ l ex hex0 h
  have hl0 := constantCoeff_l hex0 h
  refine ⟨hl0, fun σ a b ha hb => ?_⟩
  have hla : MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero ha l hl0
  have hlb : MvPowerSeries.constantCoeff (PowerSeries.subst b l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hb l hl0
  have hCa : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (MvPowerSeries.C c * PowerSeries.subst a l) = 0 :=
    fun c => by rw [map_mul, hla, mul_zero]
  have lmul : ∀ c : ℂ_[p], PowerSeries.subst (mulBy l ex c a) l = MvPowerSeries.C c * PowerSeries.subst a l :=
    fun c => l_ex_apply hex0 h _ (hCa c)
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, hla, hlb, add_zero]) ex hex0,
    fun c => PowerSeries.constantCoeff_subst_eq_zero (hCa c) ex hex0, ?_, ?_, fun c d => ?_, fun c => ?_, ?_, ?_⟩
  · unfold add; rw [add_comm]
  · unfold add mulBy; rw [map_ofNat, two_mul]
  · unfold add; rw [lmul, lmul, ← add_mul, ← map_add]; rfl
  · unfold add; rw [lmul]; unfold mulBy; rw [map_add, map_one, add_mul, one_mul]
  · unfold mulBy; rw [map_one, one_mul]; exact ex_l_apply hex0 h a ha
  · unfold mulBy; rw [map_zero, zero_mul]; exact PowerSeries.subst_zero_of_constantCoeff_zero hex0

end PI.BeDiagZp.IdentW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.CoeffPowMulPowEqZeroOfLt
section
noncomputable section

open Classical

namespace PI.BeDiagZp

open MvPowerSeries

namespace IntegralPowerSeriesBall

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

def ballSub (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem intMv_one : IntegralMv (1 : MvPowerSeries σ ℂ_[p]) := fun n => by
  rw [coeff_one]; split_ifs
  · exact (ballSub p).one_mem
  · exact (ballSub p).zero_mem

theorem intMv_inv {F : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (h1 : constantCoeff F = 1) :
    ∃ G : MvPowerSeries σ ℂ_[p], IntegralMv G ∧ F * G = 1 := by
  let F' : MvPowerSeries σ (ballSub p) := fun n => ⟨coeff n F, hF n⟩
  have hmap : map (ballSub p).subtype F' = F := by
    ext n; rw [coeff_map]; rfl
  have hc : constantCoeff F' = 1 := by
    apply Subtype.val_injective
    have := constantCoeff_map (ballSub p).subtype F'
    rw [hmap, h1] at this
    simpa using this.symm
  have hG' : F' * invOfUnit F' 1 = 1 := mul_invOfUnit F' 1 (by rw [hc, Units.val_one])
  refine ⟨map (ballSub p).subtype (invOfUnit F' 1), fun n => ?_, ?_⟩
  · rw [coeff_map]; exact (coeff n (invOfUnit F' 1)).2
  · rw [← hmap, ← map_mul, hG', map_one]

def expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • f ^ n

theorem coeff_expMv (f : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), coeff α (f ^ n) / (n.factorial : ℂ_[p]) := rfl

theorem coeff_expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) (α : σ →₀ ℕ) :
    coeff α (expT f N) = ∑ n ∈ Finset.range N, coeff α (f ^ n) / (n.factorial : ℂ_[p]) := by
  simp only [expT, map_sum, map_smul, smul_eq_mul, div_eq_inv_mul]

end IntegralPowerSeriesBall

open IntegralPowerSeriesBall

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem coeff_pow_eq_zero_of_lt {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {n : ℕ}
    {α : σ →₀ ℕ} (h : Finsupp.degree α < n) : coeff α (f ^ n) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (le_order_pow_of_constantCoeff_eq_zero n hf)

theorem coeff_pow_mul_pow_eq_zero_of_lt {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) {m j : ℕ} {α : σ →₀ ℕ} (h : Finsupp.degree α < m + j) :
    coeff α (x ^ m * y ^ j) = 0 := by
  apply coeff_of_lt_order
  calc ((Finsupp.degree α : ℕ) : ℕ∞) < ((m + j : ℕ) : ℕ∞) := by exact_mod_cast h
    _ = (m : ℕ∞) + (j : ℕ∞) := by push_cast; rfl
    _ ≤ (x ^ m).order + (y ^ j).order :=
        add_le_add (le_order_pow_of_constantCoeff_eq_zero m hx)
          (le_order_pow_of_constantCoeff_eq_zero j hy)
    _ ≤ (x ^ m * y ^ j).order := le_order_mul

theorem coeff_expMv_eq_expT {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {α : σ →₀ ℕ}
    {N : ℕ} (hN : Finsupp.degree α < N) : coeff α (expMv f) = coeff α (expT f N) := by
  rw [coeff_expMv, coeff_expT]
  apply Finset.sum_subset
  · intro n hn; simp only [Finset.mem_range] at *; omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [coeff_pow_eq_zero_of_lt hf (by omega), zero_div]

theorem inv_fact_mul_choose (n m : ℕ) (h : m ≤ n) :
    (n.factorial : ℂ_[p])⁻¹ * (n.choose m : ℂ_[p]) =
      (m.factorial : ℂ_[p])⁻¹ * ((n - m).factorial : ℂ_[p])⁻¹ := by
  have h1 := Nat.choose_mul_factorial_mul_factorial h
  have hn : (n.factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hm : (m.factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hk : ((n - m).factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (n.choose m : ℂ_[p]) * m.factorial * (n - m).factorial = n.factorial := by
    exact_mod_cast h1
  field_simp
  exact h2

theorem expT_add (x y : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    expT (x + y) N = ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range (N - m),
      (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)) := by
  rw [← Finset.sum_range_diag_flip N
    (fun m j => (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)))]
  unfold expT
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [add_pow, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  rw [← inv_fact_mul_choose n m hmn, mul_comm _ (n.choose m : ℂ_[p]), ← smul_smul,
    mul_comm _ ((n.choose m : ℕ) : MvPowerSeries σ ℂ_[p]), ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul]
  exact smul_comm _ _ _

theorem expT_mul_expT (x y : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    expT x N * expT y N = ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)) := by
  unfold expT
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm]

theorem coeff_expT_add {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) {α : σ →₀ ℕ} {N : ℕ} (hN : Finsupp.degree α < N) :
    coeff α (expT (x + y) N) = coeff α (expT x N * expT y N) := by
  rw [expT_add, expT_mul_expT, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_sum, map_sum]
  apply Finset.sum_subset
  · intro j hj; simp only [Finset.mem_range] at *; omega
  · intro j _ hj
    simp only [Finset.mem_range, not_lt] at hm hj
    rw [map_smul, coeff_pow_mul_pow_eq_zero_of_lt hx hy (by omega), smul_zero]

theorem expMv_add {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : expMv (x + y) = expMv x * expMv y := by
  ext α
  have hN : Finsupp.degree α < Finsupp.degree α + 1 := Nat.lt_succ_self _
  have hxy : constantCoeff (x + y) = 0 := by rw [map_add, hx, hy, add_zero]
  rw [coeff_expMv_eq_expT hxy hN, coeff_expT_add hx hy hN, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun βγ hβγ => ?_
  have hd : Finsupp.degree α = Finsupp.degree βγ.1 + Finsupp.degree βγ.2 := by
    rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hβγ]
  rw [coeff_expMv_eq_expT (N := Finsupp.degree α + 1) hx (by omega),
    coeff_expMv_eq_expT (N := Finsupp.degree α + 1) hy (by omega)]

theorem expMv_zero : expMv (0 : MvPowerSeries σ ℂ_[p]) = 1 := by
  ext α
  rw [coeff_expMv, Finset.sum_range_succ']
  simp

theorem constantCoeff_expMv (f : MvPowerSeries σ ℂ_[p]) : constantCoeff (expMv f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_expMv]
  simp

theorem integral_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := fun n => by
  rw [coeff_mul]
  exact (ballSub p).sum_mem fun x _ => (ballSub p).mul_mem (hF x.1) (hG x.2)

theorem integral_expMv_neg {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (h : IntegralMv (expMv x)) : IntegralMv (expMv (-x)) := by
  obtain ⟨G, hG, hG1⟩ := intMv_inv h (constantCoeff_expMv x)
  have hnx : constantCoeff (-x) = 0 := by rw [map_neg, hx, neg_zero]
  have hmul : expMv (-x) * expMv x = 1 := by rw [← expMv_add hnx hx, neg_add_cancel, expMv_zero]
  have : expMv (-x) = G := by
    calc expMv (-x) = expMv (-x) * (expMv x * G) := by rw [hG1, mul_one]
      _ = G := by rw [← mul_assoc, hmul, one_mul]
  rw [this]; exact hG

theorem simeq_refl (f : MvPowerSeries σ ℂ_[p]) : Simeq f f := by
  refine ⟨by rw [sub_self, map_zero], ?_⟩
  rw [sub_self, expMv_zero]; exact intMv_one

theorem simeq_symm {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f := by
  have e : g - f = -(f - g) := (neg_sub f g).symm
  refine ⟨by rw [e, map_neg, h.1, neg_zero], ?_⟩
  rw [e]; exact integral_expMv_neg h.1 h.2

theorem simeq_add {f g f' g' : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) (h' : Simeq f' g') :
    Simeq (f + f') (g + g') := by
  have e : f + f' - (g + g') = (f - g) + (f' - g') := add_sub_add_comm f f' g g'
  refine ⟨by rw [e, map_add, h.1, h'.1, add_zero], ?_⟩
  rw [e, expMv_add h.1 h'.1]; exact integral_mul h.2 h'.2

theorem simeq_trans {f g h : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq g h) :
    Simeq f h := by
  have e : f - h = (f - g) + (g - h) := (sub_add_sub_cancel f g h).symm
  refine ⟨by rw [e, map_add, h1.1, h2.1, add_zero], ?_⟩
  rw [e, expMv_add h1.1 h2.1]; exact integral_mul h1.2 h2.2

theorem simeq_equivalence_additive : S0 := fun _ _ _ f _ _ _ _ =>
  ⟨simeq_refl f, simeq_symm, simeq_trans, simeq_add⟩

end PI.BeDiagZp
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.ConstantCoeffSubstEqZero
section
noncomputable section

open Classical

namespace PI.BeDiagZp.ContPf

variable {p : ℕ} [Fact p.Prime]

def CC {σ : Type} (G : ℂ_[p] → MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, Continuous fun c => MvPowerSeries.coeff n (G c)

theorem cc_const {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : CC fun _ : ℂ_[p] => F :=
  fun _ => continuous_const

theorem cc_C {σ : Type} : CC fun c : ℂ_[p] => (MvPowerSeries.C c : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp only [MvPowerSeries.coeff_C]
  by_cases h : n = 0
  · simp only [h, if_true]; exact continuous_id
  · simp only [h, if_false]; exact continuous_const

theorem cc_add {σ : Type} {F G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (hG : CC G) :
    CC fun c => F c + G c := by
  intro n; simp only [map_add]; exact (hF n).add (hG n)

theorem cc_sub {σ : Type} {F G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (hG : CC G) :
    CC fun c => F c - G c := by
  intro n; simp only [map_sub]; exact (hF n).sub (hG n)

theorem cc_mul {σ : Type} {F G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (hG : CC G) :
    CC fun c => F c * G c := by
  intro n
  simp only [MvPowerSeries.coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hF x.1).mul (hG x.2)

theorem cc_pow {σ : Type} {F : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (k : ℕ) :
    CC fun c => F c ^ k := by
  induction k with
  | zero => simp only [pow_zero]; exact cc_const 1
  | succ k ih => simp only [pow_succ]; exact cc_mul ih hF

theorem coeff_pow_eq_zero {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (e : σ →₀ ℕ) (d : ℕ) (h : e.degree < d) : MvPowerSeries.coeff e (a ^ d) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d ha)

theorem coeff_subst_eq_sum {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (F : PowerSeries ℂ_[p]) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst a F) =
      ∑ d ∈ Finset.range (e.degree + 1), PowerSeries.coeff d F • MvPowerSeries.coeff e (a ^ d) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hd
  simp only [coeff_pow_eq_zero a ha e d (by omega), smul_zero]

theorem cc_subst {σ : Type} (F : PowerSeries ℂ_[p]) {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]}
    (h0 : ∀ c, MvPowerSeries.constantCoeff (G c) = 0) (hG : CC G) :
    CC fun c => PowerSeries.subst (G c) F := by
  intro e
  simp only [coeff_subst_eq_sum _ (h0 _)]
  exact continuous_finsetSum _ fun d _ => by
    have h : Continuous fun c => MvPowerSeries.coeff e (G c ^ d) := cc_pow hG d e
    exact h.const_smul (PowerSeries.coeff d F)

theorem cc_expMv {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hG : CC G) :
    CC fun c => expMv (G c) := by
  intro e
  show Continuous fun c => ∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (G c ^ n) / (n.factorial : ℂ_[p])
  exact continuous_finsetSum _ fun n _ => (cc_pow hG n e).div_const _

theorem constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (F : PowerSeries ℂ_[p]) (hF : PowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a F) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha F hF

theorem zc_continuous : Continuous (zc : ℤ_[p] → ℂ_[p]) := by
  unfold zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem zc_natCast (n : ℕ) : zc (n : ℤ_[p]) = (n : ℂ_[p]) := by
  simp [zc]

end PI.BeDiagZp.ContPf

namespace PI.BeDiagZp

open ContPf

theorem cont_holds : Cont := by
  intro p _ l ex ph hex hl hN n
  let u : MvPowerSeries Unit ℂ_[p] := Xv ()
  have hu : MvPowerSeries.constantCoeff u = 0 := by simp [u, Xv]
  have hlu : MvPowerSeries.constantCoeff (PowerSeries.subst u l) = 0 := constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution u hu l hl
  have hM0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (mulBy l ex c u) = 0 := by
    intro c
    apply constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ _ ex hex
    simp [hlu]
  have hM : CC fun c : ℂ_[p] => mulBy l ex c u := by
    apply cc_subst ex (fun c => by simp [hlu]) (cc_mul cc_C (cc_const _))
  have hA0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (add l ex u (mulBy l ex c u)) = 0 := by
    intro c
    apply constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ _ ex hex
    simp [hlu, constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hM0 c) l hl]
  have hA : CC fun c : ℂ_[p] => add l ex u (mulBy l ex c u) := by
    apply cc_subst ex (fun c => by simp [hlu, constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hM0 c) l hl])
    exact cc_add (cc_const _) (cc_subst l hM0 hM)
  have hB : CC fun c : ℂ_[p] => be l ex ph u (mulBy l ex c u) := by
    unfold be phAt
    exact cc_sub (cc_sub (cc_subst ph hA0 hA) (cc_const _)) (cc_subst ph hM0 hM)
  have hF : CC fun c : ℂ_[p] =>
      be l ex ph u (mulBy l ex c u) - MvPowerSeries.C c * be l ex ph u u :=
    cc_sub hB (cc_mul cc_C (cc_const _))
  have hE := cc_expMv hF
  have hcl : IsClosed {c : ℂ_[p] | Simeq (be l ex ph u (mulBy l ex c u))
      (MvPowerSeries.C c * be l ex ph u u)} := by
    simp only [Simeq, IntegralMv, IsIntP, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const)
      (isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hE α)) continuous_const)
    exact (hF 0).congr fun c => MvPowerSeries.coeff_zero_eq_constantCoeff_apply _
  have hcl' := hcl.preimage zc_continuous
  refine PadicInt.denseRange_natCast.induction_on n hcl' ?_
  intro k
  show Simeq _ _
  rw [zc_natCast]
  exact hN k

end PI.BeDiagZp
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOpsHolds
section
noncomputable section

open Classical

namespace PI.BeDiagZp.OpsW

variable {p : ℕ} [Fact p.Prime]

theorem psubst_comm {σ τ : Type} {s : σ → MvPowerSeries τ ℂ_[p]} (hs : MvPowerSeries.HasSubst s)
    (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst s (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst s a) f := by
  have h1 : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (a := fun _ : Unit => a) h1 hs f]

theorem substOps_holds : SubstOps := by
  intro p _ l ex ph hex hl σ τ _ s hs0
  have hs : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs0
  have cc : ∀ a : MvPowerSeries σ ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst s a) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero hs hs0 ha
  refine ⟨fun i => MvPowerSeries.subst_X hs i, fun c a => ?_, fun a b => MvPowerSeries.subst_add hs a b,
    fun a b ha hb => ?_⟩
  · rw [MvPowerSeries.subst_mul hs, MvPowerSeries.subst_C]
  · have hla : MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha l hl
    have hlb : MvPowerSeries.constantCoeff (PowerSeries.subst b l) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hb l hl
    have hab : MvPowerSeries.constantCoeff (add l ex a b) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, hla, hlb, add_zero]) ex hex
    have hadd : MvPowerSeries.subst s (add l ex a b) =
        add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
      unfold add
      rw [psubst_comm hs _ (by rw [map_add, hla, hlb, add_zero]) ex, MvPowerSeries.subst_add hs,
        psubst_comm hs a ha l, psubst_comm hs b hb l]
    refine ⟨cc a ha, hadd, fun c => ?_, psubst_comm hs a ha ph, ?_⟩
    · unfold mulBy
      rw [psubst_comm hs _ (by rw [map_mul, hla, mul_zero]) ex, MvPowerSeries.subst_mul hs,
        MvPowerSeries.subst_C, psubst_comm hs a ha l]
    · unfold be phAt
      rw [MvPowerSeries.subst_sub hs, MvPowerSeries.subst_sub hs, psubst_comm hs _ hab ph,
        psubst_comm hs a ha ph, psubst_comm hs b hb ph, hadd]

end PI.BeDiagZp.OpsW
end
end

