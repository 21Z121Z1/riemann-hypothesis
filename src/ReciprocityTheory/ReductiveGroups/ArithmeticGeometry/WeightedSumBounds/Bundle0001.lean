import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import ReciprocityTheory.DualLattices.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.EqZeroOfVecMulTmat
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def tmat (γ : Fin d → Fin d → PowerSeries C) : Matrix (Fin d) (Fin d) C :=
  Matrix.of fun a b => tangent (γ a) b

theorem sum_smul_tangent (γ : Fin d → Fin d → PowerSeries C) (x : Fin d → C) :
    ∑ b, x b • tangent (γ b) = Matrix.vecMul x (tmat γ) := by
  funext c
  simp [Matrix.vecMul, dotProduct, tmat, Finset.sum_apply]

theorem tmat_det_ne_zero {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0) :
    (tmat γ).det ≠ 0 := by
  intro h
  rw [h] at hdet
  simp at hdet

theorem tmat_isUnit_det {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0) :
    IsUnit (tmat γ).det := isUnit_iff_ne_zero.mpr (tmat_det_ne_zero hdet)

theorem isIntV_tmat_inv {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a))
    (hdet : v (tmat γ).det = 0) (i j : Fin d) : IsIntV v ((tmat γ)⁻¹ i j) := by
  let S : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
        exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }
  have hent : ∀ a b, tmat γ a b ∈ S := fun a b => by
    show 0 ≤ v (tmat γ a b)
    exact (hγ a b).2 1
  let M' : Matrix (Fin d) (Fin d) S := fun a b => ⟨tmat γ a b, hent a b⟩
  have hM : tmat γ = S.subtype.mapMatrix M' := by
    ext a b
    rfl
  have hadj : ∀ i j, (tmat γ).adjugate i j ∈ S := by
    intro i j
    rw [hM, ← RingHom.map_adjugate]
    first
    | exact (M'.adjugate i j).2
    | simp
  have hdet_inv : v ((tmat γ).det⁻¹) = 0 := by
    have h1 : v ((tmat γ).det⁻¹ * (tmat γ).det) = 0 := by
      rw [inv_mul_cancel₀ (tmat_det_ne_zero hdet), AddValuation.map_one]
    rwa [AddValuation.map_mul, hdet, add_zero] at h1
  show 0 ≤ v ((tmat γ)⁻¹ i j)
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, AddValuation.map_mul,
    hdet_inv, zero_add]
  exact hadj i j

theorem vecMul_inv_tmat {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0)
    (w : Fin d → C) : Matrix.vecMul (Matrix.vecMul w (tmat γ)⁻¹) (tmat γ) = w := by
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (tmat_isUnit_det hdet), Matrix.vecMul_one]

theorem eq_zero_of_vecMul_tmat {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0)
    {x : Fin d → C} (h : Matrix.vecMul x (tmat γ) = 0) : x = 0 := by
  have h2 := congrArg (fun w => Matrix.vecMul w (tmat γ)⁻¹) h
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (tmat_isUnit_det hdet),
    Matrix.vecMul_one, Matrix.zero_vecMul] at h2
  exact h2

theorem isIntV_vecMul_inv {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a))
    (hdet : v (tmat γ).det = 0) {w : Fin d → C} (hw : ∀ c, IsIntV v (w c)) (b : Fin d) :
    IsIntV v (Matrix.vecMul w (tmat γ)⁻¹ b) := by
  let S : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
        exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }
  have hmem : Matrix.vecMul w (tmat γ)⁻¹ b ∈ S := by
    simp only [Matrix.vecMul, dotProduct]
    exact S.sum_mem fun c _ => S.mul_mem (hw c) (isIntV_tmat_inv hγ hdet c b)
  exact hmem

theorem vecMul_tmat_support {h : ℕ} (ty : Fin d → ZMod h) {γ : Fin d → Fin d → PowerSeries C}
    (hdet : v (tmat γ).det = 0) (ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0)
    (x : Fin d → C) (τ : ZMod h) (hw : ∀ c, ty c ≠ τ → Matrix.vecMul x (tmat γ) c = 0) :
    ∀ b, ty b ≠ τ → x b = 0 := by
  intro b hb
  set x' : Fin d → C := fun b => if ty b ≠ τ then x b else 0 with hx'
  have hz : Matrix.vecMul x' (tmat γ) = 0 := by
    funext c
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hc : ty c = τ
    · apply Finset.sum_eq_zero
      intro b' _
      by_cases hb' : ty b' ≠ τ
      · have h0 : tangent (γ b') c = 0 := ht b' c (by rw [hc]; exact fun h => hb' h.symm)
        simp [hx', hb', tmat, h0]
      · simp [hx', hb']
    · have h0 := hw c hc
      simp only [Matrix.vecMul, dotProduct] at h0
      rw [← h0]
      apply Finset.sum_congr rfl
      intro b' _
      by_cases hb' : ty b' ≠ τ
      · simp [hx', hb']
      · have hb2 : ty b' = τ := not_not.mp hb'
        have h1 : tangent (γ b') c = 0 := ht b' c (by rw [hb2]; exact hc)
        simp [hx', hb', tmat, h1]
  have h3 := congrFun (eq_zero_of_vecMul_tmat hdet hz) b
  simpa [hx', hb] using h3

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement
section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open ReciprocityTheory.PGsh

noncomputable section

def OmAStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → 3 ≤ p → v (p : C) = 1 → ∀ (lg P : PowerSeries C) (Ω : C),
      PowerSeries.coeff 0 lg = 0 → PowerSeries.coeff 1 lg = 1 →
      (∀ z : C, z ^ (p ^ 2 - 1) = 1 → PowerSeries.rescale z lg = z • lg) →
      PsIsInt v P → PowerSeries.subst P lg = (p : C) • lg →
      PowerSeries.coeff 0 P = 0 → PowerSeries.coeff 1 P = p →
      (∀ n, 2 ≤ n → n < p ^ 2 → PowerSeries.coeff n P = 0) →
      v (PowerSeries.coeff (p ^ 2) P) = 0 →
      Ω ≠ 0 → PsIsInt v (expComp Ω lg) → v Ω ≤ ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) →
        v Ω = ((p / ((p : ℝ) ^ 2 - 1) : ℝ) : WithTop ℝ)

def OmBStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → 5 ≤ p → v (p : C) = 1 → ∀ (lg P : PowerSeries C) (Ω π : C),
      v π = (((1 : ℝ) / 2 : ℝ) : WithTop ℝ) →
      PowerSeries.coeff 0 lg = 0 → PowerSeries.coeff 1 lg = 1 →
      (∀ z : C, z ^ (p - 1) = 1 → PowerSeries.rescale z lg = z • lg) →
      PsIsInt v P → PowerSeries.subst P lg = π • lg →
      PowerSeries.coeff 0 P = 0 → PowerSeries.coeff 1 P = π →
      (∀ n, 2 ≤ n → n < p → PowerSeries.coeff n P = 0) →
      v (PowerSeries.coeff p P) = 0 →
      Ω ≠ 0 → PsIsInt v (expComp Ω lg) → v Ω ≤ ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) →
        v Ω = ((1 / (2 * ((p : ℝ) - 1)) : ℝ) : WithTop ℝ)

def OmCStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (lg : PowerSeries C) (Ω x₁ ζ : C),
      PowerSeries.coeff 0 lg = 0 → PowerSeries.coeff 1 lg = 1 →
      Ω ≠ 0 → PsIsInt v (expComp Ω lg) →
      v x₁ = ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) → IsPrimitiveRoot ζ p →
      (∀ N : ℕ, 1 ≤ N → ((N / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) ≤
        v (ζ - ∑ n ∈ Finset.range N, PowerSeries.coeff n (expComp Ω lg) * x₁ ^ n)) →
        v Ω = 0

def OmStatement : Prop := OmAStatement ∧ OmBStatement ∧ OmCStatement

private theorem key {C : Type} [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (lg P : PowerSeries C) (Ω b : C) (M : ℕ) (hM : 2 ≤ M) (β φ r : ℝ) (hβ : 0 < β)
    (hb : v b = β) (hfac : v (M.factorial : C) = φ) (hr : v Ω = r) (hrβ : r < β)
    (hl0 : PowerSeries.coeff 0 lg = 0) (hl1 : PowerSeries.coeff 1 lg = 1)
    (hlg : ∀ j, 2 ≤ j → j < M → PowerSeries.coeff j lg = 0)
    (hsub : PowerSeries.subst P lg = b • lg) (hP0 : PowerSeries.coeff 0 P = 0)
    (hP1 : PowerSeries.coeff 1 P = b) (hPg : ∀ j, 2 ≤ j → j < M → PowerSeries.coeff j P = 0)
    (hu : v (PowerSeries.coeff M P) = 0) (hint : PsIsInt v (expComp Ω lg)) :
    r - β = M * r - φ := by
  have hc := PowerSeriesCoeffGaps.coeff_subst_gap lg P M hM b hl0 hl1 hlg hP0 hP1 hPg
  rw [hsub, PowerSeries.coeff_smul, smul_eq_mul] at hc
  have hu' : PowerSeries.coeff M P = PowerSeries.coeff M lg * (b + -b ^ M) := by
    linear_combination -hc
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hvb : v (-b ^ M) = ((M * β : ℝ) : WithTop ℝ) := by
    rw [v.map_neg, v.map_pow, hb, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hd : v (b + -b ^ M) = β := PowerSeriesCoeffGaps.add_eq_of_lt v hb hvb (by nlinarith)
  have hk0 : PowerSeries.coeff M lg ≠ 0 := by
    intro h0
    rw [hu', h0, zero_mul, v.map_zero] at hu
    exact WithTop.top_ne_zero hu
  obtain ⟨s, hs⟩ := PowerSeriesCoeffGaps.exists_real v hk0
  have hs' : s = -β := by
    rw [hu', v.map_mul, hs, hd, ← WithTop.coe_add] at hu
    have := WithTop.coe_eq_zero.mp hu
    linarith
  have hI := hint M
  unfold IsIntV at hI
  rw [PowerSeriesCoeffGaps.coeff_expComp_gap Ω lg M hM hl0 hl1 hlg] at hI
  have hx : v (Ω * PowerSeries.coeff M lg) = ((r + -β : ℝ) : WithTop ℝ) := by
    rw [v.map_mul, hr, hs, hs', WithTop.coe_add]
  have hy : v (Ω ^ M / (M.factorial : C)) = ((M * r - φ : ℝ) : WithTop ℝ) :=
    PowerSeriesCoeffGaps.div_eq_coe v (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M))
      (by rw [v.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]) hfac
  have := PowerSeriesCoeffGaps.eq_of_nonneg_add v (by linarith) hx hy hI
  linarith

theorem omA : OmAStatement := by
  intro C _ _ _ v p hp hp3 hp1 lg P Ω hl0 hl1 hsym _ hsub hP0 hP1 hPg hu hΩ hint hle
  have hM : 2 ≤ p ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) p)
  have hp1' : v (p : C) = ((1 : ℝ) : WithTop ℝ) := by rw [hp1, WithTop.coe_one]
  obtain ⟨r, hr⟩ := PowerSeriesCoeffGaps.exists_real v hΩ
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hrle : r ≤ 1 / ((p : ℝ) - 1) := by rw [hr] at hle; exact_mod_cast hle
  have hlt1 : 1 / ((p : ℝ) - 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hfac : v (((p ^ 2).factorial : ℕ) : C) = (((p + 1 : ℕ) : ℝ) : WithTop ℝ) := by
    rw [PowerSeriesCoeffGaps.natCast_eq_factorization v hp hp1 (Nat.factorial_ne_zero _),
      PowerSeriesCoeffGaps.factorization_factorial_sq hp]
  have e := key v lg P Ω (p : C) (p ^ 2) hM 1 ((p + 1 : ℕ) : ℝ) r one_pos hp1' hfac hr
    (by linarith) hl0 hl1 (PowerSeriesCoeffGaps.coeff_eq_zero_of_symm lg (p ^ 2) hM hsym) hsub hP0 hP1 hPg hu hint
  rw [hr]
  congr 1
  push_cast at e
  rw [eq_div_iff (ne_of_gt (by nlinarith))]
  linear_combination -e

theorem omB : OmBStatement := by
  intro C _ _ _ v p hp hp5 hp1 lg P Ω π hπ hl0 hl1 hsym _ hsub hP0 hP1 hPg hu hΩ hint hle
  have hM : 2 ≤ p := hp.two_le
  obtain ⟨r, hr⟩ := PowerSeriesCoeffGaps.exists_real v hΩ
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hrle : r ≤ 1 / ((p : ℝ) - 1) := by rw [hr] at hle; exact_mod_cast hle
  have hlt : 1 / ((p : ℝ) - 1) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hfac : v ((p.factorial : ℕ) : C) = (((1 : ℕ) : ℝ) : WithTop ℝ) := by
    rw [PowerSeriesCoeffGaps.natCast_eq_factorization v hp hp1 (Nat.factorial_ne_zero _),
      PowerSeriesCoeffGaps.factorization_factorial_self hp]
  have e := key v lg P Ω π p hM (1 / 2) ((1 : ℕ) : ℝ) r (by norm_num) hπ hfac hr (by linarith)
    hl0 hl1 (PowerSeriesCoeffGaps.coeff_eq_zero_of_symm lg p hM hsym) hsub hP0 hP1 hPg hu hint
  rw [hr]
  congr 1
  push_cast at e
  rw [eq_div_iff (ne_of_gt (by linarith))]
  linear_combination -2 * e

theorem omC : OmCStatement := by
  intro C _ _ _ v p hp hp1 lg Ω x₁ ζ hl0 hl1 hΩ _ hx hζ hN
  have h2 := hN 2 (by norm_num)
  have hc0 : PowerSeries.coeff 0 (expComp Ω lg) = 1 := by
    simp [expComp, PowerSeries.coeff_mk]
  have hc1 : PowerSeries.coeff 1 (expComp Ω lg) = Ω := by
    rw [expComp, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_range_one]
    simp [hl1]
  rw [Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1, pow_zero, pow_one, mul_one] at h2
  have hz := PowerSeriesCoeffGaps.v_zeta_sub_one v hp hp1 hζ
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlt : ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) < v (ζ - (1 + Ω * x₁)) := by
    refine lt_of_lt_of_le ?_ h2
    have h12 : 1 / ((p : ℝ) - 1) < ((2 : ℕ) : ℝ) / ((p : ℝ) - 1) := by
      rw [div_lt_div_iff_of_pos_right (by linarith)]; norm_num
    exact WithTop.coe_lt_coe.mpr h12
  have e : Ω * x₁ = (ζ - 1) + -(ζ - (1 + Ω * x₁)) := by ring
  have hd : v (ζ - 1) ≠ v (-(ζ - (1 + Ω * x₁))) := by rw [v.map_neg, hz]; exact hlt.ne
  have hv : v (Ω * x₁) = ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) := by
    rw [e, v.map_add_of_distinct_val hd, hz, v.map_neg, min_eq_left hlt.le]
  obtain ⟨r, hr⟩ := PowerSeriesCoeffGaps.exists_real v hΩ
  rw [v.map_mul, hr, hx, ← WithTop.coe_add] at hv
  have h3 := WithTop.coe_injective hv
  have h4 : r = 0 := by linarith
  rw [hr, h4, WithTop.coe_zero]

theorem om : OmStatement := ⟨omA, omB, omC⟩

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

