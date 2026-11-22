import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace SectionInjectivity

set_option linter.unusedSectionVars false

theorem isLive_of_mem_points {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦
  hc k (by simpa [evalCone] using hz.2 _ hk)

theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

theorem chartForm_cross {P : ArithVariety n} {num den : MvPolynomial (Coord n) ℤ}
    (hden : den ∉ P.ideal) {c : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ}
    {f f' : MvPolynomial (Coord n) ℤ} (h : den * f - num * chartMonomial c d ∈ P.ideal)
    (h' : den * f' - num * chartMonomial c d' ∈ P.ideal) :
    f * chartMonomial c d' - f' * chartMonomial c d ∈ P.ideal := by
  have hmul : den * (f * chartMonomial c d' - f' * chartMonomial c d) ∈ P.ideal := by
    have e : den * (f * chartMonomial c d' - f' * chartMonomial c d) =
        (den * f - num * chartMonomial c d) * chartMonomial c d' -
          (den * f' - num * chartMonomial c d') * chartMonomial c d := by ring
    rw [e]
    exact P.ideal.sub_mem (P.ideal.mul_mem_right _ h) (P.ideal.mul_mem_right _ h')
  exact (P.isPrime.mem_or_mem hmul).resolve_left hden

theorem chartForm_mul_pow {P : ArithVariety n} {num₁ den₁ num₂ den₂ : MvPolynomial (Coord n) ℤ}
    {c : (k : ι) → Fin (n k + 1)} {d₁ d₂ : ι → ℕ} {f₁ f₂ : MvPolynomial (Coord n) ℤ} (t : ℕ)
    (h₁ : den₁ * f₁ - num₁ * chartMonomial c d₁ ∈ P.ideal)
    (h₂ : den₂ * f₂ - num₂ * chartMonomial c d₂ ∈ P.ideal) :
    den₁ * den₂ ^ t * (f₁ * f₂ ^ t) - num₁ * num₂ ^ t * chartMonomial c (d₁ + t • d₂) ∈ P.ideal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h₁ h₂ ⊢
  rw [chartMonomial_add, chartMonomial_nsmul]
  simp only [map_mul, map_pow] at h₁ h₂ ⊢
  calc _ = (Ideal.Quotient.mk P.ideal den₁ * Ideal.Quotient.mk P.ideal f₁) *
        (Ideal.Quotient.mk P.ideal den₂ * Ideal.Quotient.mk P.ideal f₂) ^ t := by ring
    _ = _ := by rw [h₁, h₂]; ring

theorem deg_eq (M : HermLine n) {k q : ℕ} (hkq : k < q) (t : ℕ) :
    (((M.pow (q - k)).mul (HermLine.standard n)).pow t).deg +
        t • ((M.pow k).mul (HermLine.standard n).inv).deg = (M.pow (q * t)).deg := by
  ext i
  change (t • ((q - k) • M.deg + fun _ ↦ (1 : ℤ)) : ι → ℤ) i +
      (t • (k • M.deg + -fun _ ↦ (1 : ℤ)) : ι → ℤ) i = ((q * t) • M.deg : ι → ℤ) i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, nsmul_eq_mul, Nat.cast_sub hkq.le, Nat.cast_mul,
    Pi.mul_apply, Pi.sub_apply, Pi.natCast_apply]
  ring

theorem metric_eq (M : HermLine n) {k q : ℕ} (hkq : k < q) (t : ℕ) {z : Cone n ℂ}
    (hz : BlockNonzero z) :
    (M.pow (q * t)).metric z = (((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric z *
        ((M.pow k).mul (HermLine.standard n).inv).metric z ^ t := by
  have hH := ((HermLine.standard n).metric_pos z hz).ne'
  simp only [HermLine.pow, HermLine.mul, HermLine.inv]
  rw [← mul_pow, pow_mul]
  congr 1
  have hq : M.metric z ^ q = M.metric z ^ (q - k) * M.metric z ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkq.le]
  rw [hq]
  field_simp

end SectionInjectivity

open SectionInjectivity in

theorem SectionInjectivity.proof : SectionInjectivity.Statement := by
  intro ι _ _ n P M k q hkq e C he0 heC t
  refine ⟨fun s hs ↦ ?_, fun s₁ s₂ h ↦ mul_right_cancel₀ (pow_ne_zero t he0) h⟩
  refine ⟨IntegralSection.cast (deg_eq M hkq t) (s.mul (e.pow t)), ?_, ?_⟩
  · simp only [IntegralSection.toFun, IntegralSection.cast, IntegralSection.mul, IntegralSection.pow,
      map_mul, map_pow]
    rw [div_pow, mul_div_mul_comm]
  · intro z hz c d f hcf hzc
    have hlive := isLive_of_mem_points hz hzc
    obtain ⟨d₁, f₁, hcf₁⟩ := s.regular c hlive
    obtain ⟨d₂, f₂, hcf₂⟩ := e.regular c hlive
    have hs₁ := hs z hz c d₁ f₁ hcf₁ hzc
    have he₂ := heC z hz c d₂ f₂ hcf₂ hzc
    have hf : s.den * e.den ^ t * f - s.num * e.num ^ t * chartMonomial c d ∈ P.ideal := hcf.2
    have hprod := chartForm_mul_pow t hcf₁.2 hcf₂.2
    have hden : s.den * e.den ^ t ∉ P.ideal :=
      (IntegralSection.cast (deg_eq M hkq t) (s.mul (e.pow t))).den_not_mem
    have hev := hz.2 _ (chartForm_cross hden hf hprod)
    have hμ := evalCone_chartMonomial_ne_zero hzc d
    have hμ₁ := evalCone_chartMonomial_ne_zero hzc d₁
    have hμ₂ := evalCone_chartMonomial_ne_zero hzc d₂
    rw [chartMonomial_add, chartMonomial_nsmul] at hev
    simp only [evalCone, eval₂_sub, eval₂_mul, eval₂_pow] at hev hμ hμ₁ hμ₂ hs₁ he₂ ⊢
    rw [metric_eq M hkq t hz.1, Real.exp_zero]
    have hN := ((((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric_pos z hz.1)
    have hE := (((M.pow k).mul (HermLine.standard n).inv).metric_pos z hz.1)
    set x := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) f
    set x₁ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) f₁
    set x₂ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) f₂
    set μ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (chartMonomial c d)
    set μ₁ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (chartMonomial c d₁)
    set μ₂ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (chartMonomial c d₂)
    set hNz := (((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric z
    set hEz := ((M.pow k).mul (HermLine.standard n).inv).metric z
    have hnorm : ‖x‖ * (‖μ₁‖ * ‖μ₂‖ ^ t) = ‖x₁‖ * ‖x₂‖ ^ t * ‖μ‖ := by
      have h := congrArg norm (sub_eq_zero.mp hev)
      simpa only [norm_mul, norm_pow] using h
    have hμ' := norm_pos_iff.mpr hμ
    have hμ₁' := norm_pos_iff.mpr hμ₁
    have hμ₂' := norm_pos_iff.mpr hμ₂
    have key : ‖x‖ / (‖μ‖ * (hNz * hEz ^ t)) = ‖x₁‖ / (‖μ₁‖ * hNz) * (‖x₂‖ / (‖μ₂‖ * hEz)) ^ t := by
      rw [div_pow, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (hNz * hEz ^ t) * hnorm
    rw [key]
    calc ‖x₁‖ / (‖μ₁‖ * hNz) * (‖x₂‖ / (‖μ₂‖ * hEz)) ^ t
        ≤ Real.exp (-(t * C)) * Real.exp C ^ t :=
          mul_le_mul hs₁ (pow_le_pow_left₀ (by positivity) he₂ t) (by positivity) (by positivity)
      _ = 1 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartVanishing

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def evalHom {F : Type*} [CommRing F] (z : Cone n F) : MvPolynomial (Coord n) ℤ →+* F :=
  eval₂Hom (Int.castRingHom F) fun v : Coord n ↦ z v.1 v.2

omit [Fintype ι] [DecidableEq ι] in
theorem evalHom_apply {F : Type*} [CommRing F] (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    evalHom z f = evalCone z f := rfl

omit [Fintype ι] in

theorem mkF_X_ne_zero (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 :=
  fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)

theorem chartMonomial_mem_of_not_live (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)}
    (hc : ¬ P.IsLive c) {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  simp only [ArithVariety.IsLive, not_forall, not_not] at hc
  obtain ⟨k, hk⟩ := hc
  rw [chartMonomial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hk _ (hd k))

theorem exists_clear_denom (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (e : ℕ) (f : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ e = P.mkF f := by
  induction hu using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, X v * ∏ k ∈ Finset.univ.erase v.1, X ⟨k, c k⟩, ?_⟩
    have hne := mkF_X_ne_zero P hc v.1
    simp only [ArithVariety.chartCoord, chartMonomial, Pi.one_apply, pow_one, map_prod, map_mul]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v.1)]
    field_simp
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨e, f, hf⟩ := hx
    obtain ⟨e', f', hf'⟩ := hy
    refine ⟨e + e', f * chartMonomial c 1 ^ e' + f' * chartMonomial c 1 ^ e, ?_⟩
    simp only [map_add, map_mul, map_pow, ← hf, ← hf']
    ring
  | neg x _ hx =>
    obtain ⟨e, f, hf⟩ := hx
    refine ⟨e, -f, ?_⟩
    rw [map_neg, ← hf]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨e, f, hf⟩ := hx
    obtain ⟨e', f', hf'⟩ := hy
    refine ⟨e + e', f * f', ?_⟩
    rw [map_mul, ← hf, ← hf']
    ring

theorem exists_common_denom (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {m : ℕ} {u : Fin m → P.FunField} (hu : ∀ j, u j ∈ P.chartRing c) :
    ∃ (E : ℕ) (f : Fin m → MvPolynomial (Coord n) ℤ),
      ∀ j, u j * P.mkF (chartMonomial c 1) ^ E = P.mkF (f j) := by
  choose e f hf using fun j ↦ exists_clear_denom P hc (hu j)
  refine ⟨∑ j, e j, fun j ↦ f j * chartMonomial c 1 ^ (∑ i, e i - e j), fun j ↦ ?_⟩
  have hle : e j ≤ ∑ i, e i := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (e i)) (Finset.mem_univ j)
  rw [map_mul, map_pow, ← hf j, ← Nat.add_sub_cancel' hle, pow_add, Nat.add_sub_cancel_left]
  ring

theorem cross_mem_of_live {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {c c' : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (hc' : P.IsLive c')
    (j : Fin (D.size + 1)) :
    chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
  rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc, hg.value c' hc']
  ring

theorem mkF_chartMonomial_mul_chartPow {P : ArithVariety n} (D : AddBlockData P) {d : ι → ℕ}
    (hd : ∀ k, 0 ≤ (d k : ℤ) + D.deg k) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) :
    P.mkF (chartMonomial c d) * P.chartPow c D.deg =
      P.mkF (chartMonomial c fun k ↦ (d k + D.deg k).toNat) := by
  simp only [chartMonomial, ArithVariety.chartPow, map_prod, map_pow]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (mkF_X_ne_zero P hc k),
    Int.toNat_of_nonneg (hd k)]

omit [DecidableEq ι] in

theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hz : ∀ k, z k (c k) ≠ 0) (e : ι → ℕ) : evalCone z (chartMonomial c e) ≠ 0 := by
  rw [evalCone_chartMonomial]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hz k)

theorem exists_ne_zero_of_live {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) (hm : evalCone z (chartMonomial c d) ≠ 0) : ∃ j, evalCone z (g c j) ≠ 0 := by
  by_contra h0
  simp only [not_exists, not_not] at h0
  have hzc : ∀ k, z k (c k) ≠ 0 := by
    rw [evalCone_chartMonomial] at hm
    intro k
    have hk := Finset.prod_ne_zero_iff.mp hm k (Finset.mem_univ k)
    exact (pow_ne_zero_iff (by have := hg.pos k; omega)).mp hk
  obtain ⟨u, hu, hsum⟩ := D.generating c hc
  obtain ⟨E, f, hf⟩ := exists_common_denom P hc hu
  have hcp : P.chartPow c D.deg ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (mkF_X_ne_zero P hc k)
  have hsum' : ∑ j, u j * D.elt j = P.chartPow c D.deg := by
    rw [← one_mul (P.chartPow c D.deg), ← hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp
  set Q := chartMonomial c fun k ↦ (d k + D.deg k).toNat
  have hmem : ∑ j, f j * g c j - chartMonomial c 1 ^ E * Q ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_sum, map_mul, map_pow,
      ← mkF_chartMonomial_mul_chartPow D hg.nonneg hc, ← hsum', sub_eq_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, ← hf j, hg.value c hc j]
    ring
  have hv := hz.2 _ hmem
  rw [← evalHom_apply, map_sub, map_sum, map_mul, map_pow] at hv
  simp only [map_mul, evalHom_apply, h0, mul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero] at hv
  exact mul_ne_zero (pow_ne_zero _ (evalCone_chartMonomial_ne_zero hzc 1))
    (evalCone_chartMonomial_ne_zero hzc _) hv

theorem eq_zero_of_live {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) (hm : evalCone z (chartMonomial c d) = 0) (j : Fin (D.size + 1)) :
    evalCone z (g c j) = 0 := by
  have hex : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c' hc'z using hex
  have hlive : P.IsLive c' := fun k hk ↦ hc'z k (by
    have := hz.2 _ hk
    simpa [evalCone] using this)
  have hv := hz.2 _ (cross_mem_of_live hg hc hlive j)
  rw [← evalHom_apply, map_sub, map_mul, map_mul, evalHom_apply, evalHom_apply, evalHom_apply,
    evalHom_apply, hm, zero_mul, sub_zero] at hv
  exact (mul_eq_zero.mp hv).resolve_left (evalCone_chartMonomial_ne_zero hc'z d)

theorem proof : ChartVanishing.Statement := by
  intro ι _ _ n P D d g hg z hz c
  by_cases hc : P.IsLive c
  · constructor
    · intro h0
      by_contra hm
      obtain ⟨j, hj⟩ := exists_ne_zero_of_live hg hz hc hm
      exact hj (h0 j)
    · exact eq_zero_of_live hg hz hc
  · refine ⟨fun _ ↦ hz.2 _ (chartMonomial_mem_of_not_live P hc hg.pos), fun _ j ↦ ?_⟩
    rw [hg.dead c hc j, ← evalHom_apply, map_zero]

end ChartVanishing

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsFormOfMemChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartFormsAlt

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

theorem chartMonomial_add (c : (k : ι) → Fin (n k + 1)) (e e' : ι → ℕ) :
    chartMonomial c (e + e') = chartMonomial c e * chartMonomial c e' := by
  simp [chartMonomial, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq ι] in

theorem chartMonomial_zero (c : (k : ι) → Fin (n k + 1)) :
    chartMonomial c (0 : ι → ℕ) = 1 := by
  simp [chartMonomial]

theorem chartMonomial_single (c : (k : ι) → Fin (n k + 1)) (k : ι) :
    chartMonomial c (Pi.single k 1) = X ⟨k, c k⟩ := by
  rw [chartMonomial, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem mkF_chartMonomial (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (e : ι → ℕ) :
    P.mkF (chartMonomial c e) = ∏ k, P.mkF (X ⟨k, c k⟩) ^ e k := by
  simp [chartMonomial, map_prod, map_pow]

theorem exists_form_of_mem_chartRing (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1))
    (hc : P.IsLive c) {x : P.FunField} (hx : x ∈ P.chartRing c) :
    ∃ (F : MvPolynomial (Coord n) ℤ) (e : ι → ℕ), IsWeightedHomogeneous (coordDeg n) F e ∧
      x * P.mkF (chartMonomial c e) = P.mkF F := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hne : P.mkF (X ⟨v.1, c v.1⟩) ≠ 0 := fun h ↦ hc v.1 ((P.mkF_eq_zero_iff _).mp h)
    refine ⟨X v, Pi.single v.1 1, ?_, ?_⟩
    · have h := isWeightedHomogeneous_X (R := ℤ) (coordDeg n) v
      simpa [coordDeg] using h
    · rw [chartMonomial_single, ArithVariety.chartCoord, div_mul_cancel₀ _ hne]
  | zero => exact ⟨0, 0, isWeightedHomogeneous_zero _ _ _, by simp⟩
  | one => exact ⟨1, 0, isWeightedHomogeneous_one _ _, by simp [chartMonomial_zero]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨F, e, hF, hxF⟩ := ihx
    obtain ⟨F', e', hF', hyF⟩ := ihy
    refine ⟨F * chartMonomial c e' + F' * chartMonomial c e, e + e', ?_, ?_⟩
    · refine (hF.mul (isWeightedHomogeneous_chartMonomial c e')).add ?_
      rw [add_comm e e']
      exact hF'.mul (isWeightedHomogeneous_chartMonomial c e)
    · rw [chartMonomial_add, map_add, map_mul, map_mul, map_mul, ← hxF, ← hyF]
      ring
  | neg x _ ih =>
    obtain ⟨F, e, hF, hxF⟩ := ih
    exact ⟨-F, e, hF.neg, by rw [map_neg, ← hxF, neg_mul]⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨F, e, hF, hxF⟩ := ihx
    obtain ⟨F', e', hF', hyF⟩ := ihy
    refine ⟨F * F', e + e', hF.mul hF', ?_⟩
    rw [chartMonomial_add, map_mul, map_mul, ← hxF, ← hyF]
    ring

end ChartFormsAlt

open ChartFormsAlt in

theorem ChartFormsAlt.proof : ChartFormsAlt.Statement := by
  classical
  intro ι _ _ n P D
  have hrep : ∀ (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)),
      ∃ (F : MvPolynomial (Coord n) ℤ) (e : ι → ℕ), IsWeightedHomogeneous (coordDeg n) F e ∧
        (P.IsLive c → D.elt j / P.chartPow c D.deg * P.mkF (chartMonomial c e) = P.mkF F) := by
    intro c j
    by_cases hc : P.IsLive c
    · obtain ⟨F, e, hF, h⟩ := exists_form_of_mem_chartRing P c hc (D.chart_mem c hc j)
      exact ⟨F, e, hF, fun _ ↦ h⟩
    · exact ⟨0, 0, isWeightedHomogeneous_zero _ _ _, fun h ↦ absurd h hc⟩
  choose F e hF hFe using hrep
  refine ⟨fun k ↦ 1 + (∑ c, ∑ j, e c j k) + (-D.deg k).toNat, fun d hd ↦ ?_⟩
  have hle : ∀ c j k, e c j k ≤ ∑ c, ∑ j, e c j k := fun c j k ↦
    (Finset.single_le_sum (f := fun j ↦ e c j k) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun c ↦ ∑ j, e c j k) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c))
  have hdk : ∀ k, 1 + (∑ c, ∑ j, e c j k) + (-D.deg k).toNat ≤ d k := fun k ↦ hd k
  have ht : ∀ c j k, (e c j k : ℤ) ≤ d k + D.deg k := by
    intro c j k
    have h1 := hle c j k
    have h2 := hdk k
    omega
  have hnn : ∀ k, 0 ≤ (d k : ℤ) + D.deg k := by
    intro k
    have h2 := hdk k
    omega
  let t : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → ι → ℕ :=
    fun c j k ↦ ((d k : ℤ) + D.deg k - e c j k).toNat
  refine ⟨fun c j ↦ if P.IsLive c then F c j * chartMonomial c (t c j) else 0, ?_⟩
  refine ⟨fun k ↦ ?_, hnn, fun c j ↦ ?_, fun c hc j ↦ ?_, fun c hc j ↦ ?_⟩
  · have h2 := hdk k
    omega
  · refine ⟨fun k ↦ ((d k : ℤ) + D.deg k).toNat, ?_, fun k ↦ Int.toNat_of_nonneg (hnn k)⟩
    split_ifs with hc
    · have hd' : e c j + t c j = fun k ↦ ((d k : ℤ) + D.deg k).toNat := by
        funext k
        have h1 := ht c j k
        simp only [Pi.add_apply, t]
        omega
      rw [← hd']
      exact (hF c j).mul (isWeightedHomogeneous_chartMonomial c (t c j))
    · exact isWeightedHomogeneous_zero _ _ _
  · simp only [if_pos hc]
    have hy : ∀ k, P.mkF (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
    have hC : P.chartPow c D.deg ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hy k)
    have key : P.mkF (chartMonomial c (e c j)) * P.mkF (chartMonomial c (t c j)) =
        P.mkF (chartMonomial c d) * P.chartPow c D.deg := by
      rw [mkF_chartMonomial, mkF_chartMonomial, mkF_chartMonomial, ArithVariety.chartPow,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), ← zpow_add₀ (hy k)]
      congr 1
      have h1 := ht c j k
      simp only [t]
      omega
    rw [map_mul, ← hFe c j hc, mul_assoc, key]
    field_simp
  · simp [if_neg hc]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.AddBlockData

theorem ChartFormsAlt.equiv :
    _root_.GroundTheory.Heights₂.Heights.ChartFormsAlt.Statement ↔
      _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartFormsAlt.Statement := by
  constructor
  · intro hA ι _ _ n P D
    obtain ⟨d₀, hd₀⟩ := hA ι n P (toObjects D)
    refine ⟨d₀, fun d hd ↦ ?_⟩
    obtain ⟨g, hg⟩ := hd₀ d hd
    obtain ⟨G, hGd, -⟩ := (exists_chartForms_iff_isFormSystem D d g).2 hg
    exact ⟨G, hGd⟩
  · intro hB ι _ _ n P D
    obtain ⟨d₀, hd₀⟩ := hB ι n P (ofObjects D)
    refine ⟨d₀, fun d hd ↦ ?_⟩
    obtain ⟨G, hGd⟩ := hd₀ d hd
    exact ⟨G.g, (isFormSystem_iff_exists_chartForms D d G.g).2 ⟨G, hGd, rfl⟩⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem ChartPrimality.equiv :
    GroundTheory.Heights₂.Heights.ChartPrimality.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartPrimality.Statement := by
  constructor
  · intro hA ι _ _ n P D
    obtain ⟨Q, hQ⟩ := hA ι n P (AddBlockEq.split_model_to_place_model D)
    exact ⟨Q, hQ.trans (AddBlockEq.addBlockEquiv_symm_extIdeal D)⟩
  · intro hB ι _ _ n P D
    obtain ⟨Q, hQ⟩ := hB ι n P (AddBlockEq.toIndefiniteRowSideFullHecke D)
    exact ⟨Q, hQ.trans (AddBlockEq.addBlockEquiv_extIdeal D)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

