import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AesmIteratedDerivReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0010
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernelStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_additive_character_kernel : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → IsOpen {x : k | ψ x = 1} := by
  first | exact @GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | exact GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | (intros; apply GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivEqOfEqOnRealSegmentStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment : ∀ (f g : ℂ → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ f (Metric.ball 0 ρ) → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ s : ℝ, |s| < ρ → f s = g s) → ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0 := by
  first | exact @GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | exact GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | (intros; apply GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivIntegralGaussianExponential
section
open MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.HolMean.DilatedGaussian

lemma integrable_gauss_complex :
    Integrable (fun w : ℂ => Real.exp (-Real.pi * ‖w‖ ^ 2)) := by
  have hb : 0 < ((Real.pi : ℂ)).re := by simpa using Real.pi_pos
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, Complex.norm_exp]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma integrable_gauss (m n : ℕ) :
    Integrable (fun v : Fin m → Fin n → ℂ =>
      Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by
  have h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-Real.pi * ‖u j‖ ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin n) (w : ℂ) => Real.exp (-Real.pi * ‖w‖ ^ 2))
      (μ := fun _ => volume) (fun _ => integrable_gauss_complex)
  have h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-Real.pi * ‖v a j‖ ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin m) (u : Fin n → ℂ) => ∏ j, Real.exp (-Real.pi * ‖u j‖ ^ 2))
      (μ := fun _ => volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum]

noncomputable def dilated (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
    Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

lemma differentiable_dilated (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) :
    Differentiable ℂ (dilated m n X v) := by
  unfold dilated
  fun_prop

lemma continuous_dilated (m n : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    Continuous (fun v : Fin m → Fin n → ℂ => dilated m n X v z) := by
  unfold dilated
  first
  | fun_prop
  | exact continuous_const.mul (Continuous.cexp (continuous_const.mul
      (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun j _ => continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_norm.comp ((continuous_apply j).comp (continuous_apply a))).pow 2)))))

lemma eventually_small (m n : ℕ) (X : Fin n → ℝ) :
    ∀ᶠ z : ℂ in 𝓝 0, (∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re) ∧
      ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
  have hre : ∀ j, ∀ᶠ z : ℂ in 𝓝 0, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re := by
    intro j
    have hc : Continuous fun z : ℂ => (Complex.exp (2 * z * X j)).re := by fun_prop
    have h0 : (1 / 2 : ℝ) < (Complex.exp (2 * 0 * X j)).re := by norm_num
    exact ((hc.tendsto 0).eventually (lt_mem_nhds h0)).mono fun z hz => hz.le
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
    have hc : Continuous fun z : ℂ => ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ := by fun_prop
    have h0 : ‖Complex.exp ((m : ℂ) * 0 * ∑ j, (X j : ℂ))‖ < 2 := by norm_num
    exact ((hc.tendsto 0).eventually (gt_mem_nhds h0)).mono fun z hz => hz.le
  exact (Filter.eventually_all.2 hre).and hn

lemma norm_dilated_le (m n : ℕ) (X : Fin n → ℝ) (z : ℂ)
    (h1 : ∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re)
    (h2 : ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2) (v : Fin m → Fin n → ℂ) :
    ‖dilated m n X v z‖ ≤ 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  unfold dilated
  rw [norm_mul]
  have hre : (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)).re
      = -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 := by
    have e : (-(2 * Real.pi : ℂ)) = ((-(2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [Complex.re_sum, Complex.re_mul_ofReal]
  have hS : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 ≤
      ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (h1 j) (sq_nonneg _)
  have hT : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 = (1 / 2) * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    simp only [Finset.mul_sum]
  have key : -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 ≤
      -Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    rw [hT] at hS
    nlinarith [Real.pi_pos]
  refine mul_le_mul h2 ?_ (norm_nonneg _) (by norm_num)
  rw [Complex.norm_exp, hre]
  exact Real.exp_le_exp.2 key

theorem holomorphic_integral (m n : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ)
    (hK : Continuous K) (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) (Metric.ball 0 ρ) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = ∫ v, K v * iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  have hcm : ∀ (c : ℂ) (f : ℂ → ℂ) (r : ℕ),
      iteratedDeriv r (fun w => c * f w) = fun w => c * iteratedDeriv r f w := by
    intro c f r
    induction r with
    | zero => simp only [iteratedDeriv_zero]
    | succ r ih => rw [iteratedDeriv_succ, ih, deriv_const_mul_field', iteratedDeriv_succ]
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_small m n X)
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have hd : ∀ v : Fin m → Fin n → ℂ,
      DifferentiableOn ℂ (fun z => K v * dilated m n X v z) (Metric.ball (0 : ℂ) ρ) :=
    fun v => ((differentiable_dilated m n X v).const_mul (K v)).differentiableOn
  have hm : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      AEStronglyMeasurable (fun v : Fin m → Fin n → ℂ => K v * dilated m n X v z) volume :=
    fun z _ => (hK.mul (continuous_dilated m n X z)).aestronglyMeasurable
  have hb : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ 𝓝 z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v,
        ‖K v * dilated m n X v z‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem,
      fun v => 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2),
      (integrable_gauss m n).const_mul 2, ?_⟩
    intro z hz v
    obtain ⟨h1, h2⟩ := hsmall z hz.2
    rw [norm_mul]
    calc ‖K v‖ * ‖dilated m n X v z‖
        ≤ 1 * (2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) :=
          mul_le_mul (hK1 v) (norm_dilated_le m n X z h1 h2 v) (norm_nonneg _) zero_le_one
      _ = 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := one_mul _
  have hstep := integral_step (μ := volume) hU (fun z v => K v * dilated m n X v z) hd hm hb
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro z hz
    exact (hstep.1 z hz).differentiableAt.differentiableWithinAt
  · intro r
    have h := iteratedDeriv_integral (μ := volume) hU r (fun z v => K v * dilated m n X v z)
      hd hm hb 0 (Metric.mem_ball_self hρ)
    refine h.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    exact congrFun (hcm (K v) _ r) 0

end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriBlockUpperLeviLower
section
open Matrix

namespace GlobalTheory.CompanionTheory.BlockIwahoriUML

variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]

def Cong (v : Valuation k Γ) (r : Γ) {n : ℕ} (A : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i j, v (A i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r

theorem exists_udl (v : Valuation k Γ) {r : Γ} (hr : r < 1) (n : ℕ)
    (g : Matrix (Fin n) (Fin n) k) (hg : Cong v r g) :
    ∃ u d l : Matrix (Fin n) (Fin n) k, Cong v r u ∧ Cong v r l ∧
      (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧ (∀ i j, i ≠ j → d i j = 0) ∧
      (∀ i j, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧ g = u * d * l := by
  classical
  let I : Ideal v.integer :=
    { carrier := {x | v (x : k) ≤ r}
      add_mem' := fun {a b} ha hb => by
        have := Valuation.map_add_le v ha hb
        simpa using this
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have hc : v (c : k) ≤ 1 := c.2
        have hx' : v (x : k) ≤ r := hx
        show v ((c * x : v.integer) : k) ≤ r
        rw [Subring.coe_mul, map_mul]
        calc v (c : k) * v (x : k) ≤ 1 * r := mul_le_mul' hc hx'
          _ = r := one_mul r }
  have hImem : ∀ x : v.integer, x ∈ I ↔ v (x : k) ≤ r := fun x => Iff.rfl
  have hI : ∀ x ∈ I, IsUnit (1 + x) := by
    intro x hx
    have hx' : v (x : k) < 1 := lt_of_le_of_lt ((hImem x).1 hx) hr
    have h1 : v (1 + (x : k)) = 1 := Valuation.map_one_add_of_lt v hx'
    have h0 : (1 + (x : k)) ≠ 0 := by
      intro h
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    have hmem : (1 + (x : k))⁻¹ ∈ v.integer := by
      show v _ ≤ 1
      rw [map_inv₀, h1, inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨(1 + (x : k))⁻¹, hmem⟩, Subtype.ext ?_⟩
    simpa using mul_inv_cancel₀ h0
  have hone : ∀ i j, v ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hint : ∀ i j, v (g i j) ≤ 1 := by
    intro i j
    have := Valuation.map_add_le v ((hg i j).trans hr.le) (hone i j)
    simpa using this
  let g' : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨g i j, hint i j⟩
  have hone' : ∀ i j, (((1 : Matrix (Fin n) (Fin n) v.integer) i j : v.integer) : k) =
      (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hg' : ∀ i j, g' i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j ∈ I := by
    intro i j
    rw [hImem, AddSubgroupClass.coe_sub, hone']
    exact hg i j
  obtain ⟨u, d, l, hu, hd, hl, h⟩ := IwahoriUDL.exists_udl_of_isUnit I hI n g' hg'
  have back : ∀ a : Matrix (Fin n) (Fin n) v.integer,
      (∀ i j, a i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j ∈ I) →
        Cong v r (a.map v.integer.subtype) := by
    intro a ha i j
    have := (hImem _).1 (ha i j)
    rw [AddSubgroupClass.coe_sub, hone'] at this
    exact this
  refine ⟨u.map v.integer.subtype, d.map v.integer.subtype, l.map v.integer.subtype,
    back u hu.1, back l hl.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp [hu.2.1 i j hij]
  · intro i
    simp [hu.2.2 i]
  · intro i j hij
    simp [hd.2 i j hij]
  · intro i j hij
    simp [hl.2.1 i j hij]
  · intro i
    simp [hl.2.2 i]
  · have hgg : g = g'.map v.integer.subtype := by
      ext i j
      rfl
    rw [hgg, h, Matrix.map_mul, Matrix.map_mul]

theorem up_split (v : Valuation k Γ) {r : Γ} (hr : r < 1) {n : ℕ} (β : Fin n → ℕ)
    (hβ : Monotone β) (u : Matrix (Fin n) (Fin n) k) (hu : Cong v r u)
    (hu0 : ∀ i j, j < i → u i j = 0) (hu1 : ∀ i, u i i = 1) :
    ∃ a m : Matrix (Fin n) (Fin n) k, a.det = 1 ∧ m.det = 1 ∧ Cong v r a ∧ Cong v r m ∧
      (∀ i j, β j ≤ β i → a i j = (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      (∀ i j, β i ≠ β j → m i j = 0) ∧ u = a * m := by
  classical
  let m : Matrix (Fin n) (Fin n) k := fun i j => if β i = β j then u i j else 0
  have hmb : ∀ i j, β i ≠ β j → m i j = 0 := fun i j h => if_neg h
  have hmu : ∀ i j, β i = β j → m i j = u i j := fun i j h => if_pos h
  have hm0 : ∀ i j, j < i → m i j = 0 := by
    intro i j h
    by_cases hb : β i = β j
    · rw [hmu i j hb, hu0 i j h]
    · exact hmb i j hb
  have hm1 : ∀ i, m i i = 1 := fun i => by rw [hmu i i rfl, hu1]
  have hdet : ∀ A : Matrix (Fin n) (Fin n) k, (∀ i j, j < i → A i j = 0) → (∀ i, A i i = 1) →
      A.det = 1 := by
    intro A h0 h1
    rw [Matrix.det_of_upperTriangular (fun i j h => h0 i j h)]
    simp [h1]
  have hmd : m.det = 1 := hdet m hm0 hm1
  have hud : u.det = 1 := hdet u hu0 hu1
  have hmC : Cong v r m := by
    intro i j
    by_cases hb : β i = β j
    · rw [hmu i j hb]
      exact hu i j
    · have hij : i ≠ j := fun e => hb (by rw [e])
      rw [hmb i j hb, Matrix.one_apply_ne hij]
      simp
  have hmU : IsUnit m.det := by simp [hmd]
  have huU : IsUnit u.det := by simp [hud]
  haveI : Invertible m := Matrix.invertibleOfIsUnitDet m hmU
  have hmw : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv m hmU
  have hwm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hmU
  have hbu : BlockTriangular u β := by
    intro i j h
    refine hu0 i j ?_
    by_contra hc
    exact absurd (hβ (not_lt.1 hc)) (not_le.2 h)
  have hbm : BlockTriangular m β := fun i j h => hmb i j h.ne'
  have hbw : BlockTriangular m⁻¹ β := Matrix.blockTriangular_inv_of_blockTriangular hbm
  have hK : Cong v r (u * m⁻¹) := by
    let ug : GL (Fin n) k := Matrix.nonsingInvUnit u huU
    let mg : GL (Fin n) k := Matrix.nonsingInvUnit m hmU
    have hugK : ug ∈ PrincipalCongruence.principalCongruence v r hr := hu
    have hmgK : mg ∈ PrincipalCongruence.principalCongruence v r hr := hmC
    have hag := mul_mem hugK (inv_mem hmgK)
    have hcoe : ((ug * mg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = u * m⁻¹ := by
      rw [Units.val_mul, Matrix.coe_units_inv]
      rfl
    intro i j
    have := hag i j
    rwa [hcoe] at this
  refine ⟨u * m⁻¹, m, ?_, hmd, hK, hmC, ?_, hmb, ?_⟩
  · rw [Matrix.det_mul, hud, Matrix.det_nonsing_inv, hmd]
    simp
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · have hne : i ≠ j := fun e => h.ne (by rw [e])
      rw [Matrix.one_apply_ne hne]
      exact (hbu.mul hbw) h
    · have key : (u * m⁻¹) i j = (m * m⁻¹) i j := by
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rcases lt_trichotomy (β x) (β i) with hx | hx | hx
        · rw [hbu hx, hbm hx]
        · rw [hmu i x hx.symm]
        · have : m⁻¹ x j = 0 := hbw (by rw [h]; exact hx)
          rw [this, mul_zero, mul_zero]
      rw [key, hmw]
  · rw [Matrix.mul_assoc, hwm, Matrix.mul_one]

theorem cong_transpose (v : Valuation k Γ) {r : Γ} {n : ℕ} {A : Matrix (Fin n) (Fin n) k}
    (hA : Cong v r A) : Cong v r Aᵀ := by
  intro i j
  have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = (1 : Matrix (Fin n) (Fin n) k) j i := by
    simp [Matrix.one_apply, eq_comm]
  rw [h1, Matrix.transpose_apply]
  exact hA j i

theorem units_conj {M : Type*} [Monoid M] (p q : Mˣ) (x : M) :
    ((p⁻¹ : Mˣ) : M) * ((p : M) * x * (q : M)) * ((q⁻¹ : Mˣ) : M) = x := by
  simp [mul_assoc]

theorem blockDiag_mul {n : ℕ} (β : Fin n → ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) (hB : ∀ i j, β i ≠ β j → B i j = 0) :
    ∀ i j, β i ≠ β j → (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : β i = β x
  · rw [hB x j (fun e => hij (hx.trans e)), mul_zero]
  · rw [hA i x hx, zero_mul]

theorem factor (v : Valuation k Γ) {r : Γ} (hr : r < 1) {n : ℕ} (β : Fin n → ℕ)
    (hβ : Monotone β) (g : GL (Fin n) k) (hg : Cong v r (g : Matrix (Fin n) (Fin n) k)) :
    ∃ nm : GL (Fin n) k, Cong v r (nm : Matrix (Fin n) (Fin n) k) ∧
    ∃ l : GL (Fin n) k, Cong v r (l : Matrix (Fin n) (Fin n) k) ∧
    ∃ np : GL (Fin n) k, Cong v r (np : Matrix (Fin n) (Fin n) k) ∧
      (∀ i j, β i ≤ β j → (nm : Matrix (Fin n) (Fin n) k) i j =
        (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      (∀ i j, β i ≠ β j → (l : Matrix (Fin n) (Fin n) k) i j = 0) ∧
      (∀ i j, β j ≤ β i → (np : Matrix (Fin n) (Fin n) k) i j =
        (1 : Matrix (Fin n) (Fin n) k) i j) ∧ g = np * l * nm := by
  classical
  obtain ⟨u, d, t, hu, ht, hu0, hu1, hd0, ht0, ht1, hudt⟩ := exists_udl v hr n _ hg
  obtain ⟨a, m, had, hmd, haC, hmC, hab, hmb, huam⟩ := up_split v hr β hβ u hu hu0 hu1
  have htC : Cong v r tᵀ := cong_transpose v ht
  obtain ⟨b, c, hbd, hcd, hbC, hcC, hbb, hcb, htbc⟩ :=
    up_split v hr β hβ tᵀ htC (fun i j h => ht0 j i h) ht1
  have htt : t = cᵀ * bᵀ := by
    rw [← Matrix.transpose_mul, ← htbc, Matrix.transpose_transpose]
  have hbtC : Cong v r bᵀ := cong_transpose v hbC
  let npg : GL (Fin n) k := Matrix.nonsingInvUnit a (by simp [had])
  let nmg : GL (Fin n) k := Matrix.nonsingInvUnit bᵀ (by simp [hbd])
  have hnpK : npg ∈ PrincipalCongruence.principalCongruence v r hr := haC
  have hnmK : nmg ∈ PrincipalCongruence.principalCongruence v r hr := hbtC
  have hgK : g ∈ PrincipalCongruence.principalCongruence v r hr := hg
  have hlK := mul_mem (mul_mem (inv_mem hnpK) hgK) (inv_mem hnmK)
  have hprod : (g : Matrix (Fin n) (Fin n) k) =
      (npg : Matrix (Fin n) (Fin n) k) * (m * d * cᵀ) * (nmg : Matrix (Fin n) (Fin n) k) := by
    show (g : Matrix (Fin n) (Fin n) k) = a * (m * d * cᵀ) * bᵀ
    rw [hudt, huam, htt]
    simp only [Matrix.mul_assoc]
  have hlev : ((npg⁻¹ * g * nmg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = m * d * cᵀ := by
    rw [Units.val_mul, Units.val_mul, hprod]
    exact units_conj npg nmg _
  refine ⟨nmg, hnmK, npg⁻¹ * g * nmg⁻¹, hlK, npg, hnpK, ?_, ?_, hab, by group⟩
  · intro i j hij
    show bᵀ i j = _
    rw [Matrix.transpose_apply, hbb j i hij, ← Matrix.transpose_apply (1 : Matrix (Fin n) (Fin n) k) j i, Matrix.transpose_one]
  · rw [hlev]
    refine blockDiag_mul β (blockDiag_mul β hmb ?_) ?_
    · intro i j hij
      exact hd0 i j (fun e => hij (by rw [e]))
    · intro i j hij
      exact hcb j i hij.symm

theorem iwahori_block_upper_levi_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (β : Fin N → ℕ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 → (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Monotone β → ∀ g ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ nm ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ l ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ np ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, (∀ i j, β i ≤ β j → (nm : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ (∀ i j, β i ≠ β j → (l : Matrix (Fin N) (Fin N) k) i j = 0) ∧ (∀ i j, β j ≤ β i → (np : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ g = np * l * nm := by
  intro k _ _ _ _ N ϖ m β _ hϖ _ hm hβ g hg
  have hr : ValuativeRel.valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' hϖ (by omega)
  exact factor (ValuativeRel.valuation k) hr β hβ g hg

end GlobalTheory.CompanionTheory.BlockIwahoriUML
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
section
noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

def gW (d : ℕ) (α : Type) [Fintype α] (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2))

def zeroCnt {X : Type} (d : ℕ) {α : Type} [Fintype α] (A : Set X) (b : α → X → ℂ)
    (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  (({z ∈ A | ∀ k, ∑ j, C k j * b j z = 0}.encard : ℕ∞) : ℝ≥0∞)

def fsLevi {β : Type} [Fintype β] {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a c =>
    (((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) * ∑ j, F j a * conj (F j c) -
        (∑ j, F j a * conj (f j)) * ∑ j, f j * conj (F j c)) /
      ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) ^ 2

def joinCol {d : ℕ} {α : Type} [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) : Fin d → α → ℂ :=
  fun k j => if h : j = j₀ then c k else C k ⟨j, h⟩

end GlobalTheory.CompanionTheory.FSCrofton
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
section
noncomputable section

open Matrix MeasureTheory
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp

def sumG {k : Type} [Field k] {n : ℕ} (f : GL (Ix n) k → ℂ) : ℂ := ∑ᶠ g, f g

def JpIw : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (g : GL (Ix n) L), ∃ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ : GL (Ix n) O),
      g = pM a d b * inL κ

def JpHgt : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h → ∀ κ : GL (Ix n) O,
      h (inL κ * (tauM w)⁻¹) = (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ (2 * iD (resK κ)) /
        (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ n

def JpUnif : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O),
    Irreducible ϖ → ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
    MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ φ : GL (Ix n) O → ℂ,
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∫ x, φ (ρ x) ∂ν = avgK ϖ φ

def JpCmp : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ Ψ : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ, (∀ a d b g, Ψ (pM a d b * g) = Ψ g) →
    ∀ T : GL (Ix n) O → GL (Ix n) (IsLocalRing.ResidueField O), (∀ κ, IsRed (O := O) w κ (T κ)) →
      avgK ϖ (fun κ => Ψ (T κ)) =
        sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g) /
          sumG (fun g : GL (Ix n) (IsLocalRing.ResidueField O) =>
            (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g))

def JpPos : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n r m : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 → ∀ β : Matrix (Fin n) (Fin n) k, β.rank = r →
    r ≤ m → ∃ x : ℝ, 0 < x ∧
      sumG (fun g : GL (Ix n) k => ∑ Y : Matrix (Fin n) (Fin n) k,
        (Fintype.card k : ℂ) ^ (r * iD g) * coY ψ₀ β Y * (Fintype.card k : ℂ) ^ (m * iD (g * nU Y))) = x

def JpCondition : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n r t : ℕ), r + t = n → 1 ≤ r →
    ∀ ψ₀ : AddChar (IsLocalRing.ResidueField O) ℂ, ψ₀ ≠ 1 →
    ∀ β : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), β.rank = r →
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
      ∀ ℓ : IsLocalRing.ResidueField O → O, (∀ a, IsLocalRing.residue O (ℓ a) = a) →
      ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h →
      ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
        [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
        MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ z : ℂ,
        ∫ x, ∑ Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), coY ψ₀ β Y *
          (((h (inL (ρ x) * nU ((w⁻¹ : Lˣ).1 • liftM (L := L) ℓ Y)) : ℝ≥0) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2) ∂ν = c z

end GlobalTheory.CompanionTheory.Jp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KDKDelApply
section
open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.Kabs

theorem kD_kDel_apply {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (Y : Fin (n + 1) → P) :
    kD T (kDel T' b θ) Y = ∑ s, ∑ i, T (Y s) (T' (b i) (θ (Function.update Y s (b i)))) := by
  rw [kD_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [kDel_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.insertNth_removeNth, θ.map_insertNth, map_zsmul, map_zsmul]

end GlobalTheory.CompanionTheory.Kabs
end

