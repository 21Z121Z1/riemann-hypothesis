import Mathlib

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IntegrableNormPowMulExpNegMulNormSq
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

def monomialOfMultiindex {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) : ℂ :=
  ∏ i ∈ α.support, z i ^ α i

theorem fa1Mono_eq {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α z = ∏ i, z i ^ α i := by
  unfold monomialOfMultiindex
  exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]

theorem fa1Mono_continuous {g : ℕ} (α : Fin g →₀ ℕ) : Continuous (monomialOfMultiindex α) := by
  have h : monomialOfMultiindex α = fun z : EuclideanSpace ℂ (Fin g) => ∏ i, z i ^ α i := funext (fa1Mono_eq α)
  rw [h]
  exact continuous_finsetProd _ fun i _ => (PiLp.continuous_apply 2 _ i).pow _

theorem fa1Mono_norm_le {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖monomialOfMultiindex α z‖ ≤ ‖z‖ ^ (∑ i, α i) := by
  rw [fa1Mono_eq, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le z i) _

theorem fa1Mono_smul {g : ℕ} (α : Fin g →₀ ℕ) (r : ℝ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (r • z) = (r : ℂ) ^ (∑ i, α i) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PiLp.smul_apply, Complex.real_smul, mul_pow]

theorem pow_mul_exp_neg_mul_sq_le (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-b * t ^ 2) ≤
      (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
  have hx : 0 ≤ b / 2 * t ^ 2 := by positivity
  have h1 : 1 ≤ Real.exp (b / 2 * t ^ 2) := Real.one_le_exp hx
  have h2 : (b / 2 * t ^ 2) ^ n / n.factorial ≤ Real.exp (b / 2 * t ^ 2) :=
    Real.pow_div_factorial_le_exp (x := b / 2 * t ^ 2) hx n
  have h3 : t ^ n ≤ 1 + t ^ (2 * n) := by
    rcases le_total t 1 with h | h
    · have : t ^ n ≤ 1 := pow_le_one₀ ht h
      linarith [pow_nonneg ht (2 * n)]
    · have : t ^ n ≤ t ^ (2 * n) := pow_le_pow_right₀ h (by omega)
      linarith
  have h4 : t ^ (2 * n) = (2 / b) ^ n * (b / 2 * t ^ 2) ^ n := by
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h5 : t ^ (2 * n) ≤ n.factorial * (2 / b) ^ n * Real.exp (b / 2 * t ^ 2) := by
    rw [h4]
    have h2' := (div_le_iff₀ hfac).mp h2
    have hb2 : 0 ≤ (2 / b) ^ n := by positivity
    nlinarith
  have hexp : Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) = Real.exp (-(b / 2) * t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 : t ^ n ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) := by
    nlinarith
  calc t ^ n * Real.exp (-b * t ^ 2)
      ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) :=
        mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
    _ = (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
        rw [mul_assoc, hexp]

theorem integrable_exp_neg_mul_norm_sq_euclidean {g : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => Real.exp (-b * ‖z‖ ^ 2)) := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℂ (Fin g))
    (b := (b : ℂ)) (by simpa using hb) 0 0
  refine hc.norm.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

theorem integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean {g : ℕ} (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hb2 : 0 < b / 2 := by positivity
  refine ((integrable_exp_neg_mul_norm_sq_euclidean (g := g) hb2).const_mul (1 + n.factorial * (2 / b) ^ n)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_mul_exp_neg_mul_sq_le n hb (norm_nonneg z)

theorem integrable_of_norm_le_gaussian {g : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : EuclideanSpace ℂ (Fin g) → E} (hf : Continuous f) (n : ℕ) {b C : ℝ} (hb : 0 < b)
    (h : ∀ z, ‖f z‖ ≤ C * (‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2))) : Integrable f := by
  exact ((integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean n hb).const_mul C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall h)

theorem integrable_monomial_mul_conj_gaussian {g : ℕ} (α β : Fin g →₀ ℕ) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) :=
    ((fa1Mono_continuous α).mul (Complex.continuous_conj.comp (fa1Mono_continuous β))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_norm.pow 2).neg))
  refine integrable_of_norm_le_gaussian hcont (∑ i, α i + ∑ i, β i) one_pos (C := 1) fun z => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), one_mul, neg_one_mul, pow_add]
  have h1 := fa1Mono_norm_le α z
  have h2 := fa1Mono_norm_le β z
  have he := (Real.exp_pos (-‖z‖ ^ 2)).le
  gcongr

theorem integrable_norm_monomial_sq_gaussian {g : ℕ} (α : Fin g →₀ ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2) :=
    ((fa1Mono_continuous α).norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  refine integrable_of_norm_le_gaussian hcont (2 * ∑ i, α i) hb (C := 1) fun z => ?_
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_mul']
  have h1 := fa1Mono_norm_le α z
  gcongr

noncomputable def coordinateRotation {g : ℕ} (j : Fin g) (u : Circle) :
    EuclideanSpace ℂ (Fin g) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin g) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = j then rotation u else LinearIsometryEquiv.refl ℝ ℂ)

theorem fa1Rot_apply {g : ℕ} (j : Fin g) (u : Circle) (z : EuclideanSpace ℂ (Fin g)) (i : Fin g) :
    coordinateRotation j u z i = (if i = j then (u : ℂ) else 1) * z i := by
  simp only [coordinateRotation, LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs with h
  · simp [rotation_apply]
  · simp

theorem fa1Mono_rot {g : ℕ} (α : Fin g →₀ ℕ) (j : Fin g) (u : Circle)
    (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (coordinateRotation j u z) = (u : ℂ) ^ (α j) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq]
  simp only [fa1Rot_apply, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem integral_monomial_mul_conj_gaussian_eq_zero {g : ℕ} {α β : Fin g →₀ ℕ} (h : α ≠ β) :
    ∫ z : EuclideanSpace ℂ (Fin g),
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
    by_contra hcon
    exact h (Finsupp.ext fun j => not_not.mp fun hne => hcon ⟨j, hne⟩)
  have hm : ((α j : ℝ) - β j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
  set u : Circle := Circle.exp (Real.pi / ((α j : ℝ) - β j)) with hu
  set F : EuclideanSpace ℂ (Fin g) → ℂ := fun z =>
    monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) with hF
  have hc : (u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j)) = -1 := by
    rw [hu, Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hm' : ((α j : ℂ) - β j) ≠ 0 := by exact_mod_cast hm
    have : (α j : ℂ) * (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) +
        (β j : ℂ) * (starRingEnd ℂ) (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) =
        Real.pi * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_pi_mul_I]
  have hrot : ∀ z, F (coordinateRotation j u z) =
      ((u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j))) * F z := by
    intro z
    simp only [hF, fa1Mono_rot, LinearIsometryEquiv.norm_map, map_mul]
    ring
  have hint : ∫ z, F (coordinateRotation j u z) = ∫ z, F z :=
    (coordinateRotation j u).measurePreserving.integral_comp (coordinateRotation j u).toHomeomorph.measurableEmbedding F
  simp_rw [hrot, hc] at hint
  rw [integral_const_mul] at hint
  linear_combination (-1 / 2 : ℂ) * hint

theorem integral_norm_monomial_sq_gaussian_pos {g : ℕ} (α : Fin g →₀ ℕ) :
    0 < ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  set f : EuclideanSpace ℂ (Fin g) → ℝ := fun z => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) with hf
  have hcont : Continuous f :=
    ((fa1Mono_continuous α).norm.pow 2).mul (Real.continuous_exp.comp (continuous_norm.pow 2).neg)
  have hint : Integrable f := by
    have := integrable_norm_monomial_sq_gaussian α one_pos
    simpa [neg_one_mul] using this
  have hnn : 0 ≤ f := fun z => by
    simp only [Pi.zero_apply, hf]
    positivity
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  let z₀ : EuclideanSpace ℂ (Fin g) := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hz₁ : monomialOfMultiindex α z₀ = 1 := by
    rw [fa1Mono_eq]
    simp [z₀]
  have hz₀ : f z₀ ≠ 0 := by
    simp only [hf, hz₁, norm_one, one_pow, one_mul]
    exact (Real.exp_pos _).ne'
  exact hcont.isOpen_support.measure_pos _ ⟨z₀, hz₀⟩

theorem integral_norm_monomial_sq_gaussian_half {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      2 ^ (g + ∑ i, α i) *
        ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpt : ∀ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * (‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2)) := by
    intro x
    rw [fa1Mono_smul, norm_mul, norm_pow, Complex.norm_real, norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow, mul_pow, ← pow_mul,
      mul_comm (∑ i, α i) 2, pow_mul, hs2, show -(1 / 2) * (2 * ‖x‖ ^ 2) = -‖x‖ ^ 2 by ring]
    ring
  have e1 : ∫ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * ∫ x : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hdim : |(Real.sqrt 2 ^ Module.finrank ℝ (EuclideanSpace ℂ (Fin g)))⁻¹| = ((2 : ℝ) ^ g)⁻¹ := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin, pow_mul, hs2,
      abs_of_pos (by positivity)]
  have e2 := MeasureTheory.Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℂ (Fin g)))
    (fun z => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) (Real.sqrt 2)
  beta_reduce at e2
  rw [hdim, smul_eq_mul, e1] at e2
  have h2g : (2 : ℝ) ^ g ≠ 0 := by positivity
  rw [pow_add, mul_assoc, e2, ← mul_assoc, mul_inv_cancel₀ h2g, one_mul]

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerpSurj
section
namespace ReciprocityTheory.ChartRestriction.G.I2.DimA

open Module

section Perp

variable {H : Type*} [AddCommGroup H] (B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ)

theorem alt_swap (halt : ∀ h, B h h = 0) (x y : H) : B x y = -B y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  linear_combination h

def perp (e f : H) : Submodule ℤ H := LinearMap.ker (B.flip e) ⊓ LinearMap.ker (B.flip f)

theorem mem_perp {e f h : H} : h ∈ perp B e f ↔ B h e = 0 ∧ B h f = 0 := by
  simp [perp]

variable (halt : ∀ h, B h h = 0) (e f : H) (he : B e f = 1)
include halt he

theorem proj_mem (y : H) : y - B y f • e + B y e • f ∈ perp B e f := by
  have h1 : B f e = -1 := by rw [alt_swap B halt, he]
  rw [mem_perp]
  constructor <;> simp [halt, he, h1] <;> ring

def proj : H →ₗ[ℤ] perp B e f where
  toFun y := ⟨y - B y f • e + B y e • f, proj_mem B halt e f he y⟩
  map_add' x y := by ext; simp only [map_add, LinearMap.add_apply, add_smul, Submodule.coe_add]; abel
  map_smul' c x := by
    ext; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Submodule.coe_smul, mul_smul,
      RingHom.id_apply, smul_add, smul_sub]

theorem proj_apply (y : H) : (proj B halt e f he y : H) = y - B y f • e + B y e • f := rfl

def splitEquiv : H ≃ₗ[ℤ] perp B e f × ℤ × ℤ where
  toFun y := (proj B halt e f he y, B y f, B y e)
  map_add' x y := by simp
  map_smul' c x := by simp
  invFun p := (p.1 : H) + p.2.1 • e - p.2.2 • f
  left_inv y := by simp only [proj_apply]; abel
  right_inv p := by
    obtain ⟨⟨p, hp⟩, a, c⟩ := p
    have h1 : B f e = -1 := by rw [alt_swap B halt, he]
    rw [mem_perp] at hp
    have hf : B (p + a • e - c • f) f = a := by
      simp [hp.2, he, halt]
    have hE : B (p + a • e - c • f) e = c := by
      simp [hp.1, h1, halt]
    simp only [Prod.mk.injEq]
    refine ⟨?_, hf, hE⟩
    ext
    rw [proj_apply, hf, hE]
    abel

theorem perp_surj (hB : ∀ φ : H →ₗ[ℤ] ℤ, ∃ x, B x = φ) (φ : perp B e f →ₗ[ℤ] ℤ) :
    ∃ x : perp B e f, B.domRestrict₁₂ (perp B e f) (perp B e f) x = φ := by
  obtain ⟨x, hx⟩ := hB (φ.comp (proj B halt e f he))
  refine ⟨proj B halt e f he x, LinearMap.ext fun ⟨p, hp⟩ => ?_⟩
  have hp' := (mem_perp B).1 hp
  have hpe : B e p = 0 := by rw [alt_swap B halt, hp'.1, neg_zero]
  have hpf : B f p = 0 := by rw [alt_swap B halt, hp'.2, neg_zero]
  have hproj : proj B halt e f he p = ⟨p, hp⟩ := by
    ext; rw [proj_apply, hp'.1, hp'.2]; simp
  have hxp : B x p = φ (proj B halt e f he p) := by
    rw [hx]; rfl
  rw [LinearMap.domRestrict₁₂_apply, proj_apply]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hpe, hpf, smul_eq_mul, mul_zero, sub_zero, add_zero]
  rw [hxp, hproj]

end Perp

theorem sympl : ∀ (n : ℕ) (H : Type) [AddCommGroup H] [Module.Free ℤ H] [Module.Finite ℤ H],
    finrank ℤ H = n → ∀ B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ, (∀ h, B h h = 0) →
    (∀ φ : H →ₗ[ℤ] ℤ, ∃ x, B x = φ) →
    ∃ k, n = 2 * k ∧ ∃ e f : Fin k → H, (∀ i j, B (e i) (e j) = 0) ∧
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ hn B halt hB
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨0, rfl, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  let b := Module.finBasisOfFinrankEq ℤ H hn
  obtain ⟨x, hx⟩ := hB (b.coord ⟨0, hpos⟩)
  have hxf : B x (b ⟨0, hpos⟩) = 1 := by rw [hx]; simp
  set e := x
  set f := b ⟨0, hpos⟩
  let Q := perp B e f
  haveI : Module.Free ℤ Q := Module.Free.of_basis (Q.basisOfPid b).2
  haveI : Module.Finite ℤ Q := Module.Finite.of_basis (Q.basisOfPid b).2
  have hr : finrank ℤ Q + 2 = n := by
    have h : finrank ℤ H = finrank ℤ (Q × ℤ × ℤ) := (splitEquiv B halt e f hxf).finrank_eq
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, hn] at h
    omega
  have halt' : ∀ h : Q, B.domRestrict₁₂ Q Q h h = 0 := fun h => halt h
  obtain ⟨k', hk', e', f', hee, hef⟩ :=
    ih (n - 2) (by omega) Q (by omega) (B.domRestrict₁₂ Q Q) halt'
      (perp_surj B halt e f hxf hB)
  refine ⟨k' + 1, by omega, Fin.cons e (fun i => (e' i : H)), Fin.cons f (fun i => (f' i : H)),
    ?_, ?_⟩
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using halt e
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [alt_swap B halt, ((mem_perp B).1 (e' j).2).1, neg_zero]
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact ((mem_perp B).1 (e' i).2).1
      | succ j =>
        simp only [Fin.cons_succ]
        exact hee i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hxf
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [alt_swap B halt, ((mem_perp B).1 (f' j).2).1, neg_zero]
        simp [(Fin.succ_ne_zero j).symm]
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [((mem_perp B).1 (e' i).2).2]
        simp [Fin.succ_ne_zero i]
      | succ j =>
        simp only [Fin.cons_succ, Fin.succ_inj]
        exact hef i j

end ReciprocityTheory.ChartRestriction.G.I2.DimA
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVA
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Module
open scoped nonZeroDivisors

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem exists_dual (φ : 𝓞 E →+ ℤ) :
    ∃ y : E, ∀ β : 𝓞 E, Algebra.trace ℚ E ((β : E) * y) = φ β := by
  classical
  let bZ := NumberField.RingOfIntegers.basis E
  let bQ := NumberField.integralBasis E
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  let dB := (Algebra.traceForm ℚ E).dualBasis hnd bQ
  refine ⟨∑ i, (φ (bZ i) : ℚ) • dB i, fun β => ?_⟩
  let f₁ : 𝓞 E →ₗ[ℤ] ℚ :=
    ((Algebra.trace ℚ E).restrictScalars ℤ).comp
      ((LinearMap.mulRight ℚ (∑ i, (φ (bZ i) : ℚ) • dB i)).restrictScalars ℤ ∘ₗ
        (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)
  let f₂ : 𝓞 E →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap ∘ₗ φ.toIntLinearMap
  have hf : f₁ = f₂ := by
    refine bZ.ext fun j => ?_
    simp only [f₁, f₂, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.mulRight_apply, Algebra.linearMap_apply, AddMonoidHom.coe_toIntLinearMap,
      Int.coe_castAddHom]
    rw [Finset.mul_sum, map_sum]
    have hb : (algebraMap (𝓞 E) E) (bZ j) = bQ j := (NumberField.integralBasis_apply E j).symm
    rw [hb]
    simp_rw [mul_smul_comm, map_smul]
    have h : ∀ i, Algebra.trace ℚ E (bQ j * dB i) = if j = i then 1 else 0 := fun i => by
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left hnd bQ i j
    simp [h]
  have := congrArg (fun g => g β) hf
  simpa [f₁, f₂] using this

abbrev Dual1 (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)

theorem mem_dual_of (y : E) (hy : ∀ β : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E ((β : E) * y) = k) :
    y ∈ Dual1 E := by
  rw [FractionalIdeal.mem_dual (I := (1 : FractionalIdeal (𝓞 E)⁰ E)) one_ne_zero]
  intro a ha
  obtain ⟨β, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
  obtain ⟨k, hk⟩ := hy β
  refine ⟨k, ?_⟩
  rw [Algebra.traceForm_apply, mul_comm, hk]
  simp

theorem one_le_norm_mul (l : E) (hl : l ≠ 0) (hmem : l ∈ Dual1 E * Dual1 E) :
    (1 : ℚ) ≤ |Algebra.norm ℚ l| * ((NumberField.discr E).natAbs : ℚ) ^ 2 := by
  classical
  have hD0 : Dual1 E ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  set dI : FractionalIdeal (𝓞 E)⁰ E :=
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) with hdI
  have hdD : dI * Dual1 E = 1 := by
    rw [hdI, coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
    exact inv_mul_cancel₀ hD0
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ l ≤ Dual1 E * Dual1 E :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hJ : dI * dI * FractionalIdeal.spanSingleton (𝓞 E)⁰ l ≤ 1 := by
    calc _ ≤ dI * dI * (Dual1 E * Dual1 E) := by first | exact mul_le_mul' le_rfl hle | gcongr
      _ = (dI * Dual1 E) * (dI * Dual1 E) := by ring
      _ = 1 := by rw [hdD, one_mul]
  obtain ⟨J, hJe⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hn := congrArg FractionalIdeal.absNorm hJe
  rw [map_mul, map_mul, FractionalIdeal.absNorm_span_singleton, hdI, FractionalIdeal.coeIdeal_absNorm (K := E),
    FractionalIdeal.coeIdeal_absNorm (K := E), NumberField.absNorm_differentIdeal (K := E) (𝒪 := 𝓞 E)] at hn
  have hN0 : Algebra.norm ℚ l ≠ 0 := Algebra.norm_ne_zero_iff.mpr hl
  have hd0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have hpos : ((NumberField.discr E).natAbs : ℚ) * (NumberField.discr E).natAbs
      * |Algebra.norm ℚ l| ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hd0) (by exact_mod_cast hd0)) (abs_ne_zero.mpr hN0)
  have hJ1 : 1 ≤ Ideal.absNorm J := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm J) with h0 | h0
    · exfalso; rw [h0, Nat.cast_zero] at hn; exact hpos hn.symm
    · exact h0
  have h1 : (1 : ℚ) ≤ Ideal.absNorm J := by exact_mod_cast hJ1
  rw [hn] at h1
  calc (1 : ℚ) ≤ _ := h1
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVC
section
namespace ReciprocityTheory.ChartRestriction.G.I2

theorem amgm_sum_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ℝ) (hP : 0 ≤ P) (hprod : P ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) * P ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, a i := by
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) a (fun _ _ => zero_le_one)
    (by simpa using hn') (fun i _ => ha i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [le_div_iff₀ hn'] at h
  have h2 : P ^ ((Fintype.card ι : ℝ)⁻¹) ≤ (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
    Real.rpow_le_rpow hP hprod (by positivity)
  calc (Fintype.card ι : ℝ) * P ^ ((Fintype.card ι : ℝ)⁻¹)
      ≤ (Fintype.card ι : ℝ) * (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left h2 hn'.le
    _ = (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) * Fintype.card ι := mul_comm _ _
    _ ≤ ∑ i, a i := h

theorem inv_sq_rpow_inv (D : ℝ) (hD : 0 < D) (n : ℝ) :
    ((D ^ 2)⁻¹) ^ n⁻¹ = ((D ^ n⁻¹) ^ 2)⁻¹ := by
  rw [Real.inv_rpow (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (D ^ n⁻¹), ← Real.rpow_mul hD.le,
    ← Real.rpow_mul hD.le, mul_comm]

theorem sum_ge_of_prod_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (D : ℝ) (hD : 0 < D) (hprod : (D ^ 2)⁻¹ ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) / (D ^ ((Fintype.card ι : ℝ)⁻¹)) ^ 2 ≤ ∑ i, a i := by
  have h := amgm_sum_ge a ha _ (by positivity) hprod hn
  rwa [inv_sq_rpow_inv D hD, ← div_eq_mul_inv] at h

end ReciprocityTheory.ChartRestriction.G.I2
end

