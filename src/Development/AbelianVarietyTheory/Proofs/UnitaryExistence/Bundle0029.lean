import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpMulThetaCharAutomorphy
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ThetaAH

variable {g : ℕ}

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
private lemma intCast_dotProduct' (k m : Fin g → ℤ) :
    ((k ⬝ᵥ m : ℤ) : ℂ) = (fun i => (k i : ℂ)) ⬝ᵥ (fun i => (m i : ℂ)) := by
  simp [dotProduct]

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in

theorem _root_.GlobalTheory.ThetaAH.thetaChar_add_period {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (a b w : Fin g → ℂ)
    (m n : Fin g → ℤ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b (w + ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)))) =
      Complex.exp (Real.pi * Complex.I * (2 * (a ⬝ᵥ fun i => (m i : ℂ)) - 2 * ((fun i => (n i : ℂ)) ⬝ᵥ b)
        - ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ)) - 2 * ((fun i => (n i : ℂ)) ⬝ᵥ w))) *
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar
  rw [← (Equiv.subRight n).tsum_eq, ← tsum_mul_left]
  congr 1
  funext k
  set N : Fin g → ℂ := fun i => (n i : ℂ)
  set M : Fin g → ℂ := fun i => (m i : ℂ)
  set K : Fin g → ℂ := fun i => (k i : ℂ)
  have hc : (fun i => (((Equiv.subRight n k) i : ℤ) : ℂ)) = K - N := by
    funext i; simp [K, N]
  have hsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ τ *ᵥ y = y ⬝ᵥ τ *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hs.eq]
  rw [hc, ← Complex.exp_add]
  have key : Real.pi * Complex.I * ((K - N + a) ⬝ᵥ τ *ᵥ (K - N + a)) +
      2 * Real.pi * Complex.I * ((K - N + a) ⬝ᵥ (w + (M + τ *ᵥ N) + b)) =
      Real.pi * Complex.I * (2 * (a ⬝ᵥ M) - 2 * (N ⬝ᵥ b) - (N ⬝ᵥ τ *ᵥ N) - 2 * (N ⬝ᵥ w)) +
      (Real.pi * Complex.I * ((K + a) ⬝ᵥ τ *ᵥ (K + a)) +
        2 * Real.pi * Complex.I * ((K + a) ⬝ᵥ (w + b))) +
      (((k ⬝ᵥ m - n ⬝ᵥ m : ℤ) : ℂ)) * (2 * Real.pi * Complex.I) := by
    have h1 := hsym N (K + a)
    push_cast
    rw [intCast_dotProduct', intCast_dotProduct']
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dotProduct_sub, sub_dotProduct, dotProduct_add,
      add_dotProduct] at h1 ⊢
    linear_combination (-(Real.pi * Complex.I)) * h1
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
theorem _root_.GlobalTheory.ThetaAH.hermForm_pullback (h B : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (hᵀ * B * h.map (starRingEnd ℂ)) z w = (h *ᵥ z) ⬝ᵥ B *ᵥ star (h *ᵥ w) := by
  have hs : h.map (starRingEnd ℂ) *ᵥ star w = star (h *ᵥ w) := by
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
private lemma inv_im_transpose_eq_and_mul_eq_one (τ : Matrix (Fin g) (Fin g) ℂ) (hY : (τ.map Complex.im).PosDef) :
    (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)))ᵀ =
      ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) ∧
    ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *
      (τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) = 1 := by
  have hdet : IsUnit (τ.map Complex.im).det := isUnit_iff_ne_zero.mpr hY.det_pos.ne'
  constructor
  · rw [← Matrix.transpose_map]
    congr 1
    have := hY.isHermitian.inv
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · have := Matrix.nonsing_inv_mul _ hdet
    have h2 := congrArg (fun A => A.map (Complex.ofRealHom)) this
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
private lemma re_quadratic_sub_hermitian_eq_im_form (S : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℂ) :
    (Real.pi / 2 * (v ⬝ᵥ (S.map (fun x : ℝ => (x : ℂ)) *ᵥ v))).re +
      (Real.pi / 2 * (v ⬝ᵥ (S.map (fun x : ℝ => (x : ℂ)) *ᵥ v))).re
      + -Real.pi * (v ⬝ᵥ S.map (fun x : ℝ => (x : ℂ)) *ᵥ star v).re =
      -2 * Real.pi * ((fun i => (v i).im) ⬝ᵥ (S *ᵥ fun i => (v i).im)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.mul_im]
  ring

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
private lemma star_lattice_vector_eq (τ : Matrix (Fin g) (Fin g) ℂ) (m n : Fin g → ℤ) :
    star ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) =
      ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) -
        (2 * Complex.I) • ((τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) *ᵥ (fun i => (n i : ℂ))) := by
  funext i
  apply Complex.ext <;> simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum] <;> ring

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in

theorem _root_.GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (q : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) → (∀ z, q z = Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (h *ᵥ z)))) → (∀ z, ‖Complex.exp (q z)‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) = Real.exp (-2 * Real.pi * ((fun i => ((h *ᵥ z) i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ fun i => ((h *ᵥ z) i).im)))) ∧ ∀ (lam : Fin g → ℂ) (m n : Fin g → ℤ), h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) → ∃ χ : ℂ, ‖χ‖ = 1 ∧ ∀ z, Complex.exp (q (z + lam)) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) = χ * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z lam + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm lam lam) * (Complex.exp (q z) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ (h *ᵥ z)) := by
  intro g τ h Hm c₁ c₂ q hs hY hc₁ hc₂ hHm hq
  obtain ⟨hST, hSY⟩ := inv_im_transpose_eq_and_mul_eq_one τ hY
  set S : Matrix (Fin g) (Fin g) ℂ := ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) with hSdef
  have hSsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ S *ᵥ y = y ⬝ᵥ S *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hST]
  refine ⟨fun z => ?_, fun lam m n hlam => ?_⟩
  · rw [hq, hHm, _root_.GlobalTheory.ThetaAH.hermForm_pullback, Complex.norm_exp, sq, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    exact re_quadratic_sub_hermitian_eq_im_form _ (h *ᵥ z)
  set N : Fin g → ℂ := fun i => (n i : ℂ) with hN
  set M : Fin g → ℂ := fun i => (m i : ℂ) with hM
  have him : ∀ c : Fin g → ℂ, (∀ i, c i = 0 ∨ c i = 1 / 2) → (c ⬝ᵥ M).im = 0 ∧ (N ⬝ᵥ c).im = 0 := by
    intro c hc
    constructor
    · simp only [dotProduct, Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hc i with h0 | h0 <;> simp [h0, M]
    · simp only [dotProduct, Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hc i with h0 | h0 <;> simp [h0, N]
  refine ⟨Complex.exp (Real.pi * Complex.I * (M ⬝ᵥ N + 2 * (c₁ ⬝ᵥ M) - 2 * (N ⬝ᵥ c₂))), ?_,
    fun z => ?_⟩
  · have hMN : (M ⬝ᵥ N).im = 0 := by
      simp [dotProduct, Complex.im_sum, M, N]
    rw [Complex.norm_exp, Real.exp_eq_one_iff]
    simp [Complex.mul_re, hMN, (him c₁ hc₁).1, (him c₂ hc₂).2]
  obtain ⟨v, hv⟩ : ∃ v, h *ᵥ z = v := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, h *ᵥ lam = μ := ⟨_, rfl⟩
  rw [hμ] at hlam
  have hstar : star μ = μ - (2 * Complex.I) • ((τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) *ᵥ N) := by
    rw [hlam]; exact star_lattice_vector_eq τ m n
  have hSYN : S *ᵥ ((τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) *ᵥ N) = N := by
    rw [Matrix.mulVec_mulVec, hSY, Matrix.one_mulVec]
  have hSstar : S *ᵥ star μ = S *ᵥ μ - (2 * Complex.I) • N := by
    rw [hstar, Matrix.mulVec_sub, Matrix.mulVec_smul, hSYN]
  have f1 : v ⬝ᵥ S *ᵥ star μ = v ⬝ᵥ S *ᵥ μ - 2 * Complex.I * (v ⬝ᵥ N) := by
    rw [hSstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have f2 : μ ⬝ᵥ S *ᵥ star μ = μ ⬝ᵥ S *ᵥ μ - 2 * Complex.I * (μ ⬝ᵥ N) := by
    rw [hSstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have f3 : μ ⬝ᵥ N = M ⬝ᵥ N + N ⬝ᵥ τ *ᵥ N := by
    rw [hlam, add_dotProduct, dotProduct_comm (τ *ᵥ N)]
  have f4 : (v + μ) ⬝ᵥ S *ᵥ (v + μ) = v ⬝ᵥ S *ᵥ v + 2 * (v ⬝ᵥ S *ᵥ μ) + μ ⬝ᵥ S *ᵥ μ := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hSsym μ v]
    ring
  have f5 : N ⬝ᵥ v = v ⬝ᵥ N := dotProduct_comm _ _
  have htheta : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) =
      Complex.exp (Real.pi * Complex.I * (2 * (c₁ ⬝ᵥ M) - 2 * (N ⬝ᵥ c₂) - (N ⬝ᵥ τ *ᵥ N)
        - 2 * (N ⬝ᵥ v))) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ v := by
    rw [Matrix.mulVec_add, hv, hμ, hlam]
    exact _root_.GlobalTheory.ThetaAH.thetaChar_add_period hs c₁ c₂ v m n
  rw [htheta, hq (z + lam), hq z, hHm, _root_.GlobalTheory.ThetaAH.hermForm_pullback,
    _root_.GlobalTheory.ThetaAH.hermForm_pullback, Matrix.mulVec_add, hv, hμ,
    ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  congr 2
  linear_combination (Real.pi / 2) * f4 - Real.pi * f1 - (Real.pi / 2) * f2 +
    (Real.pi * Complex.I) * f3 - (2 * Real.pi * Complex.I) * f5

end GlobalTheory.ThetaAH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.NormFin

theorem finite_of_semilinear_injective {R S N M : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [AddCommGroup N] [Module R N] [AddCommGroup M] [Module S M] [Module.Finite S M]
    (φ : R →+* S) (hφ : φ.Finite) (f : N →ₛₗ[φ] M) (hf : Function.Injective f) :
    Module.Finite R N := by
  letI := φ.toAlgebra
  letI : Module R M := Module.compHom M φ
  haveI : IsScalarTower R S M := ⟨fun r s m => mul_smul (φ r) s m⟩
  haveI : Module.Finite R S := hφ
  haveI : Module.Finite R M := Module.Finite.trans S M
  let g : N →ₗ[R] M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => f.map_smulₛₗ r x }
  exact Module.Finite.of_injective g hf

theorem finite_iterateFrobenius (k P : Type*) [Field k] [PerfectField k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] (p : ℕ) [ExpChar k p] [ExpChar P p] (e : ℕ) :
    (iterateFrobenius P p e).Finite := by
  refine RingHom.IsIntegral.to_finite ?_ ?_
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_ne_zero k p)), ?_⟩
    simp [iterateFrobenius_def]
  · refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k P) ?_
    have h : (iterateFrobenius P p e).comp (algebraMap k P) =
        (algebraMap k P).comp (iterateFrobenius k p e) := by
      ext x
      simp [iterateFrobenius_def]
    rw [h]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (.of_surjective _ (bijective_iterateFrobenius k p e).2)

theorem finite_integralClosure_of_isIntegrallyClosed (k P K F : Type*) [Field k] [PerfectField k]
    [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [Algebra k P] [Algebra.FiniteType k P]
    [Field K] [Algebra P K] [IsFractionRing P K] [Field F] [Algebra K F] [Algebra P F]
    [IsScalarTower P K F] [FiniteDimensional K F] : Module.Finite P (integralClosure P F) := by
  haveI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  obtain ⟨p, hp⟩ := ExpChar.exists k
  haveI : ExpChar P p := expChar_of_injective_algebraMap (algebraMap k P).injective p
  haveI : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective P K) p
  haveI : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let E := separableClosure K F
  haveI : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p
  haveI : Module.Finite P (integralClosure P E) := IsIntegralClosure.finite P K E _
  haveI : IsScalarTower P E F := .of_algebraMap_eq' rfl
  let e := IsPurelyInseparable.exponent E F
  have hE : ∀ z : F, z ^ p ^ e ∈ E := fun z => by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' E p z
    exact hy ▸ y.2
  let f : integralClosure P F →ₛₗ[iterateFrobenius P p e] integralClosure P E :=
    { toFun := fun z => ⟨⟨z.1 ^ p ^ e, hE _⟩,
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) Subtype.val_injective).mp
          (IsIntegral.pow z.2 _)⟩
      map_add' := fun x y => Subtype.ext (Subtype.ext (add_pow_expChar_pow _ _ _ _))
      map_smul' := fun r x => Subtype.ext (Subtype.ext (by
        change (r • x.1) ^ p ^ e = (r ^ p ^ e) • x.1 ^ p ^ e
        rw [smul_pow])) }
  refine finite_of_semilinear_injective _ (finite_iterateFrobenius k P p e) f fun x y h => ?_
  have h1 : x.1 ^ p ^ e = y.1 ^ p ^ e := congrArg (fun w : integralClosure P E => (w.1.1 : F)) h
  exact Subtype.ext ((iterateFrobenius F p e).injective h1)

theorem finite_integralClosure_of_perfectField (k B F L : Type*) [Field k] [PerfectField k]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] [Field F] [Algebra B F]
    [IsFractionRing B F] [Field L] [Algebra F L] [Algebra B L] [IsScalarTower B F L]
    [FiniteDimensional F L] : Module.Finite B (integralClosure B L) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  let P := MvPolynomial (Fin s) k
  letI : Algebra P B := g.toRingHom.toAlgebra
  haveI : Module.Finite P B := hfin
  haveI : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : Algebra P F := ((algebraMap B F).comp (algebraMap P B)).toAlgebra
  haveI : IsScalarTower P B F := .of_algebraMap_eq' rfl
  letI : Algebra P L := ((algebraMap B L).comp (algebraMap P B)).toAlgebra
  haveI : IsScalarTower P B L := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P F L := .of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply B F L _
  haveI : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    ((IsFractionRing.injective B F).comp hinj)
  let K := FractionRing P
  letI : Algebra K F := FractionRing.liftAlgebra P F
  haveI : FiniteDimensional K F := Module.Finite.of_isLocalization P B (nonZeroDivisors P)
  letI : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  haveI : IsScalarTower K F L := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P K L := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K F L, ← IsScalarTower.algebraMap_apply P K F,
      ← IsScalarTower.algebraMap_apply P F L]
  haveI : FiniteDimensional K L := Module.Finite.trans F L
  haveI := finite_integralClosure_of_isIntegrallyClosed k P K L
  have h : Module.Finite P ((integralClosure B L).restrictScalars P) := by
    rwa [integralClosure_restrictScalars_of_isIntegral]
  haveI : Module.Finite P (integralClosure B L) := h
  exact Module.Finite.of_restrictScalars_finite P B _

example : let k := AlgebraicClosure (ZMod 2)
    let B := Algebra.adjoin k ({Polynomial.X ^ 2, Polynomial.X ^ 3} : Set (Polynomial k))
    Module.Finite B (integralClosure B (FractionRing B)) := by
  intro k B
  haveI : Algebra.FiniteType k B := .adjoin_of_finite (Set.toFinite _)
  exact finite_integralClosure_of_perfectField k B (FractionRing B) (FractionRing B)

theorem finite_integralClosure_of_isAlgClosed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (F : Type) [Field F] [Algebra B F] [IsFractionRing B F],
      Module.Finite B (integralClosure B F) :=
  fun k _ _ B _ _ _ _ F _ _ _ => finite_integralClosure_of_perfectField k B F F

end GlobalTheory.NormFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankRatSkewHermitianMatricesCmField
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem two_mul_card_of_cmType_finset (E : Type) [Field E] [NumberField E]
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    2 * Ψ.card = Module.finrank ℚ E := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => star_star τ
  rw [← NumberField.Embeddings.card E ℂ]
  have h1 : (Ψᶜ).card = Ψ.card := by
    refine Finset.card_bij (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_
    · intro τ hτ
      rw [Finset.mem_compl] at hτ
      exact (hΨ _).mpr (by rw [hcc]; exact hτ)
    · intro a _ b _ h
      have := congrArg ComplexEmbedding.conjugate h
      rwa [hcc, hcc] at this
    · intro τ hτ
      refine ⟨ComplexEmbedding.conjugate τ, ?_, hcc τ⟩
      rw [Finset.mem_compl]
      exact (hΨ τ).mp hτ
  have h2 := Finset.card_add_card_compl Ψ
  omega

theorem finrank_skewHermitian_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ρ : ℕ) (Ψ : Finset (E →+* ℂ)),
      (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
      ∀ W : Submodule ℚ (Matrix (Fin ρ) (Fin ρ) E), (∀ β, β ∈ W ↔ FJ.IsSkew β) →
        Module.finrank ℚ W = Ψ.card * ρ ^ 2 := by
  intro E _ _ _ ρ Ψ hΨ W hW
  have hcard := two_mul_card_of_cmType_finset E Ψ hΨ
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : E, δ ≠ 0 ∧ IsCMField.complexConj E δ = -δ := by
    have hne : IsCMField.complexConj E ≠ 1 := IsCMField.complexConj_ne_one E
    obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
      by_contra h
      push Not at h
      exact hne (AlgEquiv.ext h)
    refine ⟨x - IsCMField.complexConj E x, sub_ne_zero.mpr hx.symm, ?_⟩
    rw [map_sub, IsCMField.complexConj_apply_apply]
    ring
  have hW' : ∀ β, β ∈ W ↔ ∀ a b, IsCMField.complexConj E (β a b) = -β b a := hW
  let f : (W × W) →ₗ[ℚ] Matrix (Fin ρ) (Fin ρ) E :=
    { toFun := fun p => (p.1 : Matrix (Fin ρ) (Fin ρ) E) + δ • (p.2 : Matrix (Fin ρ) (Fin ρ) E)
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, RingHom.id_apply,
          smul_comm δ c] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨A, B⟩ h
    have hA := (hW' _).mp A.2
    have hB := (hW' _).mp B.2
    have h0 : ∀ a b, (A : Matrix (Fin ρ) (Fin ρ) E) a b + δ * (B : Matrix (Fin ρ) (Fin ρ) E) a b = 0 :=
      fun a b => by
        have := congrFun (congrFun h a) b
        simpa [f] using this
    have h1 : ∀ a b, (A : Matrix (Fin ρ) (Fin ρ) E) a b = 0 ∧ (B : Matrix (Fin ρ) (Fin ρ) E) a b = 0 := by
      intro a b
      have e1 := h0 a b
      have e2 := congrArg (IsCMField.complexConj E) (h0 b a)
      rw [map_add, map_mul, hδ, hA, hB, map_zero] at e2
      have e3 : (A : Matrix (Fin ρ) (Fin ρ) E) a b = 0 := by linear_combination (e1 - e2) / 2
      refine ⟨e3, ?_⟩
      rw [e3, zero_add] at e1
      exact (mul_eq_zero.mp e1).resolve_left hδ0
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext a b; exact (h1 a b).1
    · ext a b; exact (h1 a b).2
  have hsurj : Function.Surjective f := by
    intro M
    refine ⟨(⟨Matrix.of fun a b => (M a b - IsCMField.complexConj E (M b a)) / 2, (hW' _).mpr ?_⟩,
      ⟨Matrix.of fun a b => (M a b + IsCMField.complexConj E (M b a)) / (2 * δ), (hW' _).mpr ?_⟩), ?_⟩
    · intro a b
      simp only [Matrix.of_apply, map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_ofNat]
      ring
    · intro a b
      simp only [Matrix.of_apply, map_div₀, map_add, map_mul, hδ,
        IsCMField.complexConj_apply_apply, map_ofNat]
      field_simp
      ring
    · ext a b
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      field_simp
      ring
  have hfin := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_prod, Module.finrank_matrix, ← hcard, Fintype.card_fin] at hfin
  have : 2 * Module.finrank ℚ W = 2 * (Ψ.card * ρ ^ 2) := by
    rw [two_mul, hfin]; ring
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory

universe u

theorem geometricallyIrreducible_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IrreducibleSpace X] :
    GeometricallyIrreducible f := by
  refine ⟨fun K _ y Z p q h => ?_⟩
  have := LocallyOfFiniteType.jacobsonSpace f
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hs : Surjective p := MorphismProperty.of_isPullback h.flip hy
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)

  have fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b := by
    intro x hx a b ha hb
    let s := pointOfClosedPoint f x hx
    have hs : s ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hx
    let t : Spec (.of K) ⟶ Z := h.lift (y ≫ s) (𝟙 _) (by simp [hs])
    have ht : IsPullback t y p s := by
      refine IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip
      rw [hs, show t ≫ q = 𝟙 _ by simp [t]]
      exact IsPullback.of_id_fst
    obtain ⟨a', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k)
      (ha.trans (pointOfClosedPoint_apply f x hx _).symm)
    obtain ⟨b', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k)
      (hb.trans (pointOfClosedPoint_apply f x hx _).symm)
    rw [Subsingleton.elim a' b']
  have hne : Nonempty Z := (p.surjective (Classical.arbitrary X)).nonempty
  have : PreirreducibleSpace Z := ⟨fun U V hU hV hU' hV' => by
    rw [Set.univ_inter] at hU' hV' ⊢
    have o₁ : IsOpen (p '' U) := p.isOpenMap _ hU
    have o₂ : IsOpen (p '' V) := p.isOpenMap _ hV
    obtain ⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hxc⟩ := nonempty_inter_closedPoints
      (nonempty_preirreducible_inter o₁ o₂ (hU'.image _) (hV'.image _))
      (o₁.inter o₂).isLocallyClosed
    exact ⟨a, ha, fib x hxc a b hax hbx ▸ hb⟩⟩
  exact ⟨hne⟩

theorem geometricallyIntegral_of_isIntegral_of_isAlgClosed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Over (Sp k)) [IsIntegral X.left],
      LocallyOfFiniteType X.hom → GeometricallyIntegral X.hom := by
  intro k _ _ X _ h
  have h₁ : GeometricallyReduced X.hom :=
    ReducedSubgroup.geometricallyReduced_of_perfectField (k := k) X.hom
  have h₂ : GeometricallyIrreducible X.hom :=
    geometricallyIrreducible_of_isAlgClosed (k := k) X.hom
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible X.hom

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
section
namespace GlobalTheory.LocalQuad

theorem landherrSt_of_hasseNormSt : GlobalTheory.Published.HasseNormSt → GlobalTheory.Published.LandherrSt :=
  fun H => GlobalTheory.Published.landherrSt_of_landherr (landherr_of_hasseNormSt H)

end GlobalTheory.LocalQuad
end

