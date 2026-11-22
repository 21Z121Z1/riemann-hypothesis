import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0090
import GroundTheory.GlobalFields.TateThesis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueIdempotent
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.AzumayaResidue

theorem isSimpleRing_of_isAzumaya (k B : Type) [Field k] [Ring B] [Algebra k B]
    [IsAzumaya k B] [Nontrivial B] : IsSimpleRing B := by
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases h : I = ⊥
  · exact Or.inl h
  right
  obtain ⟨z, hzI, hz0⟩ : ∃ z ∈ I, z ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h
    ext x
    rw [TwoSidedIdeal.mem_bot]
    exact ⟨hc x, fun hx => hx ▸ I.zero_mem⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k B, φ z ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz0 ((Module.forall_dual_apply_eq_zero_iff k z).1 hc)
  let f : B →ₗ[k] B := (φ z)⁻¹ • φ.smulRight (1 : B)
  have hf : f z = 1 := by
    simp [f, hφ]
  obtain ⟨t, ht⟩ := (IsAzumaya.bij (R := k) (A := B)).2 f
  have key : ∀ t : B ⊗[k] Bᵐᵒᵖ, AlgHom.mulLeftRight k B t z ∈ I := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [I.zero_mem]
    | tmul a b =>
      rw [AlgHom.mulLeftRight_apply]
      exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hzI)
    | add x y hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact I.add_mem hx hy
  rw [← TwoSidedIdeal.one_mem_iff, ← hf, ← ht]
  exact key t

theorem exists_rankOne_idempotent (k B : Type) [Field k] [Finite k] [Ring B] [Algebra k B]
    [IsAzumaya k B] [Nontrivial B] :
    ∃ x : B, x * x = x ∧ (∀ y : B, ∃ c : k, x * y * x = c • x) ∧
      ∃ (N : ℕ) (a b : Fin N → B), ∑ i, a i * x * b i = 1 := by
  classical
  haveI : IsSimpleRing B := isSimpleRing_of_isAzumaya k B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B
  haveI : Finite D := Module.finite_of_finite k
  have hcomm : ∀ a b : D, a * b = b * a := (littleWedderburn D).mul_comm
  have hD : ∀ d : D, ∃ c : k, algebraMap k D c = d := by
    intro d
    have hcen : e.symm (Matrix.scalar (Fin n) d) ∈ Subalgebra.center k B := by
      rw [Subalgebra.mem_center_iff]
      intro y
      apply e.injective
      rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
      ext i j
      simp [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hcomm]
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (Algebra.IsCentral.out hcen)
    refine ⟨c, ?_⟩
    have h2 := congrArg e hc
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes] at h2
    have h3 := congrFun (congrFun h2 ⟨0, Nat.pos_of_ne_zero hn.out⟩) ⟨0, Nat.pos_of_ne_zero hn.out⟩
    simpa [Matrix.algebraMap_eq_diagonal] using h3
  let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn.out⟩
  let E : Matrix (Fin n) (Fin n) D := Matrix.single i₀ i₀ 1
  refine ⟨e.symm E, ?_, ?_, n, fun i => e.symm (Matrix.single i i₀ 1),
    fun i => e.symm (Matrix.single i₀ i 1), ?_⟩
  · rw [← map_mul]
    simp [E, Matrix.single_mul_single_same]
  · intro y
    obtain ⟨c, hc⟩ := hD (e y i₀ i₀)
    refine ⟨c, ?_⟩
    apply e.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, map_smul, AlgEquiv.apply_symm_apply]
    simp only [E, Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single, ← hc]
    rw [Algebra.algebraMap_eq_smul_one]
  · apply e.injective
    simp [E, map_sum, Matrix.single_mul_single_same, Matrix.sum_single_one]

end GlobalTheory.AzumayaResidue

namespace GlobalTheory.AzumayaResidue

theorem mem_smul_top_of_one_tmul_eq_zero (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type)
    [Ring Λ] [Algebra A Λ] (y : Λ) (h : (1 : ResidueField A) ⊗ₜ[A] y = 0) :
    y ∈ (maximalIdeal A) • (⊤ : Submodule A Λ) := by
  have := TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := Λ) (maximalIdeal A) y
  rw [← Submodule.Quotient.mk_eq_zero, ← this]
  exact (congrArg (TensorProduct.quotTensorEquivQuotSMul Λ (maximalIdeal A)) h).trans (map_zero _)

theorem one_tmul_surjective (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type)
    [Ring Λ] [Algebra A Λ] (z : ResidueField A ⊗[A] Λ) : ∃ y : Λ, (1 : ResidueField A) ⊗ₜ[A] y = z := by
  first
  | exact @_root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq
  | exact _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq
  | (apply _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq ..)

theorem exists_residue_idempotent : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] [Nontrivial Λ], ∃ x : Λ, x * x - x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) ∧ (∀ y : Λ, ∃ c : A, x * y * x - c • x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) ∧ ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * x * b i - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) := by
  intro A _ _ _ Λ _ _ _ _ _
  classical
  let k := ResidueField A
  haveI : IsAzumaya k (k ⊗[A] Λ) := GlobalTheory.isAzumaya_baseChange A k Λ
  haveI : Nontrivial (k ⊗[A] Λ) := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    have : (0 : k) = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (α := k ⊗[A] Λ) fun _ => Subsingleton.elim _ _
    exact zero_ne_one this
  let π : Λ →ₐ[A] k ⊗[A] Λ := Algebra.TensorProduct.includeRight
  have hπ : ∀ y, π y = (1 : k) ⊗ₜ[A] y := fun y => rfl
  have hker : ∀ y, π y = 0 → y ∈ (maximalIdeal A) • (⊤ : Submodule A Λ) := fun y h =>
    mem_smul_top_of_one_tmul_eq_zero A Λ y ((hπ y).symm.trans h)
  have hsurj : ∀ z, ∃ y, π y = z := one_tmul_surjective A Λ
  obtain ⟨xb, hxx, hxy, N, ab, bb, hsum⟩ := exists_rankOne_idempotent k (k ⊗[A] Λ)
  obtain ⟨x, rfl⟩ := hsurj xb
  choose a ha using fun i => hsurj (ab i)
  choose b hb using fun i => hsurj (bb i)
  refine ⟨x, hker _ ?_, fun y => ?_, N, a, b, hker _ ?_⟩
  · rw [map_sub, map_mul, hxx, sub_self]
  · obtain ⟨cb, hc⟩ := hxy (π y)
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective cb
    refine ⟨c, hker _ ?_⟩
    rw [map_sub, map_mul, map_mul, hc, map_smul, ← ResidueField.algebraMap_eq,
      algebraMap_smul, sub_self]
  · simp only [map_sub, map_sum, map_mul, map_one, ha, hb, hsum, sub_self]

end GlobalTheory.AzumayaResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootOfUnitZeroDimensional
section
namespace GlobalTheory

theorem pow_idempotent_combination {R : Type} [CommRing R] {g : R} (hg : IsIdempotentElem g)
    (a b : R) (n : ℕ) : (g * a + (1 - g) * b) ^ n = g * a ^ n + (1 - g) * b ^ n := by
  induction n with
  | zero => ring
  | succ n ih =>
    rw [pow_succ, ih]
    linear_combination (a ^ n * a + b ^ n * b - a ^ n * b - b ^ n * a) * hg.eq

theorem exists_unit_pow_eq_of_krullDimLE_zero : ∀ (R : Type) [CommRing R] [Ring.KrullDimLE 0 R]
    (q : ℕ), 0 < q → IsUnit (q : R) → ∀ u : Rˣ,
    (∀ m : Ideal R, m.IsMaximal → ∃ x : R, x ^ q - (u : R) ∈ m) → ∃ v : Rˣ, v ^ q = u := by
  intro R _ _ q hq hqu u hloc
  have hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal := fun P hP => hP.isMaximal'
  let S : Set R := {g | IsIdempotentElem g ∧ ∃ x : R, IsNilpotent (g * (x ^ q - u))}
  have hjoin : ∀ g ∈ S, ∀ h ∈ S, g + h - g * h ∈ S := by
    rintro g ⟨hg, x, hx⟩ h ⟨hh, z, hz⟩
    refine ⟨?_, g * x + (1 - g) * z, ?_⟩
    · show (g + h - g * h) * (g + h - g * h) = g + h - g * h
      linear_combination (1 - 2 * h + h ^ 2) * hg.eq + (1 - g) * hh.eq
    · have key : (g + h - g * h) * ((g * x + (1 - g) * z) ^ q - u)
          = g * (x ^ q - u) + (1 - g) * (h * (z ^ q - u)) := by
        rw [pow_idempotent_combination hg]
        linear_combination (x ^ q - z ^ q - h * x ^ q + h * z ^ q) * hg.eq
      rw [key]
      exact Commute.isNilpotent_add (Commute.all _ _) hx ((Commute.all _ _).isNilpotent_mul_left (show IsNilpotent (h * (z ^ q - u)) from hz))
  have hcover : ∀ m : Ideal R, m.IsMaximal → ∃ g ∈ S, g ∉ m := by
    intro m hm
    obtain ⟨x, hx⟩ := hloc m hm
    obtain ⟨e, b, he, hab, hep⟩ := exists_isIdempotentElem_mul_of_forall_isMaximal hR (x ^ q - u)
    refine ⟨1 - e, ⟨he.one_sub, x, ?_⟩, ?_⟩
    · rw [nilpotent_iff_mem_prime]
      intro p hp
      by_cases ha : x ^ q - (u : R) ∈ p
      · exact p.mul_mem_left _ ha
      · have hep' := hep p hp ha
        have h0 : e * (1 - e) ∈ p := by
          have : e * (1 - e) = 0 := by linear_combination -he.eq
          rw [this]; exact p.zero_mem
        rcases hp.mem_or_mem h0 with h | h
        · exact absurd h hep'
        · exact p.mul_mem_right _ h
    · intro h
      have hem : e ∈ m := hab ▸ m.mul_mem_right b hx
      apply hm.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using m.add_mem h hem
  have hspan : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgS, hgm⟩ := hcover m hm
    exact hgm (hle (Ideal.subset_span hgS))
  have hfin : ∀ T : Finset R, (↑T ⊆ S) → ∃ G ∈ S, ∀ g ∈ T, g * G = g := by
    classical
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, ⟨IsIdempotentElem.zero, 0, by simp⟩, by simp⟩
    | insert a T ha ih =>
      intro hT
      have haS : a ∈ S := hT (by simp)
      obtain ⟨G, hG, hGT⟩ := ih (fun y hy => hT (by simp [hy]))
      refine ⟨a + G - a * G, hjoin a haS G hG, ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · linear_combination (1 - G) * haS.1.eq
      · have := hGT g hg
        linear_combination (1 - a) * this
  have h1 : (1 : R) ∈ Ideal.span S := by rw [hspan]; trivial
  obtain ⟨n, f, g, hf⟩ := Submodule.mem_span_set'.mp h1
  classical
  obtain ⟨G, hG, hGT⟩ := hfin (Finset.univ.image fun i => (g i : R)) (by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact (g i).2)
  have hG1 : G = 1 := by
    have : (∑ i, f i • (g i : R)) * G = ∑ i, f i • (g i : R) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, hGT _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    rw [hf, one_mul] at this
    exact this
  obtain ⟨x, hx⟩ := hG.2
  rw [hG1, one_mul] at hx
  have hxq : IsUnit (x ^ q) := by
    have := hx.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)
    simpa using this
  have hxu : IsUnit x := (isUnit_pow_iff hq.ne').mp hxq
  let P : Polynomial R := Polynomial.X ^ q - Polynomial.C (u : R)
  have hP : ∀ y : R, Polynomial.aeval y P = y ^ q - u := by
    intro y; simp [P]
  have hdP : Polynomial.aeval x (Polynomial.derivative P) = (q : R) * x ^ (q - 1) := by
    simp [P, Polynomial.derivative_X_pow]
  obtain ⟨v, ⟨-, hv⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (P := P) (x := x)
    (by rw [hP]; exact hx) (by rw [hdP]; exact hqu.mul (hxu.pow _))
  rw [hP, sub_eq_zero] at hv
  have hvu : IsUnit v := (isUnit_pow_iff hq.ne').mp (hv ▸ u.isUnit)
  exact ⟨hvu.unit, Units.ext (by simp [hv])⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzGaussWidth
section
open FourierTransform MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_schwartz_gauss_width (c : ℝ) (hc : 0 < c) :
    ∃ g : SchwartzMap E ℂ, ∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  set t : ℝ := Real.sqrt (c / Real.pi) with ht_def
  have ht : t ≠ 0 := (Real.sqrt_pos.2 (div_pos hc Real.pi_pos)).ne'
  have ht2 : t ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc Real.pi_pos).le
  let e : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (GroundTheory.Global.gaussianSchwartz E), fun y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
  congr 1
  have hey : e y = t • y := rfl
  rw [hey, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ht2]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

theorem mem_of_smul {M : Submodule ℂ (SchwartzMap E ℂ)} (c : ℝ) (K : ℂ) (hK : K ≠ 0)
    (u : SchwartzMap E ℂ) (hu : ∀ y, u y = K * Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)))
    (huM : u ∈ M) :
    ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro g hg
  have : g = K⁻¹ • u := by
    ext y
    rw [SchwartzMap.smul_apply, hu, hg, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  rw [this]
  exact M.smul_mem _ huM

variable [MeasurableSpace E] [BorelSpace E]

theorem integral_gauss_mul_gauss (s c : ℝ) (hs : 0 < s) (hc : 0 < c) (y : E) :
    ∫ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (-(((s * c / (s + c)) * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  have hsc : 0 < s + c := by linarith
  have key : ∀ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((s + c : ℝ) : ℂ) * (‖a‖ : ℂ) ^ 2 + ((2 * c : ℝ) : ℂ) * ((inner ℝ y a : ℝ) : ℂ)) *
        Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [norm_sub_sq_real]
    push_cast
    ring
  simp_rw [key]
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (by simpa using hsc) _ y, mul_assoc, ← Complex.exp_add]
  congr 2
  have h1 : ((s + c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  push_cast at h1 ⊢
  field_simp
  ring

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def HasWidth (M : Submodule ℂ (SchwartzMap E ℂ)) (c : ℝ) : Prop :=
  ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M

def ConvStable (M : Submodule ℂ (SchwartzMap E ℂ)) : Prop :=
  ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
        Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) → u ∈ M

theorem cpow_ne_zero_of_pos (r : ℝ) (hr : 0 < r) (z : ℂ) : ((r : ℂ)) ^ z ≠ 0 := by
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  exact (Complex.ofReal_ne_zero.2 hr.ne') h.1

theorem hasWidth_of_lt {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) (c' : ℝ) (hc' : 0 < c') (hlt : c' < c) : HasWidth M c' := by
  set s : ℝ := c * c' / (c - c') with hs_def
  have hcc : 0 < c - c' := by linarith
  have hs : 0 < s := div_pos (mul_pos hc hc') hcc
  have hsc : s * c / (s + c) = c' := by
    rw [hs_def]; field_simp; ring
  obtain ⟨h, hh⟩ := exists_schwartz_gauss_width (E := E) (s / 2) (by linarith)
  obtain ⟨g', hg'⟩ := exists_schwartz_gauss_width (E := E) c' hc'
  set K : ℂ := ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / ((s + c : ℝ) : ℂ) = ((Real.pi / (s + c) : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos (by linarith)) _
  have huM : K • g' ∈ M := hconv (s / 2) c (by linarith) hc hP h (K • g') (fun y => by
    rw [SchwartzMap.smul_apply, smul_eq_mul, hg', ← hsc, ← integral_gauss_mul_gauss s c hs hc y]
    congr 1
    funext a
    rw [hh]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring)
  exact mem_of_smul c' K hK (K • g') (fun y => by rw [SchwartzMap.smul_apply, smul_eq_mul, hg']) huM

theorem hasWidth_fourier {M : Submodule ℂ (SchwartzMap E ℂ)} (hF : ∀ f ∈ M, 𝓕 f ∈ M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) : HasWidth M (Real.pi ^ 2 / c) := by
  obtain ⟨g, hg⟩ := exists_schwartz_gauss_width (E := E) c hc
  set K : ℂ := ((Real.pi : ℂ) / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / (c : ℂ) = ((Real.pi / c : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos hc) _
  refine mem_of_smul (Real.pi ^ 2 / c) K hK (𝓕 g) (fun w => ?_) (hF g (hP g hg))
  have hfun : (g : E → ℂ) = fun v => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v; rw [hg]; push_cast; ring_nf
  rw [SchwartzMap.fourier_coe, hfun, fourier_gaussian_innerProductSpace (by simpa using hc)]
  congr 2
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

theorem hasWidth_all {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M)
    (hF : ∀ f ∈ M, 𝓕 f ∈ M) (hπ : HasWidth M Real.pi) (c : ℝ) (hc : 0 < c) : HasWidth M c := by
  rcases lt_trichotomy c Real.pi with hlt | heq | hgt
  · exact hasWidth_of_lt hconv Real.pi Real.pi_pos hπ c hc hlt
  · exact heq ▸ hπ
  · have hc' : 0 < Real.pi ^ 2 / c := by positivity
    have hlt : Real.pi ^ 2 / c < Real.pi := by
      rw [div_lt_iff₀ hc]; nlinarith [Real.pi_pos]
    have h1 := hasWidth_fourier hF _ hc' (hasWidth_of_lt hconv Real.pi Real.pi_pos hπ _ hc' hlt)
    have : Real.pi ^ 2 / (Real.pi ^ 2 / c) = c := by
      have := Real.pi_pos.ne'; field_simp
    rwa [this] at h1

theorem hasWidth_pi {M : Submodule ℂ (SchwartzMap E ℂ)} (G : SchwartzMap E ℂ)
    (hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) (hGM : G ∈ M) :
    HasWidth M Real.pi := by
  intro g hg
  have : g = G := by ext y; rw [hg, hG]
  rwa [this]

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

theorem all_widths_of_conv
    (hconvAll : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
      ∀ (b c : ℝ), 0 < b → 0 < c →
      (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
      ∀ (h u : SchwartzMap E ℂ),
        (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
          Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
        u ∈ M) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro E _ _ _ _ _ M hM hℓ hF G hG hGM c hc g hg
  exact hasWidth_all (fun b c' hb hc' hP h u hu => hconvAll E M hM hℓ b c' hb hc' hP h u hu) hF
    (hasWidth_pi G hG hGM) c hc g hg

end GlobalTheory.GaussWidths
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfAdjointEndoRelatingHermitianFormsStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by
  first | exact @GlobalTheory.herm_gamma | exact GlobalTheory.herm_gamma | (intros; apply GlobalTheory.herm_gamma <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparabilityElementOfTraceNondegenerateStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' : ∀ (A : Type) [Ring A] [Module.Free ℤ A] [Module.Finite ℤ A], (∀ x : A, (∀ y : A, LinearMap.trace ℤ A (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0) → ∃ (N : ℤ) (k : ℕ) (x y : Fin k → A), N ≠ 0 ∧ ∑ j, x j * y j = (N : A) ∧ ∀ c : A, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c) := by
  first | exact @GlobalTheory.exists_separability_element_of_trace_nondegenerate | exact GlobalTheory.exists_separability_element_of_trace_nondegenerate | (intros; apply GlobalTheory.exists_separability_element_of_trace_nondegenerate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingBasicOpenFunctionsStatement
section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_basicOpen_functions' : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  first | exact @GlobalTheory.exists_separating_basicOpen_functions | exact GlobalTheory.exists_separating_basicOpen_functions | (intros; apply GlobalTheory.exists_separating_basicOpen_functions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingElementRingHomModuleFiniteIntStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_element_ringHom_moduleFinite_int : ∀ (k : Type) [Field k] (C : Type) [CommRing C] [Module.Finite ℤ C] (S : Finset (C →+* k)) (χ₀ : C →+* k), ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  first | (exact @GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (exact GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (intros; apply GlobalTheory.ringHom_exists_sep_of_moduleFinite_int  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFockFormOfComplexStructureStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_fock_form_of_complex_structure : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), (∀ x y, β x y = β y x) → (∀ w, J (J w) = -w) →
    (∀ w w', β (J w).1 (J w').2 - β (J w').1 (J w).2 = β w.1 w'.2 - β w'.1 w.2) →
    (∀ w, w ≠ 0 → 0 < β w.1 (J w).2 - β (J w).1 w.2) →
    ∃ (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, Q x y = Q y x) ∧
      ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) = Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := by
  first | exact @GlobalTheory.siegel_fock_exists | exact GlobalTheory.siegel_fock_exists | (intros; apply GlobalTheory.siegel_fock_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemRangeOfSurjectiveLocalizedMapStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map : ∀ (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) → ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  first | exact @GlobalTheory.exists_smul_mem_range_of_surjective_localization_map | exact GlobalTheory.exists_smul_mem_range_of_surjective_localization_map | (intros; apply GlobalTheory.exists_smul_mem_range_of_surjective_localization_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquarePresentationOfTowerStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_presentation_of_tower : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  first | exact @GlobalTheory.SquareTower.tower | exact GlobalTheory.SquareTower.tower | (intros; apply GlobalTheory.SquareTower.tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkRetractionOfSmallLiftingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_retraction_of_small_lifting : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → ∀ (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))], Function.Surjective (f.residueFieldMap x).hom → ∀ n : ℕ, ∃ ψ : X.presheaf.stalk x →+* Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1), ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ := by
  first | exact @GlobalTheory.SmallLift.exists_retraction | exact GlobalTheory.SmallLift.exists_retraction | (intros; apply GlobalTheory.SmallLift.exists_retraction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardBasisExtensionDetNeZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_basis_extension_det_ne_zero : ∀ {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K), LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧ (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by
  first | exact @GlobalTheory.extend_linearIndependent_rows_by_standard_basis | exact GlobalTheory.extend_linearIndependent_rows_by_standard_basis | (intros; apply GlobalTheory.extend_linearIndependent_rows_by_standard_basis <;> assumption)
end

