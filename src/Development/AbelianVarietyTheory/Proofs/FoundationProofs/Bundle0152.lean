import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0146
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisCoboundaryCongZeroModPrimePow
section
open GlobalTheory.K5

namespace GlobalTheory.K5.KernLoc

theorem kern_of (SPAN : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) (ORTH : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
  IsInt p (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt p (c j)) : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt p w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong p k (τ w - w) o → Cong p k o 0 := by
  intro p _ _ Ω _ _ hΩ T τ hτ hτq k N w o hw hwH ho hc
  haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hζalg : IsAlgZp p (T.ζ N) := by
    refine ⟨Polynomial.X ^ (p ^ N) - 1, Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos N) 1, ?_⟩
    simp [(T.prim N).pow_eq_one]
  have hfixζ : ∀ g ∈ Ggeo p Ω, g (T.ζ N) = T.ζ N := fun g hg => hg (T.ζ N) hζalg
  have hτpow : ∀ i : ℕ, (τ ^ i) (T.qq N) = T.ζ N ^ i * T.qq N := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih, hfixζ _ (Subgroup.pow_mem _ hτ i)]
      ring
  have hτi : ∀ i : ℕ, τ ^ i ∈ Ggeo p Ω := fun i => Subgroup.pow_mem _ hτ i

  have hτN : (τ ^ (p ^ N)) w = w := by
    apply hwH
    refine ⟨hτi _, ?_⟩
    show (τ ^ (p ^ N)) (T.qq N) = T.qq N
    rw [hτpow, (T.prim N).pow_eq_one, one_mul]

  obtain ⟨z, hz, hze⟩ := hc
  have hzH : ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z := by
    intro g hg
    have hg1 : g ∈ Ggeo p Ω := hg.1
    have hg2 : g (T.qq N) = T.qq N := hg.2
    have hconj : τ⁻¹ * g * τ ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N) := by
      refine ⟨(Ggeo p Ω).mul_mem ((Ggeo p Ω).mul_mem ((Ggeo p Ω).inv_mem hτ) hg1) hτ, ?_⟩
      show (τ⁻¹ * g * τ) (T.qq N) = T.qq N
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτq, map_mul, hfixζ g hg1, hg2, ← hτq,
        ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hgτw : g (τ w) = τ w := by
      have := hwH _ hconj
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
      have h2 := congrArg τ this
      rwa [← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h2
    have e := congrArg g hze
    rw [map_sub, map_sub, hgτw, hwH g hg, ho g hg1, map_mul, map_pow, map_natCast, hze] at e
    exact (mul_left_cancel₀ (pow_ne_zero k hp0) e).symm
  obtain ⟨c, hcfix, hzc⟩ := SPAN p Ω hΩ T τ hτ hτq N z hzH

  have hsumz : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) z = (p : Ω) ^ N * c 0 := by
    have h1 : ∀ i j : ℕ, (τ ^ i) (c j * T.qq N ^ j) = c j * T.qq N ^ j * (T.ζ N ^ j) ^ i := by
      intro i j
      rw [map_mul, map_pow, hcfix j _ (hτi i), hτpow]
      ring
    rw [hzc]
    simp_rw [map_sum, h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_eq_single 0]
    · simp [mul_comm]
    · intro j hj hj0
      have hj' := Finset.mem_range.1 hj
      have hne : T.ζ N ^ j ≠ 1 := (T.prim N).pow_ne_one_of_pos_of_lt hj0 hj'
      rw [geom_sum_eq hne, ← pow_mul, mul_comm j, pow_mul, (T.prim N).pow_eq_one, one_pow, sub_self,
        zero_div, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (pow_pos (Fact.out : p.Prime).pos N)) h
  have hsumL : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) (τ w - w - o) = -((p : Ω) ^ N * o) := by
    have h1 : ∀ i : ℕ, (τ ^ i) (τ w - w - o) = (τ ^ (i + 1)) w - (τ ^ i) w - o := by
      intro i
      rw [map_sub, map_sub, pow_succ, AlgEquiv.mul_apply, ho _ (hτi i)]
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => (τ ^ i) w), hτN, pow_zero,
      AlgEquiv.one_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have key : -((p : Ω) ^ N * o) = (p : Ω) ^ k * ((p : Ω) ^ N * c 0) := by
    rw [← hsumL, ← hsumz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hze, map_mul, map_pow, map_natCast]
  have hc0 : IsInt p (c 0) := ORTH p Ω hΩ T N c hcfix (hzc ▸ hz) 0 (pow_pos (Fact.out : p.Prime).pos N)
  refine ⟨-c 0, hc0.neg, ?_⟩
  have hpN : (p : Ω) ^ N ≠ 0 := pow_ne_zero N hp0
  apply mul_left_cancel₀ hpN
  linear_combination -key

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt p w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong p k (τ w - w) o → Cong p k o 0 :=
  kern_of GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau GlobalTheory.T.isIntegral_coeffs_of_geometricInvariant_towerParameter_expansion

end GlobalTheory.K5.KernLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem modGrowth_pow_bounds (y : ℝ) (hy : 0 < y) (A : ℕ) :
    max y y⁻¹ ^ A ≤ y ^ A + (y ^ A)⁻¹ ∧ y ^ A + (y ^ A)⁻¹ ≤ 2 * max y y⁻¹ ^ A := by
  rw [← inv_pow]
  have h1 : 0 < y ^ A := pow_pos hy A
  have h2 : 0 < y⁻¹ ^ A := pow_pos (inv_pos.mpr hy) A
  rcases le_total y y⁻¹ with h | h
  · rw [max_eq_right h]
    have : y ^ A ≤ y⁻¹ ^ A := pow_le_pow_left₀ hy.le h A
    constructor <;> linarith
  · rw [max_eq_left h]
    have : y⁻¹ ^ A ≤ y ^ A := pow_le_pow_left₀ (inv_pos.mpr hy).le h A
    constructor <;> linarith

theorem one_le_max_inv (y : ℝ) (hy : 0 < y) : 1 ≤ max y y⁻¹ := by
  rcases le_total 1 y with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hy).mpr h)

theorem mod_of_bound (F : ℍ → ℂ) (C : ℝ) (A : ℕ) (h : ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A) :
    Mod F := by
  refine ⟨max C 0, A, fun τ => ?_⟩
  obtain ⟨b1, _⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hM : 0 ≤ max τ.im τ.im⁻¹ ^ A :=
    pow_nonneg (le_trans zero_le_one (one_le_max_inv _ τ.im_pos)) A
  calc ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := h τ
    _ ≤ max C 0 * max τ.im τ.im⁻¹ ^ A := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    _ ≤ _ := mul_le_mul_of_nonneg_left b1 (le_max_right _ _)

theorem bound_of_mod (F : ℍ → ℂ) (hF : Mod F) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := by
  obtain ⟨C, A, h⟩ := hF
  refine ⟨2 * max C 0, A, by positivity, fun τ => ?_⟩
  obtain ⟨_, b2⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hh : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ :=
    add_nonneg (pow_pos τ.im_pos A).le (inv_pos.mpr (pow_pos τ.im_pos A)).le
  calc ‖F τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := h τ
    _ ≤ max C 0 * (τ.im ^ A + (τ.im ^ A)⁻¹) := mul_le_mul_of_nonneg_right (le_max_left _ _) hh
    _ ≤ max C 0 * (2 * max τ.im τ.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left b2 (le_max_right _ _)
    _ = _ := by ring

theorem mod_add (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ + G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C + D) (A + B) fun τ => ?_
  have hM := one_le_max_inv _ τ.im_pos
  have eA : max τ.im τ.im⁻¹ ^ A ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_right A B)
  have eB : max τ.im τ.im⁻¹ ^ B ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_left B A)
  calc ‖F τ + G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := norm_add_le _ _
    _ ≤ C * max τ.im τ.im⁻¹ ^ A + D * max τ.im τ.im⁻¹ ^ B := add_le_add (h1 τ) (h2 τ)
    _ ≤ C * max τ.im τ.im⁻¹ ^ (A + B) + D * max τ.im τ.im⁻¹ ^ (A + B) :=
        add_le_add (mul_le_mul_of_nonneg_left eA hC) (mul_le_mul_of_nonneg_left eB hD)
    _ = _ := by ring

theorem mod_mul (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ * G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C * D) (A + B) fun τ => ?_
  have hM := le_trans zero_le_one (one_le_max_inv _ τ.im_pos)
  calc ‖F τ * G τ‖ = ‖F τ‖ * ‖G τ‖ := norm_mul _ _
    _ ≤ (C * max τ.im τ.im⁻¹ ^ A) * (D * max τ.im τ.im⁻¹ ^ B) :=
        mul_le_mul (h1 τ) (h2 τ) (norm_nonneg _) (mul_nonneg hC (pow_nonneg hM A))
    _ = _ := by ring

theorem mod_const (c : ℂ) : Mod fun _ => c :=
  mod_of_bound _ ‖c‖ 0 fun τ => by simp

theorem im_slz_arg (δ : M2) (hc : δ 1 0 = 0) (τ : ℍ) :
    (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im
      = (δ 0 0 : ℝ) / (δ 1 1 : ℝ) * τ.im := by
  rw [hc]
  simp [Complex.div_im]
  rcases eq_or_ne ((δ 1 1 : ℤ) : ℝ) 0 with h | h
  · simp [h]
  · field_simp

theorem max_inv_mul_le (r y : ℝ) (hr : 0 < r) (hy : 0 < y) :
    max (r * y) (r * y)⁻¹ ≤ max r r⁻¹ * max y y⁻¹ := by
  have h1 := one_le_max_inv r hr
  have h2 := one_le_max_inv y hy
  rw [mul_inv]
  apply max_le
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) hy.le (by linarith)
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (inv_pos.mpr hy).le (by linarith)

theorem mod_slz (F : ℍ → ℂ) (k : ℕ) (δ : M2) (hdet : 0 < δ.det) (hc : δ 1 0 = 0) (hF : Mod F) :
    Mod (slz k δ F) := by
  obtain ⟨C, A, hC0, hC⟩ := bound_of_mod F hF
  have hdet' : δ.det = δ 0 0 * δ 1 1 := by rw [Matrix.det_fin_two, hc]; ring
  have had : (0 : ℝ) < (δ 0 0 : ℝ) * (δ 1 1 : ℝ) := by
    have : (0 : ℤ) < δ 0 0 * δ 1 1 := hdet' ▸ hdet
    exact_mod_cast this
  have hd : (δ 1 1 : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at had; exact lt_irrefl _ had
  have hrpos : (0 : ℝ) < (δ 0 0 : ℝ) / (δ 1 1 : ℝ) := by
    have : (δ 0 0 : ℝ) / (δ 1 1 : ℝ) = (δ 0 0 : ℝ) * δ 1 1 / ((δ 1 1 : ℝ) ^ 2) := by
      field_simp
    rw [this]; exact div_pos had (by positivity)
  set r : ℝ := (δ 0 0 : ℝ) / (δ 1 1 : ℝ) with hr
  set K : ℝ := ‖((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹‖ with hK
  set R : ℝ := max r r⁻¹ with hR
  have hR1 : 1 ≤ R := one_le_max_inv r hrpos
  refine mod_of_bound _ (K * (C * R ^ A)) A fun τ => ?_
  have him := im_slz_arg δ hc τ
  rw [← hr] at him
  have hz : 0 < (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im := by
    rw [him]; exact mul_pos hrpos τ.im_pos
  set w : ℍ := ofComplex ((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ))) with hw
  have hwim : w.im = r * τ.im := by
    rw [hw, ofComplex_apply_of_im_pos hz]; exact him
  have hMw : max w.im w.im⁻¹ ^ A ≤ R ^ A * max τ.im τ.im⁻¹ ^ A := by
    rw [← mul_pow, hwim]
    exact pow_le_pow_left₀ (le_trans zero_le_one (one_le_max_inv _ (mul_pos hrpos τ.im_pos)))
      (max_inv_mul_le r τ.im hrpos τ.im_pos) A
  have hslz : slz k δ F τ = (((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹) * F w := by
    rw [slz, hw]; simp [hc]
  rw [hslz, norm_mul, ← hK]
  have hK0 : 0 ≤ K := norm_nonneg _
  calc K * ‖F w‖ ≤ K * (C * max w.im w.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left (hC w) hK0
    _ ≤ K * (C * (R ^ A * max τ.im τ.im⁻¹ ^ A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMw hC0) hK0
    _ = _ := by ring

theorem mod_algebra : (∀ F G : ℍ → ℂ, Mod F → Mod G → Mod (fun τ => F τ + G τ) ∧ Mod (fun τ => F τ * G τ)) ∧ (∀ c : ℂ, Mod fun _ => c) ∧ (∀ (F : ℍ → ℂ) (k : ℕ) (δ : M2), 0 < δ.det → δ 1 0 = 0 → Mod F → Mod (slz k δ F)) :=
  ⟨fun F G hF hG => ⟨mod_add F G hF hG, mod_mul F G hF hG⟩, mod_const,
    fun F k δ hdet hc hF => mod_slz F k δ hdet hc hF⟩

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrow
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma pow_succ_le_factorial_mul_choose (n A : ℕ) :
    ((n : ℝ) + 1) ^ A ≤ (A.factorial : ℝ) * ((n + A).choose A : ℕ) := by
  have h := Nat.pow_succ_le_ascFactorial (n + 1) A
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at h
  exact_mod_cast h

lemma norm_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-2 * π * τ.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma one_sub_exp_inv_le (y : ℝ) (hy : 0 < y) :
    (1 - Real.exp (-2 * π * y))⁻¹ ≤ 1 + y⁻¹ := by
  set t := 2 * π * y with ht
  have htpos : 0 < t := by positivity
  have hty : y ≤ t := by
    have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    nlinarith
  have h1 : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp t])
  have h2 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have : t / (1 + t) = 1 - (1 + t)⁻¹ := by field_simp; ring
    linarith
  have h3 : (1 - Real.exp (-t))⁻¹ ≤ (t / (1 + t))⁻¹ := inv_anti₀ (by positivity) h2
  have h4 : (t / (1 + t))⁻¹ = 1 + t⁻¹ := by field_simp; ring
  have h5 : t⁻¹ ≤ y⁻¹ := inv_anti₀ hy hty
  have : -2 * π * y = -t := by rw [ht]; ring
  rw [this]
  linarith

lemma one_add_inv_pow_le (y : ℝ) (hy : 0 < y) (B : ℕ) :
    (1 + y⁻¹) ^ B ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
  rcases le_or_gt 1 y with h | h
  · have : 1 + y⁻¹ ≤ 2 * y := by
      have : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * y ^ B := mul_pow _ _ _
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ (y ^ B)⁻¹ := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]
  · have : 1 + y⁻¹ ≤ 2 * y⁻¹ := by
      have : 1 ≤ y⁻¹ := one_le_inv₀ hy |>.mpr h.le
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y⁻¹) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * (y ^ B)⁻¹ := by rw [mul_pow, inv_pow]
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ y ^ B := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]

theorem mod_qs_of_polyB : ∀ a : ℕ → ℂ, PolyB a → Mod (qs a) := by
  intro a ⟨C, A, hC⟩
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C * A.factorial * 2 ^ (A + 1), A + 1, fun τ => ?_⟩
  set y := τ.im
  have hy : 0 < y := τ.im_pos
  set r := Real.exp (-2 * π * y) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    have := Real.pi_pos
    calc r < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  have hS := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) A hrn
  have hbound : ∀ n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by
    intro n
    rw [norm_mul, norm_qterm]
    have h1 := hC n
    have h2 := pow_succ_le_factorial_mul_choose n A
    calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ C * ((A.factorial : ℝ) * ((n + A).choose A : ℕ)) * r ^ n := by
          gcongr
      _ = (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by ring
  have hsum2 : HasSum (fun n : ℕ => (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n))
      ((C * A.factorial) * (1 / (1 - r) ^ (A + 1))) := hS.mul_left _
  have hsumm : Summable (fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsum2.summable
  have key : ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := by
    unfold qs
    calc ‖∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)‖
        ≤ ∑' n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := norm_tsum_le_tsum_norm hsumm
      _ ≤ ∑' n : ℕ, (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) :=
          hsumm.tsum_le_tsum hbound hsum2.summable
      _ = _ := hsum2.tsum_eq
  have hinv : 1 / (1 - r) ^ (A + 1) ≤ 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by
    rw [one_div, ← inv_pow]
    calc ((1 - r)⁻¹) ^ (A + 1) ≤ (1 + y⁻¹) ^ (A + 1) :=
          pow_le_pow_left₀ (by have : 0 < 1 - r := by linarith
                               positivity) (one_sub_exp_inv_le y hy) _
      _ ≤ _ := one_add_inv_pow_le y hy _
  calc ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := key
    _ ≤ (C * A.factorial) * (2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = C * A.factorial * 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverOfIntegralInvariant
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

private theorem gamma_le_of_dvd' {N N' : ℕ} (hd : N ∣ N') :
    CongruenceSubgroup.Gamma N' ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ x : ℤ, (x : ZMod N) = ZMod.castHom hd (ZMod N) (x : ZMod N') := fun x => by
    rw [map_intCast]
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, h1, map_one]
  · rw [key, h2, map_zero]
  · rw [key, h3, map_zero]
  · rw [key, h4, map_one]

theorem exists_common_lv {E : Subring ℂ} {n : ℕ} (M : ℕ) (hM : 0 < M) (r : Fin n → ℍ → ℂ)
    (hr : ∀ j, InR E (r j)) : ∃ N w : ℕ, 0 < N ∧ M ∣ N ∧ ∀ j, Lv E N w (r j) := by
  choose Nj wj hNj hLv using hr
  have hpos : 0 < M * ∏ j, Nj j := Nat.mul_pos hM (Finset.prod_pos fun j _ => hNj j)
  refine ⟨M * ∏ j, Nj j, ∑ j, wj j, hpos, dvd_mul_right _ _, fun j => ?_⟩
  exact GlobalTheory.T.lv_mono_of_dvd_of_le E (Nj j) _ (wj j) _ (r j) hpos
    (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) M)
    (Finset.single_le_sum (fun i _ => Nat.zero_le (wj i)) (Finset.mem_univ j)) (hLv j)

theorem mdifferentiable_DD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) DD := CuspForm.discriminant.holo'

theorem mdifferentiable_comp_smul {h : ℍ → ℂ} (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun τ => h (γ • τ) := by
  have e : (fun τ => h (γ • τ)) = h ∣[(0 : ℤ)] γ := by
    funext τ
    rw [ModularForm.SL_slash_apply]
    simp
  rw [e]
  exact hh.slash 0 _

theorem DD_vadd (N : ℕ) (τ : ℍ) : DD ((N : ℝ) +ᵥ τ) = DD τ := by
  have hT : (ModularGroup.T ^ (N : ℤ)) • τ = (N : ℝ) +ᵥ τ := by
    rw [UpperHalfPlane.modular_T_zpow_smul]; simp
  have hden : UpperHalfPlane.denom (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) τ = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
  rw [← hT, ReciprocityTheory.ChartRestriction.L1.DD_smul, hden, one_pow, one_mul]

theorem comp_smul_vadd {N : ℕ} {h : ℍ → ℂ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, h (γ • τ) = h τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    h (γ • ((N : ℝ) +ᵥ τ)) = h (γ • τ) := by
  have hT : (ModularGroup.T ^ (N : ℤ)) • τ = (N : ℝ) +ᵥ τ := by
    rw [UpperHalfPlane.modular_T_zpow_smul]; simp
  have h1 : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have h2 := (CongruenceSubgroup.Gamma_normal N).conj_mem _ h1 γ
  rw [← hT, ← mul_smul,
    show γ * ModularGroup.T ^ (N : ℤ) = (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) * γ by group, mul_smul]
  exact hinv _ h2 _

theorem inR_of_integral : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (h : ℍ → ℂ)
    (r : Fin n → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, h (γ • τ) = h τ) → (∀ j, InR ε.range (r j)) →
    (∀ τ, h τ ^ n + ∑ j, r j τ * h τ ^ (j : ℕ) = 0) → InR ε.range h := by
  intro Ω _ _ ε M n h r hM hh hinv hr heq
  obtain ⟨N, w, hN, hMN, hlv⟩ := exists_common_lv M hM r hr
  have hinvN : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, h (γ • τ) = h τ :=
    fun γ hγ τ => hinv γ (gamma_le_of_dvd' hMN hγ) τ
  refine ⟨N, w, hN, hinvN, fun γ => ?_⟩
  have hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => DD τ ^ w * h (γ • τ)) :=
    (mdifferentiable_DD.pow w).mul (mdifferentiable_comp_smul hh γ)
  have hper : ∀ τ : ℍ, DD ((N : ℝ) +ᵥ τ) ^ w * h (γ • ((N : ℝ) +ᵥ τ)) = DD τ ^ w * h (γ • τ) := by
    intro τ; rw [DD_vadd, comp_smul_vadd hinvN γ τ]
  let s : Fin n → ℍ → ℂ := fun j τ => DD τ ^ (w * (n - (j : ℕ))) * r j (γ • τ)
  have hs : ∀ j, QAll (· ∈ ε.range) N (s j) := by
    intro j
    have h1 := (hlv j).2 γ
    have h2 : QAll (· ∈ ε.range) N fun τ => DD τ ^ (w * (n - 1 - (j : ℕ))) :=
      QAllSubring.pow _ (eis_qAll N hN DD (Or.inr (Or.inr rfl)) ε.range)
    refine (congrArg (QAll (· ∈ ε.range) N) (funext fun τ => ?_)).mp (QAllSubring.mul h2 h1)
    have hj := j.isLt
    have e : w * (n - 1 - (j : ℕ)) + w = w * (n - (j : ℕ)) := by
      rw [← Nat.mul_succ]; congr 1; omega
    simp only [s]
    rw [← mul_assoc, ← pow_add, e]
  have heqH : ∀ τ, (DD τ ^ w * h (γ • τ)) ^ n +
      ∑ j, s j τ * (DD τ ^ w * h (γ • τ)) ^ (j : ℕ) = 0 := by
    intro τ
    have e := heq (γ • τ)
    calc _ = DD τ ^ (w * n) * (h (γ • τ) ^ n + ∑ j, r j (γ • τ) * h (γ • τ) ^ (j : ℕ)) := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          · rw [mul_pow, pow_mul]
          · refine Finset.sum_congr rfl fun j _ => ?_
            have hj := j.isLt
            have e2 : w * n = w * (n - (j : ℕ)) + w * (j : ℕ) := by
              rw [← Nat.mul_add]; congr 1; omega
            simp only [s]
            rw [e2, pow_add, mul_pow, ← pow_mul]; ring
      _ = 0 := by rw [e, mul_zero]
  exact GlobalTheory.T.qExpansionAllCoeffs_range_of_monic_root Ω ε N n _ s hN hH hper hs heqH

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormUniformiserEqInvAbsNorm
section
open scoped NNReal
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_uniformiser_eq_inv_absNorm :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : v.adicCompletion F),
      Formalism.UG.IsUnifV F v ϖ → ‖ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ := by
  intro F _ _ v ϖ h
  apply NNReal.eq
  rw [coe_nnnorm, FinitePlace.norm_def]
  unfold Formalism.UG.IsUnifV at h
  rw [h]
  have hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  rw [WithZeroMulInt.toNNReal_neg_apply _ hne]
  simp only [WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelGLengthConjStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selG_length_eq_of_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (P : LocPrime l) (nb : ∀ w, w ∈ Formalism.BasicNotions.placesOver E l → LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) (A.1 w)) O) (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (k : ℕ) (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : GL (Fin k) O), (∀ g, M' g * (U : Matrix (Fin k) (Fin k) O) = (U : Matrix (Fin k) (Fin k) O) * M g) → Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M) = Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M') := by
  first | exact @GlobalTheory.SelConj.selG_length_conj | exact GlobalTheory.SelConj.selG_length_conj | (intros; apply GlobalTheory.SelConj.selG_length_conj <;> assumption)
end

