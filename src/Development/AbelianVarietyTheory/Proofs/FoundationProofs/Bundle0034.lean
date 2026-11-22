import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAddOfLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormDegreeBoundPolynomialCombination
section
open Polynomial

namespace GlobalTheory.NormDegree

noncomputable section

variable {k A : Type} [Field k] [CommRing A] [Algebra k[X] A] {n : ℕ}

theorem natDegree_norm_of_coord_degree : ∀ (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A), ∃ (c : ℕ) (lam : Fin n → k),
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) → (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < d) → (∑ i, (C (lam i) * X ^ d + p i) • b i) ≠ 0 ∧ (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c) := by
  first
  | exact @_root_.GlobalTheory.NormFormBound.norm_degree
  | exact _root_.GlobalTheory.NormFormBound.norm_degree
  | (apply _root_.GlobalTheory.NormFormBound.norm_degree <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormFormBound.norm_degree <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormFormBound.norm_degree <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormFormBound.norm_degree ..)

end

end GlobalTheory.NormDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormXLeOneOfNsmulEqZero
section
namespace GlobalTheory.TorsionIntegral

open IsUltrametricDist WeierstrassCurve

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := norm_add_le_max a (-b)
  rwa [norm_neg, ← sub_eq_add_neg] at this

lemma norm_add_eq_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_y_sq {A B x y : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hx : 1 < ‖x‖)
    (h : y ^ 2 = x ^ 3 + A * x + B) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  have h1 : ‖x‖ < ‖x‖ ^ 3 := by
    have := pow_lt_pow_right₀ hx (show 1 < 3 by norm_num)
    simpa using this
  rw [← norm_pow, h, add_assoc, norm_add_eq_of_lt, norm_pow]
  rw [norm_pow]
  refine (norm_add_le_max _ _).trans_lt (max_lt ?_ (by linarith))
  rw [norm_mul]
  nlinarith [norm_nonneg A]

lemma norm_sum_three_le (a b c : K) : ‖a + b + c‖ ≤ max (max ‖a‖ ‖b‖) ‖c‖ :=
  (norm_add_le_max _ _).trans (max_le_max (norm_add_le_max _ _) le_rfl)

lemma norm_two_le : ‖(2 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 2

lemma norm_three_le : ‖(3 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 3

lemma torsion_root_norm_bound {A B x₁ x₂ x₃ l n : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (e1 : x₁ + x₂ + x₃ = l ^ 2) (e2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = A - 2 * l * n)
    (e3 : x₁ * x₂ * x₃ = n ^ 2 - B) (h12 : ‖x₂‖ ≤ ‖x₁‖) (h2 : 1 < ‖x₂‖) : ‖x₂‖ ≤ ‖x₃‖ := by
  by_contra hc
  push Not at hc
  set a := ‖x₁‖ with ha
  set b := ‖x₂‖ with hb
  set c := ‖x₃‖ with hc'
  have c0 : 0 ≤ c := norm_nonneg _
  have hl : ‖l‖ ^ 2 ≤ a := by
    rw [← norm_pow, ← e1]
    exact (norm_sum_three_le _ _ _).trans (max_le (max_le le_rfl h12) (by linarith))
  have hn : ‖n‖ ^ 2 ≤ max (a * b * c) 1 := by
    rw [← norm_pow, show n ^ 2 = x₁ * x₂ * x₃ + B by rw [e3]; ring]
    refine (norm_add_le_max _ _).trans (max_le_max ?_ hB)
    rw [norm_mul, norm_mul]
  have hab : a * b ≤ max 1 (‖l‖ * ‖n‖) := by
    have h1 : ‖x₁ * x₂ + x₁ * x₃ + x₂ * x₃‖ = a * b := by
      rw [add_assoc, norm_add_eq_of_lt, norm_mul]
      refine (norm_add_le_max _ _).trans_lt (max_lt ?_ ?_) <;> rw [norm_mul, norm_mul] <;>
        nlinarith
    rw [← h1, e2]
    refine (norm_sub_le_max' _ _).trans (max_le_max hA ?_)
    rw [norm_mul, norm_mul]
    have := norm_two_le (K := K)
    have h3 : 0 ≤ ‖l‖ * ‖n‖ := by positivity
    nlinarith
  have hab1 : 1 < a * b := by nlinarith
  have hab2 : a * b ≤ ‖l‖ * ‖n‖ := by
    rcases le_max_iff.1 hab with h | h
    · linarith
    · exact h
  have h4 : (a * b) ^ 2 ≤ a * max (a * b * c) 1 := by
    calc (a * b) ^ 2 ≤ (‖l‖ * ‖n‖) ^ 2 := by gcongr
      _ = ‖l‖ ^ 2 * ‖n‖ ^ 2 := by ring
      _ ≤ _ := by gcongr
  have a0 : 0 < a := by linarith
  have h5 : max (a * b * c) 1 < a * b * b := by
    refine max_lt ?_ ?_
    · exact mul_lt_mul_of_pos_left hc (by linarith)
    · nlinarith
  have := mul_lt_mul_of_pos_left h5 a0
  nlinarith

lemma core {A B x₁ x₂ x₃ y₁ y₂ y₃ l n : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hM : 1 < M)
    (e1 : x₁ + x₂ + x₃ = l ^ 2) (e2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = A - 2 * l * n)
    (e3 : x₁ * x₂ * x₃ = n ^ 2 - B) (hy₁ : y₁ = l * x₁ + n) (hy₂ : y₂ = l * x₂ + n)
    (hy₃ : y₃ = l * x₃ + n) (h1 : M ≤ ‖x₁‖) (h2 : M ≤ ‖x₂‖) :
    M ≤ ‖x₃‖ ∧ ‖x₁ / y₁ + x₂ / y₂ + x₃ / y₃‖ ≤ M⁻¹ := by
  have h3 : M ≤ ‖x₃‖ := by
    rcases le_total ‖x₂‖ ‖x₁‖ with h | h
    · exact h2.trans (torsion_root_norm_bound hA hB e1 e2 e3 h (by linarith))
    · exact h1.trans (torsion_root_norm_bound (x₁ := x₂) (x₂ := x₁) (l := l) (n := n) hA hB
        (by linear_combination e1) (by linear_combination e2) (by linear_combination e3) h
        (by linarith))
  refine ⟨h3, ?_⟩
  have q1 : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B := by
    rw [hy₁]; linear_combination (-x₁ ^ 2) * e1 + x₁ * e2 - e3
  have q2 : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B := by
    rw [hy₂]; linear_combination (-x₂ ^ 2) * e1 + x₂ * e2 - e3
  have q3 : y₃ ^ 2 = x₃ ^ 3 + A * x₃ + B := by
    rw [hy₃]; linear_combination (-x₃ ^ 2) * e1 + x₃ * e2 - e3
  have n1 := norm_y_sq hA hB (by linarith) q1
  have n2 := norm_y_sq hA hB (by linarith) q2
  have n3 := norm_y_sq hA hB (by linarith) q3
  set a := ‖x₁‖ with ha
  set b := ‖x₂‖ with hb
  set c := ‖x₃‖ with hc
  have hab : M ≤ a * b := by nlinarith
  have hac : M ≤ a * c := by nlinarith
  have hbc : M ≤ b * c := by nlinarith
  have habc : M ^ 2 ≤ a * b * c := by nlinarith
  have hM2 : 1 < M ^ 2 := by nlinarith
  have hn : ‖n‖ ^ 2 = a * b * c := by
    rw [← norm_pow, show n ^ 2 = x₁ * x₂ * x₃ + B by rw [e3]; ring, norm_add_eq_of_lt,
      norm_mul, norm_mul]
    rw [norm_mul, norm_mul]
    linarith
  have hl : ‖l‖ ≤ ‖n‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hn, ← norm_pow, ← e1]
    refine (norm_sum_three_le _ _ _).trans (max_le (max_le ?_ ?_) ?_) <;> nlinarith
  have hMn : M ≤ ‖n‖ := by
    refine (pow_le_pow_iff_left₀ (by linarith) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hn]; exact habc
  have hyy : ‖y₁ * y₂ * y₃‖ = ‖n‖ ^ 3 := by
    refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [norm_mul, norm_mul, mul_pow, mul_pow, n1, n2, n3, ← pow_mul, mul_comm 3 2, pow_mul, hn]
    ring
  have n0 : 0 < ‖n‖ := by linarith
  have hy0 : y₁ * y₂ * y₃ ≠ 0 := by
    rw [← norm_pos_iff, hyy]; positivity
  have y1 : y₁ ≠ 0 := fun h => hy0 (by simp [h])
  have y2 : y₂ ≠ 0 := fun h => hy0 (by simp [h])
  have y3 : y₃ ≠ 0 := fun h => hy0 (by simp [h])
  have hS : x₁ * y₂ * y₃ + y₁ * x₂ * y₃ + y₁ * y₂ * x₃ = 2 * A * l * n - 3 * B * l * l := by
    rw [hy₁, hy₂, hy₃]
    linear_combination n ^ 2 * e1 + 2 * l * n * e2 + 3 * l ^ 2 * e3
  have hq : x₁ / y₁ + x₂ / y₂ + x₃ / y₃ = (2 * A * l * n - 3 * B * l * l) / (y₁ * y₂ * y₃) := by
    rw [← hS]; field_simp
  have hN : ‖2 * A * l * n - 3 * B * l * l‖ ≤ ‖n‖ ^ 2 := by
    refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_mul, norm_mul]
      calc _ ≤ 1 * 1 * ‖n‖ * ‖n‖ := by gcongr; exact norm_two_le
        _ = _ := by ring
    · rw [norm_mul, norm_mul, norm_mul]
      calc _ ≤ 1 * 1 * ‖n‖ * ‖n‖ := by gcongr; exact norm_three_le
        _ = _ := by ring
  rw [hq, norm_div, hyy]
  calc _ ≤ ‖n‖ ^ 2 / ‖n‖ ^ 3 := by gcongr
    _ = ‖n‖⁻¹ := by field_simp
    _ ≤ M⁻¹ := by gcongr

noncomputable def param {W : Affine K} : W.Point → K
  | .zero => 0
  | .some x y _ => x / y

def Near {W : Affine K} (M : ℝ) : W.Point → Prop
  | .zero => True
  | .some x _ _ => M ≤ ‖x‖

lemma add_step [DecidableEq K] {A B : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hM : 1 < M)
    (P Q : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Point) (hP : Near M P)
    (hQ : Near M Q) : Near M (P + Q) ∧ ‖param (P + Q) - param P - param Q‖ ≤ M⁻¹ := by
  first
  | exact @_root_.GlobalTheory.UltrametricLineBounds.large_add
  | exact _root_.GlobalTheory.UltrametricLineBounds.large_add
  | (apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricLineBounds.large_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricLineBounds.large_add ..)

theorem norm_x_le_one_of_nsmul_eq_zero (K : Type) [NormedField K] [IsUltrametricDist K]
    [DecidableEq K] (A B : K) (N : ℕ) (x y : K)
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hN : ‖(N : K)‖ = 1)
    (h0 : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖x‖ ≤ 1 := by
  by_contra hx
  push Not at hx
  have M0 : 0 ≤ ‖x‖⁻¹ := by positivity
  have hP : Near ‖x‖ (Affine.Point.some x y h) := le_refl _
  have key : ∀ k : ℕ, Near ‖x‖ (k • Affine.Point.some x y h) ∧
      ‖param (k • Affine.Point.some x y h) - (k : K) * (x / y)‖ ≤ ‖x‖⁻¹ := by
    intro k
    induction k with
    | zero =>
      rw [zero_nsmul]
      exact ⟨trivial, by simp [Affine.Point.zero_def, param]⟩
    | succ k ih =>
      obtain ⟨s1, s2⟩ := add_step hA hB hx _ _ ih.1 hP
      rw [succ_nsmul]
      refine ⟨s1, ?_⟩
      have := (norm_add_le_max _ _).trans (max_le s2 ih.2)
      refine le_of_eq_of_le (congrArg norm ?_) this
      simp only [param]
      push_cast
      ring
  have h1 := (key N).2
  rw [h0] at h1
  simp only [Affine.Point.zero_def, param, zero_sub, norm_neg, norm_mul, hN, one_mul,
    norm_div] at h1
  have he : y ^ 2 = x ^ 3 + A * x + B := by
    have := (Affine.equation_iff _ _).1 h.1
    simp only at this
    linear_combination this
  have hy := norm_y_sq hA hB hx he
  have x0 : 0 < ‖x‖ := by linarith
  have y0 : 0 < ‖y‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
    rw [← h] at hy
    have : 0 < ‖x‖ ^ 3 := by positivity
    simp at hy
    linarith
  rw [inv_eq_one_div, div_le_div_iff₀ y0 x0, one_mul] at h1
  have h2 : (‖x‖ * ‖x‖) ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
  rw [hy] at h2
  have : ‖x‖ ^ 3 * 1 < ‖x‖ ^ 3 * ‖x‖ := by gcongr
  nlinarith

end GlobalTheory.TorsionIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZeroStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_of_mul_mem_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)), (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | exact GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | (intros; apply GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PerfectPairingQuotients
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem exists_addChar_quotient {G : Type} [AddCommGroup G] (H : AddSubgroup G) (f : G → ℂ)
    (h0 : f 0 = 1) (hadd : ∀ x y, f (x + y) = f x * f y) (hH : ∀ x ∈ H, f x = 1) :
    ∃ χ : AddChar (G ⧸ H) ℂ, ∀ g : G, χ (g : G ⧸ H) = f g := by
  have hout : ∀ g : G, f (Quotient.out (g : G ⧸ H)) = f g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hadd, hH _ h.2, mul_one]
  refine ⟨⟨fun q => f (Quotient.out q), ?_, ?_⟩, hout⟩
  · rw [← QuotientAddGroup.mk_zero, hout, h0]
  · intro a b
    induction a using QuotientAddGroup.induction_on
    induction b using QuotientAddGroup.induction_on
    rw [← QuotientAddGroup.mk_add, hout, hout, hout, hadd]

theorem exists_injective_addChar {G K : Type} [AddCommGroup G] [AddCommGroup K] (H : AddSubgroup G)
    (L : AddSubgroup K) (p : G → K → ℂ)
    (hl : ∀ x y z, p (x + y) z = p x z * p y z) (hr : ∀ x y z, p x (y + z) = p x y * p x z)
    (h0 : ∀ x, p x 0 = 1) (h0' : ∀ y, p 0 y = 1)
    (hH : ∀ g, g ∈ H ↔ ∀ k, p g k = 1) (hL : ∀ k ∈ L, ∀ g, p g k = 1) :
    ∃ Φ : G ⧸ H → AddChar (K ⧸ L) ℂ, Function.Injective Φ ∧
      ∀ (g : G) (k : K), Φ (g : G ⧸ H) (k : K ⧸ L) = p g k := by
  choose χ hχ using fun g : G =>
    exists_addChar_quotient L (p g) (h0 g) (hr g) (fun k hk => hL k hk g)
  have hout : ∀ (g : G) (k : K), p (Quotient.out (g : G ⧸ H)) k = p g k := by
    intro g k
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hl, (hH _).1 h.2, mul_one]
  have hΦ : ∀ (g : G) (k : K), χ (Quotient.out (g : G ⧸ H)) (k : K ⧸ L) = p g k := by
    intro g k
    rw [hχ, hout]
  refine ⟨fun q => χ (Quotient.out q), ?_, hΦ⟩
  intro a b hab
  induction a using QuotientAddGroup.induction_on with | _ a
  induction b using QuotientAddGroup.induction_on with | _ b
  rw [QuotientAddGroup.eq, hH]
  intro k
  have h1 : p a k = p b k := by
    rw [← hΦ, ← hΦ]
    exact congrArg (fun ψ : AddChar (K ⧸ L) ℂ => ψ (k : K ⧸ L)) hab
  rw [hl, ← h1, ← hl, neg_add_cancel, h0']

theorem perfect_pairing_quotients : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (S A T₀ T : AddSubgroup X), (∀ a ∈ A, a ∈ S ↔ ∀ t ∈ T, γ a t = 1) → (∀ t ∈ T, t ∈ T₀ ↔ ∀ a ∈ A, γ a t = 1) → T₀.relIndex T ≠ 0 → S.relIndex A = T₀.relIndex T ∧ (∀ y : X, (∀ a ∈ A, a ∈ S → γ a y = 1) → ∃ t ∈ T, ∀ a ∈ A, γ a y = γ a t) ∧ ∀ t ∈ T, (∑ᶠ q : A ⧸ S.addSubgroupOf A, γ ((Quotient.out q : A) : X) t) = if t ∈ T₀ then (S.relIndex A : ℂ) else 0 := by
  intro R X M _ _ _ _ _ σ w γ W h S A T₀ T hS hT hfin
  have hS' : ∀ a : A, a ∈ S.addSubgroupOf A ↔ ∀ t : T, γ a t = 1 := by
    intro a
    rw [AddSubgroup.mem_addSubgroupOf, hS a a.2]
    simp
  have hT' : ∀ t : T, t ∈ T₀.addSubgroupOf T ↔ ∀ a : A, γ a t = 1 := by
    intro t
    rw [AddSubgroup.mem_addSubgroupOf, hT t t.2]
    simp
  obtain ⟨Φ, hΦi, hΦ⟩ := exists_injective_addChar (S.addSubgroupOf A) (T₀.addSubgroupOf T)
    (fun a t => γ a t) (fun x y z => h.add_left _ _ _) (fun x y z => h.add_right _ _ _)
    (fun x => h.zero_right _) (fun x => h.zero_left _) hS' (fun k hk => (hT' k).1 hk)
  obtain ⟨Ψ, hΨi, hΨ⟩ := exists_injective_addChar (T₀.addSubgroupOf T) (S.addSubgroupOf A)
    (fun t a => γ a t) (fun x y z => h.add_right _ _ _) (fun x y z => h.add_left _ _ _)
    (fun x => h.zero_left _) (fun x => h.zero_right _) hT' (fun k hk => (hS' k).1 hk)
  haveI : Finite (T ⧸ T₀.addSubgroupOf T) := Nat.finite_of_card_ne_zero hfin
  haveI : Finite (A ⧸ S.addSubgroupOf A) := Finite.of_injective Φ hΦi
  letI := Fintype.ofFinite (T ⧸ T₀.addSubgroupOf T)
  letI := Fintype.ofFinite (A ⧸ S.addSubgroupOf A)
  have c1 := Fintype.card_le_of_injective Φ hΦi
  have c2 := Fintype.card_le_of_injective Ψ hΨi
  have c3 := c2
  rw [AddChar.card_eq] at c1 c2
  have hc : Fintype.card (A ⧸ S.addSubgroupOf A) = Fintype.card (T ⧸ T₀.addSubgroupOf T) :=
    le_antisymm c1 c2
  have eA : S.relIndex A = Fintype.card (A ⧸ S.addSubgroupOf A) := Nat.card_eq_fintype_card
  have eT : T₀.relIndex T = Fintype.card (T ⧸ T₀.addSubgroupOf T) := Nat.card_eq_fintype_card
  refine ⟨by rw [eA, eT, hc], ?_, ?_⟩
  · intro y hy
    obtain ⟨χ, hχ⟩ := exists_addChar_quotient (S.addSubgroupOf A) (fun a : A => γ a y)
      (h.zero_left _) (fun a b => h.add_left _ _ _)
      (fun a ha => hy a a.2 (AddSubgroup.mem_addSubgroupOf.1 ha))
    have hb : Function.Bijective Ψ :=
      (Fintype.bijective_iff_injective_and_card Ψ).2 ⟨hΨi, by rw [AddChar.card_eq, hc]⟩
    obtain ⟨q, hq⟩ := hb.2 χ
    induction q using QuotientAddGroup.induction_on with | _ t
    refine ⟨t, t.2, fun a ha => ?_⟩
    have h1 := hΨ t ⟨a, ha⟩
    rw [hq, hχ] at h1
    exact h1
  · intro t ht
    rw [finsum_eq_sum_of_fintype]
    have h1 : ∀ q : A ⧸ S.addSubgroupOf A,
        γ ((Quotient.out q : A) : X) t = Ψ ((⟨t, ht⟩ : T) : T ⧸ T₀.addSubgroupOf T) q := by
      intro q
      conv_rhs => rw [← QuotientAddGroup.out_eq' q]
      rw [hΨ]
    rw [Finset.sum_congr rfl fun q _ => h1 q, AddChar.sum_eq_ite, eA]
    refine if_congr ?_ rfl rfl
    rw [hT t ht]
    constructor
    · intro h0 a ha
      have h2 := hΨ ⟨t, ht⟩ ⟨a, ha⟩
      rw [h0] at h2
      simpa using h2.symm
    · intro h0
      ext q
      rw [← h1, h0 _ (Quotient.out q).2]
      simp

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceUnitSetEqSmoothingMulPieceRaw
section
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.Smoothing

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem zpow_congr_of_pow_eq_one {ζ : K} {M : ℕ} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨s, hs⟩ := h.dvd
  have hb : b = a + M * s := by linarith
  rw [hb, zpow_add₀ hz, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem eisF_congr_mod {j M : ℕ} (hM : 0 < M) {ζ : K} (hζ : ζ ^ M = 1) {a₁ a₂ b₁ b₂ : ℤ}
    (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) :
    eisF j M ζ a₁ a₂ = eisF j M ζ b₁ b₂ := by
  funext n
  have h₁' : a₁ % (M : ℤ) = b₁ % (M : ℤ) := h₁
  have hc : const0 j M ζ a₁ a₂ = const0 j M ζ b₁ b₂ := by
    have hd : ((M : ℤ) ∣ a₁) ↔ ((M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁']
    have hf : frc M a₁ = frc M b₁ := by unfold frc; rw [h₁']
    unfold const0
    rw [zpow_congr_of_pow_eq_one hM hζ h₂, hf]
    simp only [hd]
  have hp : coefPos j M ζ a₁ a₂ n = coefPos j M ζ b₁ b₂ n := by
    unfold coefPos
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have e1 : ∀ z : ℤ, z ≡ a₁ [ZMOD M] ↔ z ≡ b₁ [ZMOD M] :=
      fun z => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    rw [zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)).neg]
    simp only [e1]
  unfold eisF
  rw [hc, hp]

omit [CharZero K] in
theorem cmul_expand (a b a' b' : K) (f g h l : ℕ → K) (r : ℕ) :
    cmul (fun i => a * f i - b * g i) (fun i => a' * h i - b' * l i) r =
      a * a' * cmul f h r - a * b' * cmul f l r - b * a' * cmul g h r + b * b' * cmul g l r := by
  unfold cmul
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem not_dvd_val_iff_isUnit {p n : ℕ} [hp : Fact p.Prime] (hn : 0 < n) (y : ZMod (p ^ n)) :
    ¬ p ∣ y.val ↔ IsUnit y := by
  have h := ZMod.isUnit_iff_coprime y.val (p ^ n)
  rw [ZMod.natCast_zmod_val] at h
  rw [h, Nat.coprime_pow_right_iff hn, Nat.coprime_comm, hp.out.coprime_iff_not_dvd]

theorem isUnit_intCast_of_not_dvd {p n : ℕ} [hp : Fact p.Prime] {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : IsUnit (c : ZMod (p ^ n)) := by
  have h1 : IsCoprime (p : ℤ) c :=
    (Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hc
  obtain ⟨a, b, hab⟩ := (h1.pow_left (m := n))
  have h2 : ((a * (p : ℤ) ^ n + b * c : ℤ) : ZMod (p ^ n)) = 1 := by rw [hab]; simp
  have h3 : ((p : ZMod (p ^ n))) ^ n = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  push_cast at h2
  rw [h3, mul_zero, zero_add, mul_comm] at h2
  exact IsUnit.of_mul_eq_one _ h2

def diagGL {R : Type*} [CommRing R] (u v : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![(u : R), v], Matrix.diagonal ![((u⁻¹ : Rˣ) : R), ((v⁻¹ : Rˣ) : R)],
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp,
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp⟩

theorem diagGL_mul_zero {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 j =
      (u : R) * (γ : Matrix (Fin 2) (Fin 2) R) 0 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_one {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 j =
      (v : R) * (γ : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_det {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det =
      (u : R) * v * (γ : Matrix (Fin 2) (Fin 2) R).det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [diagGL_mul_zero, diagGL_mul_one]
  ring

theorem diagGL_mul_mem {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (u v : (ZMod (p ^ n))ˣ)
    (γ : GL (Fin 2) (ZMod (p ^ n))) : diagGL u v * γ ∈ unitSet p n ↔ γ ∈ unitSet p n := by
  simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, not_dvd_val_iff_isUnit hn,
    diagGL_mul_zero, diagGL_mul_one, Units.isUnit_units_mul]

end GlobalTheory.KummerEisensteinGalois.Smoothing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowSmulHeckeVOperatorExplicitEqSlashDiag
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem smul_vOp_eq_slash (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q) : (q : ℂ) ^ (k - 1) • vOp q f = f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  set g := (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) with hg
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = q := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hdet : (g.det : ℝ) = q := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdpos : 0 < (g.det : ℝ) := by rw [hdet]; exact_mod_cast hq
  ext τ
  have hden : denom g τ = 1 := by simp [denom, h10, h11]
  have hnum : num g τ = q * τ := by simp [num, h00, h01]
  have hsmul : ((g • τ : ℍ) : ℂ) = q * τ := by
    rw [UpperHalfPlane.coe_smul_of_det_pos hdpos, hnum, hden, div_one]
  have hof : ofComplex ((q : ℂ) * τ) = g • τ := by
    rw [← hsmul]; exact ofComplex_apply _
  rw [slash_apply, hden, one_zpow, mul_one, hdet, abs_of_pos (by exact_mod_cast hq : (0:ℝ) < q)]
  simp only [σ, hdpos, if_true, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, vOp, hof]
  push_cast
  ring_nf
  rfl

end GlobalTheory.Hk
end

