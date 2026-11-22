import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscFieldEqTorsionField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.DiscRoot

open Polynomial WeierstrassCurve

theorem exists_vieta_two (p q : ℂ) : ∃ x y : ℂ, x + y = p ∧ x * y = q := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (p ^ 2 - 4 * q) (show 0 < 2 by norm_num)
  exact ⟨(p + s) / 2, (p - s) / 2, by ring, by linear_combination (-1 / 4 : ℂ) * hs⟩

theorem exists_vieta_three (p q r : ℂ) :
    ∃ x y z : ℂ, x + y + z = p ∧ x * y + x * z + y * z = q ∧ x * y * z = r := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 3 - C p * X ^ 2 + C q * X - C r : ℂ[X]) (by
    have : (X ^ 3 - C p * X ^ 2 + C q * X - C r : ℂ[X]).degree = 3 := by compute_degree!
    rw [this]; decide)
  simp only [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx
  obtain ⟨y, z, h1, h2⟩ := exists_vieta_two (p - x) (q - x * (p - x))
  exact ⟨x, y, z, by linear_combination h1, by linear_combination x * h1 + h2, by linear_combination x * h2 + hx⟩

theorem exists_vieta_four (p q r t : ℂ) :
    ∃ x y z w : ℂ, x + y + z + w = p ∧ x * y + x * z + x * w + y * z + y * w + z * w = q ∧
      x * y * z + x * y * w + x * z * w + y * z * w = r ∧ x * y * z * w = t := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 4 - C p * X ^ 3 + C q * X ^ 2 - C r * X + C t : ℂ[X]) (by
    have : (X ^ 4 - C p * X ^ 3 + C q * X ^ 2 - C r * X + C t : ℂ[X]).degree = 4 := by compute_degree!
    rw [this]; decide)
  simp only [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx
  obtain ⟨y, z, w, h1, h2, h3⟩ := exists_vieta_three (p - x) (q - x * (p - x)) (r - x * (q - x * (p - x)))
  exact ⟨x, y, z, w, by linear_combination h1, by linear_combination x * h1 + h2, by linear_combination x * h2 + h3,
    by linear_combination x * h3 - hx⟩

variable {W : WeierstrassCurve ℂ}

theorem four_torsion (hΔ : W.Δ ≠ 0) {e s t : ℂ} (h2 : W.b₂ = -4 * (3 * e - s ^ 2 - t ^ 2))
    (h4 : W.b₄ = 2 * (e * (e - s ^ 2) + e * (e - t ^ 2) + (e - s ^ 2) * (e - t ^ 2)))
    (h6 : W.b₆ = -4 * (e * (e - s ^ 2) * (e - t ^ 2))) (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    e + s * t ∈ torsionCoords W 4 ∧
      s * t * (s + t) - (W.a₁ * (e + s * t) + W.a₃) / 2 ∈ torsionCoords W 4 := by
  simp only [b₂, b₄, b₆] at h2 h4 h6
  set x := e + s * t with hx
  set y := s * t * (s + t) - (W.a₁ * x + W.a₃) / 2 with hy
  have heq : W.toAffine.Equation x y := by
    rw [Affine.equation_iff]
    simp only [toAffine]
    rw [hy, hx]
    linear_combination (-(e + s * t) ^ 2 / 4) * h2 - (e + s * t) / 2 * h4 - 1 / 4 * h6
  have hns : W.toAffine.Nonsingular x y := (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 heq
  have hd : y - W.toAffine.negY x y = 2 * (s * t * (s + t)) := by
    simp only [Affine.negY, toAffine]
    rw [hy]; ring
  have hd0 : y - W.toAffine.negY x y ≠ 0 := by
    rw [hd]; exact mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hs ht) hst)
  have hne : y ≠ W.toAffine.negY x y := sub_ne_zero.1 hd0
  have hl : W.toAffine.slope x x y y = s + t - W.a₁ / 2 := by
    rw [Affine.slope_of_Y_ne rfl hne, div_eq_iff hd0, hd]
    simp only [toAffine]
    rw [hy, hx]
    linear_combination (e + s * t) / 2 * h2 + 1 / 2 * h4
  have h0 : 4 • Affine.Point.some x y hns = 0 := by
    rw [show 4 = 2 * 2 from rfl, mul_smul, two_smul, two_smul, Affine.Point.add_self_of_Y_ne hne]
    apply Affine.Point.add_self_of_Y_eq
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, hl, toAffine]
    rw [hy, hx]
    linear_combination (s + t) / 2 * h2
  exact ⟨⟨x, y, hns, h0, Or.inl rfl⟩, ⟨x, y, hns, h0, Or.inr rfl⟩⟩

theorem three_torsion (hΔ : W.Δ ≠ 0) {x : ℂ}
    (h : 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ = 0) : x ∈ torsionCoords W 3 := by
  simp only [b₂, b₄, b₆, b₈] at h
  obtain ⟨y, y', h1, h2⟩ := exists_vieta_two (-(W.a₁ * x + W.a₃)) (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    linear_combination y * h1 - h2
  have hns : W.toAffine.Nonsingular x y :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 ((Affine.equation_iff _ _).2 heq)
  have key : (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2 +
      W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃) =
      (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    linear_combination -h - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * heq
  have hd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    simp only [Affine.negY, toAffine]; ring
  have hd0 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro h0
    rw [h0] at key
    have h3 : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = 0 := by
      apply pow_eq_zero_iff (n := 2) two_ne_zero |>.1
      linear_combination key
    rcases ((Affine.nonsingular_iff _ _).1 hns).2 with h4 | h4
    · exact h4 (by simp only [toAffine]; linear_combination -h3)
    · exact h4 (by simp only [toAffine]; linear_combination h0)
  have hne : y ≠ W.toAffine.negY x y := sub_ne_zero.1 (hd ▸ hd0)
  have hX : W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
    have hl : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
      rw [Affine.slope_of_Y_ne rfl hne, hd, div_mul_cancel₀ _ hd0]
    rw [← hl] at key
    simp only [Affine.addX, toAffine] at key ⊢
    apply mul_right_cancel₀ (pow_ne_zero 2 hd0)
    linear_combination key
  refine ⟨x, y, hns, ?_, Or.inl rfl⟩
  rw [show 3 = 2 + 1 from rfl, add_smul, two_smul, one_smul, Affine.Point.add_self_of_Y_ne hne]
  apply Affine.Point.add_of_Y_eq hX
  simp only [Affine.addY, Affine.negAddY, hX, sub_self, mul_zero, zero_add]

variable {M : IntermediateField ℚ ℂ}

theorem sqrt_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 4 ⊆ M) {e₁ e₂ e₃ s : ℂ}
    (h2 : W.b₂ = -4 * (e₁ + e₂ + e₃)) (h4 : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃)) (h6 : W.b₆ = -4 * (e₁ * e₂ * e₃))
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) (hs : s ^ 2 = e₁ - e₂) : s ∈ M := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₃) (show 0 < 2 by norm_num)
  have key : ∀ t : ℂ, t ^ 2 = e₁ - e₃ → s * t ≠ 0 ∧ e₁ + s * t ∈ M ∧ s * t * (s + t) ∈ M := by
    intro t ht
    have hs0 : s ≠ 0 := fun h => h12 (by rw [h] at hs; linear_combination -hs)
    have ht0 : t ≠ 0 := fun h => h13 (by rw [h] at ht; linear_combination -ht)
    have hst : s + t ≠ 0 := fun h => h23 (by linear_combination hs - ht - (s - t) * h)
    obtain ⟨k1, k2⟩ := four_torsion (e := e₁) hΔ (by rw [hs, ht, h2]; ring) (by rw [hs, ht, h4]; ring)
      (by rw [hs, ht, h6]; ring) hs0 ht0 hst
    have k1 : e₁ + s * t ∈ M := hM k1
    have k2 : _ ∈ M := hM k2
    refine ⟨mul_ne_zero hs0 ht0, k1, ?_⟩
    have := add_mem k2 (div_mem (add_mem (mul_mem ha₁ k1) ha₃) (ofNat_mem M 2))
    rwa [sub_add_cancel] at this
  obtain ⟨h0, k1, k2⟩ := key t ht
  obtain ⟨-, k3, k4⟩ := key (-t) (by rw [neg_sq, ht])
  have hs0 : s ≠ 0 := left_ne_zero_of_mul h0
  have ht0 : t ≠ 0 := right_ne_zero_of_mul h0
  have : s = (s * t * (s + t) - s * -t * (s + -t)) / ((e₁ + s * t) - (e₁ + s * -t)) := by
    rw [eq_div_iff (by
      rw [show (e₁ + s * t) - (e₁ + s * -t) = 2 * (s * t) by ring]
      exact mul_ne_zero two_ne_zero h0)]
    ring
  rw [this]
  exact div_mem (sub_mem k2 k4) (sub_mem k1 k3)

theorem fourth_root_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 4 ⊆ M) {c : ℂ}
    (hc : c ^ 4 = W.Δ) : c ∈ M := by
  obtain ⟨e₁, e₂, e₃, k2, k4, k6⟩ := exists_vieta_three (-W.b₂ / 4) (W.b₄ / 2) (-W.b₆ / 4)
  have h2 : W.b₂ = -4 * (e₁ + e₂ + e₃) := by linear_combination 4 * k2
  have h4 : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by linear_combination -2 * k4
  have h6 : W.b₆ = -4 * (e₁ * e₂ * e₃) := by linear_combination 4 * k6
  have h8 : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by linear_combination W.b_relation / 4
  have hD : W.Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
    rw [Δ, h8, h2, h4, h6]; ring
  have h12 : e₁ ≠ e₂ := fun h => hΔ (by rw [hD, h]; ring)
  have h13 : e₁ ≠ e₃ := fun h => hΔ (by rw [hD, h]; ring)
  have h23 : e₂ ≠ e₃ := fun h => hΔ (by rw [hD, h]; ring)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₂) (show 0 < 2 by norm_num)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₃) (show 0 < 2 by norm_num)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (e₂ - e₃) (show 0 < 2 by norm_num)
  have ms : s ∈ M := sqrt_mem hΔ ha₁ ha₃ hM h2 h4 h6 h12 h13 h23 hs
  have mt : t ∈ M := sqrt_mem (e₁ := e₁) (e₂ := e₃) (e₃ := e₂) hΔ ha₁ ha₃ hM (by rw [h2]; ring) (by rw [h4]; ring)
    (by rw [h6]; ring) h13 h12 h23.symm ht
  have mu : u ∈ M := sqrt_mem (e₁ := e₂) (e₂ := e₃) (e₃ := e₁) hΔ ha₁ ha₃ hM (by rw [h2]; ring) (by rw [h4]; ring)
    (by rw [h6]; ring) h23 h12.symm h13.symm hu
  have mi : Complex.I * s ∈ M := sqrt_mem (e₁ := e₂) (e₂ := e₁) (e₃ := e₃) hΔ ha₁ ha₃ hM (by rw [h2]; ring)
    (by rw [h4]; ring) (by rw [h6]; ring) h12.symm h23 h13 (by rw [mul_pow, Complex.I_sq, hs]; ring)
  have mb : 2 * (s * t * u) ∈ M := mul_mem (ofNat_mem M 2) (mul_mem (mul_mem ms mt) mu)
  have mb' : Complex.I * (2 * (s * t * u)) ∈ M := by
    rw [show Complex.I * (2 * (s * t * u)) = 2 * (Complex.I * s * t * u) by ring]
    exact mul_mem (ofNat_mem M 2) (mul_mem (mul_mem mi mt) mu)
  have hb : (2 * (s * t * u)) ^ 4 = c ^ 4 := by
    rw [hc, hD, ← hs, ← ht, ← hu]; ring
  generalize 2 * (s * t * u) = b at mb mb' hb
  have hf : (c - b) * (c + b) * ((c - Complex.I * b) * (c + Complex.I * b)) = 0 := by
    linear_combination -hb - (c ^ 2 - b ^ 2) * b ^ 2 * Complex.I_sq
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hf
  rcases hf with (h | h) | h | h <;> rw [h]
  exacts [mb, neg_mem mb, mb', neg_mem mb']

theorem cube_root_mem (hΔ : W.Δ ≠ 0) (hM : torsionCoords W 3 ⊆ M) {c : ℂ} (hc : c ^ 3 = W.Δ) : c ∈ M := by
  obtain ⟨x, y, z, w, k2, k4, k6, k8⟩ := exists_vieta_four (-W.b₂ / 3) W.b₄ (-W.b₆) (W.b₈ / 3)
  have h2 : W.b₂ = -3 * (x + y + z + w) := by linear_combination 3 * k2
  have h4 := k4.symm
  have h6 : W.b₆ = -(x * y * z + x * y * w + x * z * w + y * z * w) := by linear_combination k6
  have h8 : W.b₈ = 3 * (x * y * z * w) := by linear_combination -3 * k8
  have mx : x ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have my : y ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have mz : z ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have mw : w ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have m4 : W.b₄ ∈ M := by
    rw [h4]
    exact add_mem (add_mem (add_mem (add_mem (add_mem (mul_mem mx my) (mul_mem mx mz)) (mul_mem mx mw))
      (mul_mem my mz)) (mul_mem my mw)) (mul_mem mz mw)
  have hr := W.b_relation
  have res : ∀ u : ℂ, u ^ 3 - W.b₄ * u ^ 2 + (W.b₂ * W.b₆ - 4 * W.b₈) / 3 * u -
      (W.b₂ ^ 2 * W.b₈ / 27 + W.b₆ ^ 2 - 4 * W.b₄ * W.b₈ / 3) = 0 → (W.b₄ - 3 * u) ^ 3 = W.Δ := by
    intro u hu
    rw [Δ]
    linear_combination -27 * hu + (9 * W.b₄ - 9 * u) * hr
  have a1 := res (x * y + z * w) (by rw [h2, h4, h6, h8]; ring)
  have a2 := res (x * z + y * w) (by rw [h2, h4, h6, h8]; ring)
  have a3 := res (x * w + y * z) (by rw [h2, h4, h6, h8]; ring)
  have m1 : W.b₄ - 3 * (x * y + z * w) ∈ M :=
    sub_mem m4 (mul_mem (ofNat_mem M 3) (add_mem (mul_mem mx my) (mul_mem mz mw)))
  have m2 : W.b₄ - 3 * (x * z + y * w) ∈ M :=
    sub_mem m4 (mul_mem (ofNat_mem M 3) (add_mem (mul_mem mx mz) (mul_mem my mw)))
  rw [show W.b₄ - 3 * (x * w + y * z) = -((W.b₄ - 3 * (x * y + z * w)) + (W.b₄ - 3 * (x * z + y * w))) by
    linear_combination 3 * h4] at a3
  generalize W.b₄ - 3 * (x * y + z * w) = a at a1 a3 m1
  generalize W.b₄ - 3 * (x * z + y * w) = b at a2 a3 m2
  have hab : b - a ≠ 0 := fun h => hΔ (by
    rw [sub_eq_zero.1 h] at a3
    linear_combination (-8 / 9 : ℂ) * a1 - 1 / 9 * a3)
  have hq : b ^ 2 + b * a + a ^ 2 = 0 := mul_left_cancel₀ hab (by linear_combination a2 - a1)
  have hf : (c - a) * (c - b) * (c + (a + b)) = 0 := by
    linear_combination hc - a1 + (a - c) * hq
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hf
  rcases hf with (h | h) | h <;> rw [h]
  exacts [m1, m2, neg_mem (add_mem m1 m2)]

theorem twelfth_root_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 12 ⊆ M) {z : ℂ}
    (hz : z ^ 12 = W.Δ) : z ∈ M := by
  have h0 : z ≠ 0 := fun h => hΔ (by rw [← hz, h]; norm_num)
  have h3 : z ^ 3 ∈ M := fourth_root_mem hΔ ha₁ ha₃ ((torsionCoords_mono W (by norm_num)).trans hM)
    (by rw [← hz]; ring)
  have h4 : z ^ 4 ∈ M := cube_root_mem hΔ ((torsionCoords_mono W (by norm_num)).trans hM) (by rw [← hz]; ring)
  rw [show z = z ^ 4 / z ^ 3 by field_simp]
  exact div_mem h4 h3

theorem discField_eq_torsionField (d : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F) [A.IsElliptic] :
    discField d A = torsionField d A := by
  refine le_antisymm (sup_le le_rfl ?_) (torsionField_le_discField d A)
  rw [IntermediateField.adjoin_le_iff]
  intro z (hz : z ^ 12 = _)
  have hF : F ≤ torsionField d A := le_sup_right.trans (hilbertField_le_torsionField d A)
  have hD : (A.baseChange ℂ).Δ = (A.Δ : ℂ) := by rw [baseChange, map_Δ]; rfl
  refine twelfth_root_mem (W := A.baseChange ℂ) ?_ (hF A.a₁.2) (hF A.a₃.2) ?_ (hD ▸ hz)
  · rw [hD]
    exact fun h => A.isUnit_Δ.ne_zero (Subtype.ext h)
  · exact fun w hw => (le_sup_right : _ ≤ torsionField d A) (IntermediateField.subset_adjoin ℚ _ hw)

end GlobalTheory.Mem.DiscRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApplyEqOfNormal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayMono

theorem exists_apply_eq_of_normal {K A Ω : Type} [Field K] [Field A] [Field Ω] [Algebra K A] [Algebra K Ω]
    [Normal K A] (i j : A →ₐ[K] Ω) (x : A) : ∃ y, j y = i x := by
  let _ := j.toRingHom.toAlgebra
  have : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  exact ⟨i.restrictNormal A x, i.restrictNormal_commutes A x⟩

theorem le_of_isRayFieldIn_of_dvd : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (𝔪 𝔪' : Ideal (𝓞 E))
    (M M' : IntermediateField ℚ ℂ), 𝔪' ≠ ⊥ → 𝔪 ∣ 𝔪' → IsRayFieldIn φ 𝔪 M → IsRayFieldIn φ 𝔪' M' → M ≤ M' := by
  rintro E _ _ φ 𝔪 𝔪' M M' hn hd ⟨h, _, hM⟩ ⟨h', _, hM'⟩ z hz
  let _ := algOf φ M h
  let _ := algOf φ M' h'
  let _ := φ.toAlgebra
  have := hM.1
  have := hM'.1
  obtain ⟨f⟩ := nonempty_algHom_of_isRay_of_dvd hn hd hM'.2 hM.2
  let i : M →ₐ[E] ℂ := { M.val.toRingHom with commutes' := fun _ => rfl }
  let i' : M' →ₐ[E] ℂ := { M'.val.toRingHom with commutes' := fun _ => rfl }
  obtain ⟨y, hy⟩ := exists_apply_eq_of_normal i (i'.comp f) ⟨z, hz⟩
  have hy' : ((f y : M') : ℂ) = z := hy
  exact hy' ▸ (f y).2

end GlobalTheory.Mem.RayMono
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIndexIdealInfSupLattices
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaEx
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem exists_index_ideal_inf_sup (E : Type) [Field E] [NumberField E] (n : ℕ)
    (M M' : Submodule (𝓞 E) (Fin n → E)) (hb : Bdd (M' ⊔ M))
    (ht : ∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') :
    ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan (M ⊓ M') = 𝔞 • detSpan M ∧
      detSpan M' = 𝔞 • detSpan (M' ⊔ M) ∧
      Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex M.toAddSubgroup := by
  classical
  have hsub : ∀ N : Submodule (𝓞 E) (Fin n → E), N ≤ M' ⊔ M → Bdd N := by
    intro N hN
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk, fun v hv => h v (hN hv)⟩
  have key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ M) →
      ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧
        detSpan (M ⊓ M') = 𝔞 • detSpan ((M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        detSpan M' = 𝔞 • detSpan (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex
          ((M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))).toAddSubgroup := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨⊤, by simp, by simp, by simp, by simp⟩
    | insert m s _ ih =>
      intro hs
      obtain ⟨𝔞, h0, h1, h1', h2⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hsM : Submodule.span (𝓞 E) (s : Set (Fin n → E)) ≤ M :=
        Submodule.span_le.2 fun x hx => hs x (Finset.mem_insert_of_mem hx)
      set N := (M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hN
      set S := M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hS
      have hm : m ∈ M := hs m (Finset.mem_insert_self _ _)
      have hmM : Submodule.span (𝓞 E) {m} ≤ M := (Submodule.span_singleton_le_iff_mem _ _).2 hm
      have e : (M ⊓ M') ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          N ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hN, sup_assoc, sup_comm (Submodule.span _ {m})]
      have e' : M' ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          S ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hS, sup_assoc, sup_comm (Submodule.span _ {m})]
      have hNS : N = M ⊓ S := by
        rw [hN, hS, inf_sup_assoc_of_le _ hsM]
      have hb1 : Bdd (N ⊔ Submodule.span (𝓞 E) {m}) :=
        hsub _ (le_sup_of_le_right (sup_le (sup_le inf_le_left hsM) hmM))
      have hb2 : Bdd (S ⊔ Submodule.span (𝓞 E) {m}) :=
        hsub _ (sup_le (sup_le_sup_left hsM _) (le_sup_of_le_right hmM))
      have hc : (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) =
          S.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) := by
        ext a
        rw [hNS]
        exact ⟨fun h => h.2, fun h => ⟨M.smul_mem a hm, h⟩⟩
      rw [e, e']
      refine ⟨𝔞 * (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_, ?_⟩
      · refine mul_ne_zero h0 ?_
        obtain ⟨a, ha, ham⟩ := ht m hm
        exact (Submodule.ne_bot_iff _).2
          ⟨a, (le_sup_left : M ⊓ M' ≤ N) ⟨M.smul_mem a hm, ham⟩, ha⟩
      · rw [h1, Submodule.mul_smul, ← detSpan_cyclic N m hb1]
      · rw [h1', hc, Submodule.mul_smul, ← detSpan_cyclic S m hb2]
      · rw [map_mul, h2, index_cyclic]
        exact AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left)
          (Submodule.toAddSubgroup_mono le_sup_left)
  have hfg : M.FG := by
    obtain ⟨k, hk, h⟩ := hsub M le_sup_right
    have hs : (stdLat E n).FG := Submodule.fg_pi fun _ => by
      rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
    apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k)
      (fun x y hxy => smul_right_injective _ hk hxy)
    exact hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
  obtain ⟨s, rfl⟩ := hfg
  have := key s fun x hx => Submodule.subset_span hx
  rwa [sup_eq_right.2 inf_le_left] at this

end GlobalTheory.BetaEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCurveLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

noncomputable section

namespace GlobalTheory.Mem.Col2.CurveLat

theorem exists_periodPair_mul_image {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : 𝓞 K →+* ℂ) (hσ : Function.Injective σ) (a : 𝓞 K) (ha : (σ a).im ≠ 0) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ c : 𝓞 K, z = δ * σ c := by
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans hK)
  have hs : ∀ x : 𝓞 K, σ x = b.repr x 0 * σ (b 0) + b.repr x 1 * σ (b 1) := by
    intro x
    have := congrArg σ (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ (b 0) ≠ 0 := (map_ne_zero_iff σ hσ).2 (b.ne_zero 0)
  have h0 : (σ (b 1) * starRingEnd ℂ (σ (b 0))).im ≠ 0 := by
    intro h0
    have e := hs (a * b 0)
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ (b 0))).im) e
    simp only [map_mul] at e'
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨δ * σ (b 0), δ * σ (b 1), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e0
    have e : (x : ℂ) * σ (b 0) + (y : ℂ) * σ (b 1) = 0 := by
      apply mul_left_cancel₀ hδ
      simp only [Complex.real_smul] at e0
      linear_combination e0
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 1)).im * e1 - (σ (b 1)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 0)).re * e2 - (σ (b 0)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m • b 0 + n • b 1, by simp; ring⟩
    · rintro ⟨x, rfl⟩
      exact ⟨b.repr x 0, b.repr x 1, by rw [hs x]; ring⟩

theorem not_isIntegral_half : ¬ IsIntegral ℤ (1 / 2 : ℂ) := by
  intro h
  have h1 : IsIntegral ℤ (1 / 2 : ℚ) := by
    refine (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).1 ?_
    simpa using h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  have h2 : (2 * y : ℚ) = 1 := by
    simp only [eq_intCast] at hy
    rw [hy]; norm_num
  have h3 : 2 * y = 1 := by exact_mod_cast h2
  omega

theorem not_isIntegral_of_re {z : ℂ} (hz : z.re = 1 / 4) : ¬ IsIntegral ℤ z := by
  intro h
  have h1 : IsIntegral ℤ (starRingEnd ℂ z) := h.map (starRingEnd ℂ).toIntAlgHom
  have h2 := h.add h1
  rw [Complex.add_conj, hz] at h2
  apply not_isIntegral_half
  have e : ((2 * (1 / 4) : ℝ) : ℂ) = 1 / 2 := by
    push_cast
    norm_num
  rwa [e] at h2

variable {R : Ranks} (H : Host R)

def embO : 𝓞 H.K →+* ℂ := (H.φ₀.comp H.K.val.toRingHom).comp (algebraMap (𝓞 H.K) H.K)

theorem mem_lamOf_top (δ z : ℂ) : z ∈ Th.lamOf H ⊤ δ ↔ ∃ c : 𝓞 H.K, z = δ * embO H c := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, -, rfl⟩ := hx
      exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by rw [map_add, mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, by rw [map_neg, mul_neg]⟩
  · rintro ⟨c, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, rfl⟩

theorem exists_periodPair_lamOf (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Th.lamOf H ⊤ δ ↔ z ∈ L.lattice := by
  have hK : Module.finrank ℚ H.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq
  have hinj : Function.Injective (embO H) :=
    (H.φ₀.comp H.K.val.toRingHom).injective.comp RingOfIntegers.coe_injective
  have ha : (embO H ⟨_, HostK.isIntegral_half H⟩).im ≠ 0 := by
    have e : embO H ⟨_, HostK.isIntegral_half H⟩ = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2 := by
      rw [← HostK.φ₀_sqrt]
      change (H.φ₀.comp H.K.val.toRingHom) ((1 + (⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ : H.K)) / 2) = _
      rw [map_div₀, map_add, map_one, map_ofNat]
      rfl
    have hd : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
    rw [e]
    simp [hd.ne']
  obtain ⟨L, hL⟩ := exists_periodPair_mul_image hK (embO H) hinj _ ha δ hδ
  exact ⟨L, fun z => by rw [mem_lamOf_top, hL]⟩

theorem not_mem_lamOf (δ : ℂ) (hδ : δ ≠ 0) {z : ℂ} (hz : z.re = 1 / 4) : δ * z ∉ Th.lamOf H ⊤ δ := by
  rw [mem_lamOf_top]
  rintro ⟨c, hc⟩
  apply not_isIntegral_of_re hz
  rw [mul_left_cancel₀ hδ hc]
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) c).map (embO H).toIntAlgHom

end GlobalTheory.Mem.Col2.CurveLat

namespace GlobalTheory.Mem.Col2

open CurveLat

theorem exists_curve_lattice : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  intro R H
  obtain ⟨L₁, h₁⟩ := exists_periodPair_lamOf H 1 one_ne_zero
  have hΔ := (GlobalTheory.LatticeInvariants.invariants_dictionary L₁ _ h₁).2.2.1
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (Th.lamOf H ⊤ 1)) (n := 12) (by norm_num)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hδ]; norm_num)
  obtain ⟨L, hL⟩ := exists_periodPair_lamOf H δ hδ0
  refine ⟨δ, L, δ, hδ, AddSubgroup.ext fun z => (hL z).symm, ?_, ?_, ?_⟩
  · exact (mem_lamOf_top H δ _).2 ⟨1, by rw [map_one]; ring⟩
  · have := not_mem_lamOf H δ hδ0 (z := (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring
  · have := not_mem_lamOf H δ hδ0 (z := (1 - Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring

end GlobalTheory.Mem.Col2

end
end

