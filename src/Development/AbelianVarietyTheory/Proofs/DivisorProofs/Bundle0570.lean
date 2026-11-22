import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Formalism.LocalToGlobal.Divisibility.CoefMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0558
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarJacLeExp
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.PolarJacBound

open MvPolynomial in
private lemma shc_nonneg' (x : ℝ) : 0 ≤ _root_.Formalism.MainNotions.SchurIrreducible.shc x := by
  unfold _root_.Formalism.MainNotions.SchurIrreducible.shc
  split_ifs with hx
  · norm_num
  · rcases lt_or_gt_of_ne hx with h | h
    · exact (div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h) h).le
    · exact (div_pos (Real.sinh_pos_iff.mpr h) h).le

open MvPolynomial in
private lemma sinh_div_le_exp_of_pos {y : ℝ} (hy : 0 < y) : Real.sinh y / y ≤ Real.exp y := by
  rw [div_le_iff₀ hy, Real.sinh_eq]
  have h1 : -(2 * y) + 1 ≤ Real.exp (-(2 * y)) := Real.add_one_le_exp _
  have h2 : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 0 < Real.exp y := Real.exp_pos y
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]

open MvPolynomial in
private lemma shc_le_exp_abs (x : ℝ) : _root_.Formalism.MainNotions.SchurIrreducible.shc x ≤ Real.exp |x| := by
  unfold _root_.Formalism.MainNotions.SchurIrreducible.shc
  split_ifs with hx
  · simp [hx]
  · rcases lt_or_gt_of_ne hx with h | h
    · rw [abs_of_neg h]
      have := sinh_div_le_exp_of_pos (neg_pos.mpr h)
      rwa [Real.sinh_neg, neg_div_neg_eq] at this
    · rw [abs_of_pos h]
      exact sinh_div_le_exp_of_pos h

open MvPolynomial in
private lemma sum_sum_ite_lt_four_mul_add_eq (m : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (if i < j then 4 * (a i + a j) else 0) =
      4 * (((m : ℝ) - 1) * ∑ i ∈ Finset.range m, a i) := by
  have e : ∀ i j, (if i < j then 4 * (a i + a j) else 0) =
      4 * ((if i < j then a i else 0) + (if i < j then a j else 0)) := by
    intro i j; split_ifs <;> ring
  simp_rw [e, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then a j else 0), ← Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  have t : ∀ j, ((if i < j then a i else 0) + (if j < i then a i else 0)) =
      a i - (if i = j then a i else 0) := by
    intro j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, not_lt.mpr hij.le]
    · simp [hij]
    · simp [hij, hij.ne', not_lt.mpr hij.le]
  simp_rw [t, Finset.sum_sub_distrib, Finset.sum_ite_eq, hi, Finset.sum_const, Finset.card_range]
  simp; ring

open MvPolynomial in
private lemma sum_norm_sq_diag_eq_sum_range_min (p q : ℕ) (h : ℕ → ℝ) :
    ∑ a : Fin p, ∑ b : Fin q, ‖if (a : ℕ) = b then ((h a : ℝ) : ℂ) else 0‖ ^ 2 =
      ∑ i ∈ Finset.range (min p q), h i ^ 2 := by
  have hrow : ∀ a : Fin p, ∑ b : Fin q, ‖if (a : ℕ) = b then ((h a : ℝ) : ℂ) else 0‖ ^ 2 =
      if (a : ℕ) < q then h a ^ 2 else 0 := by
    intro a
    rw [Fin.sum_univ_eq_sum_range (fun j => ‖if (a : ℕ) = j then ((h a : ℝ) : ℂ) else 0‖ ^ 2) q]
    have : ∀ j, ‖if (a : ℕ) = j then ((h a : ℝ) : ℂ) else 0‖ ^ 2 =
        if (a : ℕ) = j then h a ^ 2 else 0 := by
      intro j; split_ifs <;> simp
    simp_rw [this, Finset.sum_ite_eq, Finset.mem_range]
  simp_rw [hrow]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < q then h i ^ 2 else 0) p, ← Finset.sum_filter]
  congr 1
  ext i; simp [lt_min_iff]

open MvPolynomial in
private lemma hsNorm_aOf_eq_sqrt_two_mul_sum_sq (p q : ℕ) (h : ℕ → ℝ) :
    _root_.Formalism.BasicNotions.TH.hsNorm (_root_.Formalism.MainNotions.SchurIrreducible.aOf p q h) = Real.sqrt (2 * ∑ i ∈ Finset.range (min p q), h i ^ 2) := by
  simp only [_root_.Formalism.BasicNotions.TH.hsNorm, _root_.Formalism.MainNotions.SchurIrreducible.aOf, _root_.Formalism.MainNotions.SchurIrreducible.pOf]
  simp
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))), sum_norm_sq_diag_eq_sum_range_min, ← two_mul,
    Real.sqrt_mul (by norm_num)]

open MvPolynomial in

theorem _root_.GlobalTheory.PolarJacBound.polarJac_le_exp : ∀ (p q : ℕ) (h : ℕ → ℝ), (∏ i ∈ Finset.range (min p q), _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * (max p q - min p q))) * (∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2 else 1) ≤ Real.exp (((p + q : ℕ) : ℝ) * Real.sqrt (2 * (min p q : ℕ)) * _root_.Formalism.BasicNotions.TH.hsNorm (_root_.Formalism.MainNotions.SchurIrreducible.aOf p q h)) := by
  intro p q h
  set r := Finset.range (min p q) with hr
  set k := max p q - min p q with hk
  have hA : ∏ i ∈ r, _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * k) ≤
      ∏ i ∈ r, Real.exp ((2 + 2 * (k : ℝ)) * |h i|) := by
    refine Finset.prod_le_prod
      (fun i _ => mul_nonneg (shc_nonneg' _) (pow_nonneg (shc_nonneg' _) _)) fun i _ => ?_
    calc _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * k)
        ≤ Real.exp |2 * h i| * Real.exp |h i| ^ (2 * k) :=
          mul_le_mul (shc_le_exp_abs _)
            (pow_le_pow_left₀ (shc_nonneg' _) (shc_le_exp_abs _) _)
            (pow_nonneg (shc_nonneg' _) _) (Real.exp_pos _).le
      _ = Real.exp ((2 + 2 * (k : ℝ)) * |h i|) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, abs_mul, abs_two]; push_cast; ring_nf
  have hB : (∏ i ∈ r, ∏ j ∈ r,
        if i < j then (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2 else 1) ≤
      ∏ i ∈ r, ∏ j ∈ r, Real.exp (if i < j then 4 * (|h i| + |h j|) else 0) := by
    refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) fun i _ =>
      Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
    · split_ifs
      · exact sq_nonneg _
      · exact zero_le_one
    · split_ifs
      · exact sq_nonneg _
      · exact zero_le_one
    · split_ifs
      · have h1 : _root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j) ≤
            Real.exp (2 * (|h i| + |h j|)) := by
          calc _root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)
              ≤ Real.exp |h i - h j| * Real.exp |h i + h j| :=
                mul_le_mul (shc_le_exp_abs _) (shc_le_exp_abs _) (shc_nonneg' _)
                  (Real.exp_pos _).le
            _ = Real.exp (|h i - h j| + |h i + h j|) := (Real.exp_add _ _).symm
            _ ≤ Real.exp (2 * (|h i| + |h j|)) := by
                gcongr
                linarith [abs_sub (h i) (h j), abs_add_le (h i) (h j)]
        calc (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2
            ≤ Real.exp (2 * (|h i| + |h j|)) ^ 2 :=
              pow_le_pow_left₀ (mul_nonneg (shc_nonneg' _) (shc_nonneg' _)) h1 2
          _ = Real.exp (4 * (|h i| + |h j|)) := by rw [← Real.exp_nat_mul]; ring_nf
      · simp
  set S := ∑ i ∈ r, |h i| with hS
  set Q := ∑ i ∈ r, h i ^ 2 with hQ
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCS : S ^ 2 ≤ (min p q : ℕ) * Q := by
    have := Finset.sum_mul_sq_le_sq_mul_sq r (fun _ => (1 : ℝ)) (fun i => |h i|)
    simpa [hr, sq_abs] using this
  have hkey : 2 * S ≤ Real.sqrt (2 * (min p q : ℕ)) * Real.sqrt (2 * Q) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hn : ((p + q : ℕ) : ℝ) = (max p q : ℕ) + (min p q : ℕ) := by
    rw [← Nat.cast_add, max_add_min]
  have hkR : (k : ℝ) = (max p q : ℕ) - (min p q : ℕ) := by
    rw [hk, Nat.cast_sub min_le_max]
  calc _ ≤ (∏ i ∈ r, Real.exp ((2 + 2 * (k : ℝ)) * |h i|)) *
        ∏ i ∈ r, ∏ j ∈ r, Real.exp (if i < j then 4 * (|h i| + |h j|) else 0) :=
        mul_le_mul hA hB (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
          split_ifs
          · exact sq_nonneg _
          · exact zero_le_one) (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
    _ = Real.exp ((2 + 2 * (k : ℝ)) * S + 4 * (((min p q : ℕ) : ℝ) - 1) * S) := by
        simp_rw [← Real.exp_sum]
        rw [← Real.exp_add]
        congr 1
        rw [hS, hr, sum_sum_ite_lt_four_mul_add_eq, ← Finset.mul_sum]
        ring
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [hsNorm_aOf_eq_sqrt_two_mul_sum_sq, mul_assoc, hn]
        have hm0 : (0 : ℝ) ≤ (min p q : ℕ) := Nat.cast_nonneg _
        have hM0 : (0 : ℝ) ≤ (max p q : ℕ) := Nat.cast_nonneg _
        rw [hkR]
        nlinarith [mul_le_mul_of_nonneg_left hkey (add_nonneg hM0 hm0)]

end GlobalTheory.PolarJacBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolariseIntegral
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial MeasureTheory

namespace GlobalTheory.SchurPol

theorem polarise_integral {G H : Type*} [MeasurableSpace G] [AddCommGroup H] [Module ℂ H]
    (μ : Measure G) (F : H → H → G → ℂ) (R : H → H → ℂ) (c : ℂ)
    (hF : ∀ x y g, F x y g = (1 / 4 : ℂ) * ((F (x + y) (x + y) g - F (x - y) (x - y) g) +
      c * (F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g)))
    (hR : ∀ x y, R x y = (1 / 4 : ℂ) * ((R (x + y) (x + y) - R (x - y) (x - y)) +
      c * (R (x + Complex.I • y) (x + Complex.I • y) -
        R (x - Complex.I • y) (x - Complex.I • y))))
    (hd : ∀ x, Integrable (F x x) μ ∧ ∫ g, F x x g ∂μ = R x x) (x y : H) :
    Integrable (F x y) μ ∧ ∫ g, F x y g ∂μ = R x y := by
  have e : F x y = fun g => (1 / 4 : ℂ) * ((F (x + y) (x + y) g - F (x - y) (x - y) g) +
      c * (F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g)) := funext (hF x y)
  have h1 : Integrable (fun g => F (x + y) (x + y) g - F (x - y) (x - y) g) μ :=
    (hd _).1.sub (hd _).1
  have h2 : Integrable (fun g => F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g) μ := (hd _).1.sub (hd _).1
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (h1.add (h2.const_mul c)).const_mul _
  · rw [hR x y]
    simp only [hF x y]
    rw [integral_const_mul, integral_add h1 (h2.const_mul c), integral_const_mul,
      integral_sub (hd _).1 (hd _).1, integral_sub (hd _).1 (hd _).1,
      (hd _).2, (hd _).2, (hd _).2, (hd _).2]

theorem schur_half {p q : ℕ} {T : GrpData p q} (D : DSRep T) (w u₁ u₂ : D.U.H) :
    Integrable (fun g => inner ℂ w (D.U.π g u₁) * star (inner ℂ w (D.U.π g u₂))) T.haar ∧
      ∫ g, inner ℂ w (D.U.π g u₁) * star (inner ℂ w (D.U.π g u₂)) ∂T.haar =
        ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ w w) := by
  refine polarise_integral T.haar
    (fun x y g => inner ℂ w (D.U.π g x) * star (inner ℂ w (D.U.π g y)))
    (fun x y => ((D.fdeg : ℂ))⁻¹ * inner ℂ y x * star (inner ℂ w w)) Complex.I ?_ ?_ ?_ u₁ u₂
  · intro x y g
    simp only [map_add, map_sub, map_smul, inner_add_right, inner_sub_right, inner_smul_right,
      star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I]
    linear_combination (1 / 2 : ℂ) * (inner ℂ w (D.U.π g x) * (starRingEnd ℂ) (inner ℂ w (D.U.π g y))
      - inner ℂ w (D.U.π g y) * (starRingEnd ℂ) (inner ℂ w (D.U.π g x))) * Complex.I_mul_I
  · intro x y
    simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_add_left, inner_sub_left,
      inner_smul_left, Complex.conj_I]
    linear_combination (1 / 2 : ℂ) * ((D.fdeg : ℂ))⁻¹ * star (inner ℂ w w) *
      (inner ℂ y x - inner ℂ x y) * Complex.I_mul_I
  · intro x
    have e : ∀ g, inner ℂ w (D.U.π g x) * star (inner ℂ w (D.U.π g x)) =
        ((‖inner ℂ w (D.U.π g x)‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e]
    refine ⟨(D.schur x w).1.ofReal, ?_⟩
    rw [integral_complex_ofReal, (D.schur x w).2, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K]
    simp only [Complex.star_def, map_pow, Complex.coe_algebraMap, Complex.conj_ofReal]
    push_cast
    ring

theorem schur_polarised (p q : ℕ) (T : GrpData p q) (D : DSRep T) (u₁ w₁ u₂ w₂ : D.U.H) :
    Integrable (fun g => inner ℂ w₁ (D.U.π g u₁) * star (inner ℂ w₂ (D.U.π g u₂))) T.haar ∧
      ∫ g, inner ℂ w₁ (D.U.π g u₁) * star (inner ℂ w₂ (D.U.π g u₂)) ∂T.haar =
        ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ w₂ w₁) := by
  refine polarise_integral T.haar
    (fun x y g => inner ℂ x (D.U.π g u₁) * star (inner ℂ y (D.U.π g u₂)))
    (fun x y => ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ y x)) (-Complex.I) ?_ ?_
    (fun x => schur_half D x u₁ u₂) w₁ w₂
  · intro x y g
    simp only [inner_add_left, inner_sub_left, inner_smul_left, map_add, map_sub, map_mul, map_neg,
      star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I, neg_neg]
    linear_combination (1 / 2 : ℂ) *
      (inner ℂ x (D.U.π g u₁) * (starRingEnd ℂ) (inner ℂ y (D.U.π g u₂))
      - inner ℂ y (D.U.π g u₁) * (starRingEnd ℂ) (inner ℂ x (D.U.π g u₂))) * Complex.I_mul_I
  · intro x y
    simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_add_left, inner_sub_left,
      inner_smul_left, Complex.conj_I, Complex.star_def, map_add, map_sub, map_mul, map_neg,
      neg_neg]
    linear_combination (1 / 2 : ℂ) * ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ *
      ((starRingEnd ℂ) (inner ℂ y x) - (starRingEnd ℂ) (inner ℂ x y)) * Complex.I_mul_I

end GlobalTheory.SchurPol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

abbrev Var (ι : Type) (d a : ℕ) : Type := ι × Fin d × Fin a

abbrev Pol (ι : Type) (d a : ℕ) : Type := MvPolynomial (Var ι d a) ℂ

abbrev Tup (ι : Type) (a d : ℕ) (n : ι → ℕ) : Type := ∀ τ, Fin (n τ) → {s : Fin a → Fin d // StrictMono s}

variable {ι : Type}

def minorAt (τ : ι) {a d : ℕ} (s : Fin a → Fin d) : Pol ι d a :=
  (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)).det

variable [Fintype ι]

def prodMinors {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : Pol ι d a := ∏ τ, ∏ j, minorAt τ (T τ j).1

def rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ i' : Fin d, C (κ y.1 i' y.2.1) * X (y.1, i', y.2.2)

def colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ j' : Fin a, C (g y.1 j' y.2.2) * X (y.1, y.2.1, j')

def detChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) : ℂ := ∏ τ, (g τ).det ^ n τ

def inv (a d : ℕ) (n : ι → ℕ) : Submodule ℂ (Pol ι d a) where
  carrier := {P | ∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ,
    colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P = detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • P}
  add_mem' := by
    intro P Q hP hQ g
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, hP g, hQ g, smul_add]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c P hP g
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hP g, smul_comm]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem colSub_minorAt {a d : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (s : Fin a → Fin d) :
    colSub g (minorAt τ s) = (g τ).det • minorAt τ s := by
  unfold minorAt
  rw [AlgHom.map_det]
  have hM : (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).mapMatrix (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) =
      (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) * (g τ).map C := by
    ext i i'
    simp [colSub, Matrix.mul_apply, mul_comm]
  rw [hM, Matrix.det_mul, show ((g τ).map C).det = C (g τ).det from ((C : ℂ →+* Pol ι d a).map_det (g τ)).symm, smul_eq_C_mul, mul_comm]

theorem colSub_prodMinors {a d : ℕ} {n : ι → ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (T : Tup ι a d n) :
    colSub g (prodMinors T) = detChar n g • prodMinors T := by
  unfold prodMinors detChar
  simp only [map_prod, colSub_minorAt, smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, map_prod, map_pow]

theorem prodMinors_mem_inv {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : prodMinors T ∈ inv a d n :=
  fun g => colSub_prodMinors _ T

theorem colSub_rowSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    colSub g (rowSub κ P) = rowSub κ (colSub g P) := by
  have : (colSub g).comp (rowSub κ) = (rowSub κ).comp (colSub g) := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [AlgHom.comp_apply, rowSub, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem rowSub_mem_inv {a d : ℕ} {n : ι → ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) {P : Pol ι d a} (hP : P ∈ inv a d n) :
    rowSub κ P ∈ inv a d n := by
  intro g
  rw [colSub_rowSub, hP g, map_smul]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

open Classical

variable {ι : Type} [Fintype ι]

theorem fockS_conj {σ : Type} (f g : MvPolynomial σ ℂ) :
    Formalism.L2.DIV.fockS f g = starRingEnd ℂ (Formalism.L2.DIV.fockS g f) := by
  rw [Formalism.L2.DIV.fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_natCast, RCLike.star_def, Complex.conj_conj]
  ring

theorem fockS_self_re_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (Formalism.L2.DIV.fockS f f).re := by
  unfold Formalism.L2.DIV.fockS
  rw [Complex.re_sum]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hf
  have hms : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have key : ∀ k ∈ f.support, (star (f.coeff k) * f.coeff k * (Formalism.L2.DIV.mfact k : ℂ)).re =
      ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ) := by
    intro k _
    rw [RCLike.star_def, mul_comm (starRingEnd ℂ _), Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl key]
  have hpos : 0 < ‖f.coeff m‖ ^ 2 * (Formalism.L2.DIV.mfact m : ℝ) := by
    have : (0 : ℝ) < Formalism.L2.DIV.mfact m := by
      unfold Formalism.L2.DIV.mfact; exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
    positivity
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k => ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ))
    (fun k _ => by positivity) hms)

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnOfPsiOn
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiUnitOfPsiOn

theorem injective_of_isIso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] : Function.Injective f.hom := by
  intro a b e
  have := congrArg (inv f).hom e
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

theorem mem_wchart1 {Y B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (z : Y) (i : M.ι) (hz : φ z ∈ M.U i) :
    z ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => i) := Set.mem_iInter.2 fun _ => hz

theorem psiUnitOn_of_psiOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), PsiOn D W → ∀ y : D.X, PsiUnitOn D y (W : Set (Spec (CommRingCat.of R))) := by
  intro R _ _ D W ψ y j V _ hVW hj h
  obtain ⟨p, rfl⟩ : ∃ p, j = fun _ => p := ⟨j PUnit.unit, funext fun _ => rfl⟩
  have hle : W.ι ⁻¹ᵁ V ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    fun z hz => mem_wchart1 _ _ _ _ (hj hz)
  have hVr : V ≤ W.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact hVW
  haveI := W.ι.isIso_app V hVr
  set u : Γ(W.toScheme, W.ι ⁻¹ᵁ V)ˣ := res hle ((ψ.psi y).s (fun _ => p)) with hu
  set r : Γ(Spec (CommRingCat.of R), V) := (inv (W.ι.app V)).hom u.val with hr
  have hr' : (W.ι.app V).hom r = u.val := by
    rw [hr, ← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  refine ⟨r, u.isUnit.map (inv (W.ι.app V)).hom, ?_⟩
  have hKr : jK R ⁻¹ᵁ V ≤ (jK R ⁻¹ᵁ W).ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]; exact fun z hz => hVW hz
  haveI := (jK R ⁻¹ᵁ W).ι.isIso_app (jK R ⁻¹ᵁ V) hKr
  apply injective_of_isIso ((jK R ⁻¹ᵁ W).ι.app (jK R ⁻¹ᵁ V))
  apply fn_ext
  intro z hz
  have hι : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hzV : jK R ((jK R ⁻¹ᵁ W).ι z) ∈ V := hz
  have hpt : W.ι ((jK R ∣_ W) z) = jK R ((jK R ⁻¹ᵁ W).ι z) := congrArg (fun q => q z) hι
  have hm : (jK R ∣_ W) z ∈ W.ι ⁻¹ᵁ V := by
    show W.ι ((jK R ∣_ W) z) ∈ V
    rw [hpt]; exact hzV
  have h₁ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hm)
  have h₂ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ⁻¹ᵁ W).ι ≫ D.xK y) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hzV)
  have e₃ := (gm_pullGen D.P.L _ _ (ψ.psi y) (jK R ∣_ W) (𝟙 _) z (fun _ => p) h₁).symm.trans
    ((gm_corr D.P.L (ψ.psi_eq y) (𝟙 _) z p h₁ h₂).trans
      (gm_pullGen D.P.L _ _ (D.psi y) (jK R ⁻¹ᵁ W).ι (𝟙 _) z (fun _ => p) h₂))
  rw [Category.id_comp, Category.id_comp] at e₃
  have l₁ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz ((jK R).app V |>.hom r)
  have l₂ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz
    (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi y).s (fun _ => p)).val)
  rw [Category.id_comp] at l₁ l₂
  rw [l₁, l₂, gs_pull _ _ z V hzV r, ← hι, ← gs_pull _ _ z V hm r, hr', hu,
    gs_unit _ z _ hm]
  erw [gm_res _ z hle hm]
  erw [gs_res _ z h hz]
  rw [gs_unit _ z _ (h hz)]
  exact congrArg Units.val e₃

end GlobalTheory.PsiUnitOfPsiOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftHarishChandraInductionEqTwistedStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → shLift s (hc a b α β n) = hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n := by
  first | (exact @GlobalTheory.Shin.shLift_hc_eq_hcTw) | (exact GlobalTheory.Shin.shLift_hc_eq_hcTw) | (intros; apply GlobalTheory.Shin.shLift_hc_eq_hcTw  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomologyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etC_a2 : GlobalTheory.EtC.A2 := by
  first | exact @GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology | exact GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology | (intros; apply GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationPrimeEqStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_henselisation_prime_eq : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j ∧
      ∃ (D₁ : Type) (_ : CommRing D₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁)
        (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ ∧
        ∀ σ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ →
          Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_torsor) | (exact GlobalTheory.KeyOriginCut.exists_stage_torsor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_torsor  <;> assumption)
end

