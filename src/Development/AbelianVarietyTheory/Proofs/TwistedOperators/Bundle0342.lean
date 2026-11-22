import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGLZetaSumTrivialParameterSubOneLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GLZetaBound

theorem norm_mul_sub_one_le {a b : ℂ} {c : ℝ} (hc : 0 ≤ c) {m k : ℕ}
    (ha : ‖a - 1‖ ≤ (1 + c) ^ m - 1) (hb : ‖b - 1‖ ≤ (1 + c) ^ k - 1) :
    ‖a * b - 1‖ ≤ (1 + c) ^ (m + k) - 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [e, pow_add]
  have h1 : ‖(a - 1) * (b - 1)‖ ≤ ((1 + c) ^ m - 1) * ((1 + c) ^ k - 1) := by
    rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)
  calc ‖(a - 1) * (b - 1) + (a - 1) + (b - 1)‖
      ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ + ‖b - 1‖ := norm_add₃_le
    _ ≤ ((1 + c) ^ m - 1) * ((1 + c) ^ k - 1) + ((1 + c) ^ m - 1) + ((1 + c) ^ k - 1) := by
        gcongr
    _ = (1 + c) ^ m * (1 + c) ^ k - 1 := by ring

theorem norm_inv_one_sub_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have h1 : 1 - ‖y‖ ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    rwa [norm_one] at this
  have h2 : (1 : ℂ) - y ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have e : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
  rw [e, norm_div, div_le_iff₀ (norm_pos_iff.2 h2)]
  nlinarith [norm_nonneg y]

theorem norm_eulerFac_sub_one_le {B : Multiset ℂˣ} {x : ℂ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ ≤ δ) : ‖GlobalTheory.LFun.eulerFac B x - 1‖ ≤ (1 + 2 * δ) ^ B.card - 1 := by
  rw [GlobalTheory.LFun.eulerFac_eq_prod]
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih =>
    have h1 := ih fun c hc => h c (Multiset.mem_cons_of_mem hc)
    have h2 := h b (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm B.card 1]
    refine norm_mul_sub_one_le (by linarith) ?_ h1
    rw [pow_one]
    have := norm_inv_one_sub_sub_one_le (h2.trans hδ)
    linarith

theorem norm_prod_one_sub_sub_one_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h : ∀ i ∈ s, ‖z i‖ ≤ δ) : ‖∏ i ∈ s, (1 - z i) - 1‖ ≤ (1 + 2 * δ) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := ih fun c hc => h c (Finset.mem_insert_of_mem hc)
    have h2 := h a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_comm s.card 1]
    refine norm_mul_sub_one_le (by linarith) ?_ h1
    rw [pow_one]
    have e : (1 - z a) - 1 = -z a := by ring
    rw [e, norm_neg]
    linarith

theorem one_add_two_mul_pow_sub_one_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (m : ℕ) :
    (1 + 2 * δ) ^ m - 1 ≤ 3 ^ m * δ := by
  have key : (1 + 2 * δ) ^ m - 1 ≤ (3 ^ m - 1) * δ := by
    induction m with
    | zero => simp
    | succ m ih =>
      have h3 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      have hf : 0 ≤ (1 + 2 * δ) ^ m - 1 := by
        have : (1 : ℝ) ≤ (1 + 2 * δ) ^ m := one_le_pow₀ (by linarith)
        linarith
      have e : (1 + 2 * δ) ^ (m + 1) - 1 = (1 + 2 * δ) * ((1 + 2 * δ) ^ m - 1) + 2 * δ := by ring
      rw [e, pow_succ]
      have : (1 + 2 * δ) * ((1 + 2 * δ) ^ m - 1) ≤ (3 / 2) * ((3 ^ m - 1) * δ) := by
        have : 1 + 2 * δ ≤ 3 / 2 := by linarith
        exact mul_le_mul this ih hf (by norm_num)
      nlinarith
  have : (3 ^ m - 1) * δ ≤ 3 ^ m * δ := by nlinarith
  linarith

theorem norm_trivial_sub_one_le : ∀ (q : ℕ), 2 ≤ q → ∀ (r t : ℕ), r + 5 ≤ t → ∀ (B : Multiset ℂˣ), B.card = r → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ X : ℂ, ‖X‖ = (q : ℝ) ^ (-((1 + (t : ℝ)) / 2)) → ‖eulerFac B X * eulerFac (B.map fun β => β⁻¹) X * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((q : ℂ) ^ i)⁻¹) - 1‖ ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro q hq r t hrt B hB hβ X hX
  set δ : ℝ := ((q : ℝ) ^ 2)⁻¹ with hδdef
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : δ ≤ 1 / 4 := by
    rw [hδdef]
    have : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hrt' : (r : ℝ) + 5 ≤ t := by exact_mod_cast hrt
  have hbx : (q : ℝ) ^ (((r : ℝ) - 1) / 2) * ‖X‖ ≤ δ := by
    rw [hX, ← Real.rpow_add hq0]
    have e : δ = (q : ℝ) ^ (-(2 : ℝ)) := by
      rw [hδdef, Real.rpow_neg hq0.le, Real.rpow_two]
    rw [e]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    linarith
  have hB1 : ∀ b ∈ B, ‖(b : ℂ) * X‖ ≤ δ := by
    intro b hb
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hβ b hb).1 (norm_nonneg _)).trans hbx
  have hB2 : ∀ b ∈ B.map (fun β : ℂˣ => β⁻¹), ‖(b : ℂ) * X‖ ≤ δ := by
    intro b hb
    obtain ⟨β, hβB, rfl⟩ := Multiset.mem_map.1 hb
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hβ β hβB).2 (norm_nonneg _)).trans hbx
  have h1 := norm_eulerFac_sub_one_le hδ0 (by linarith) hB1
  have h2 := norm_eulerFac_sub_one_le hδ0 (by linarith) hB2
  have h3 := norm_prod_one_sub_sub_one_le (Finset.Ioc t (r + t)) (fun i => ((q : ℂ) ^ i)⁻¹) hδ0
    (by
      intro i hi
      have hi2 : 2 ≤ i := by
        have := (Finset.mem_Ioc.1 hi).1; omega
      rw [norm_inv, norm_pow, Complex.norm_natCast, hδdef]
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ hq1 hi2)
  rw [Multiset.card_map] at h2
  rw [Nat.card_Ioc, show r + t - t = r by omega] at h3
  rw [hB] at h1 h2
  have h12 := norm_mul_sub_one_le (by linarith) h1 h2
  have h123 := norm_mul_sub_one_le (by linarith) h12 h3
  have h4 := one_add_two_mul_pow_sub_one_le hδ0 hδ (r + r + r)
  have e27 : (3 : ℝ) ^ (r + r + r) = 27 ^ r := by
    rw [show r + r + r = 3 * r by ring, pow_mul]; norm_num
  rw [e27] at h4
  exact h123.trans h4

end GlobalTheory.GLZetaBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormUnitaryZetaSumTrivialBoundSubOneLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.UnitaryBound

open GlobalTheory.LFun

theorem norm_prod_sub_one_le (c : ℝ) (M : Multiset ℂ) (h : ∀ z ∈ M, ‖z - 1‖ ≤ c) :
    ‖M.prod - 1‖ ≤ (1 + c) ^ M.card - 1 := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have h1 := ih fun z hz => h z (Multiset.mem_cons_of_mem hz)
    have h2 := h a (Multiset.mem_cons_self _ _)
    have hc : 0 ≤ c := (norm_nonneg _).trans h2
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have e : a * M.prod - 1 = (a - 1) * (M.prod - 1) + (a - 1) + (M.prod - 1) := by ring
    rw [e]
    have h3 : ‖(a - 1) * (M.prod - 1)‖ ≤ c * ((1 + c) ^ M.card - 1) := by
      rw [norm_mul]; exact mul_le_mul h2 h1 (norm_nonneg _) hc
    have h4 : ‖(a - 1) * (M.prod - 1) + (a - 1) + (M.prod - 1)‖ ≤
        ‖(a - 1) * (M.prod - 1)‖ + ‖a - 1‖ + ‖M.prod - 1‖ :=
      by
        linarith [norm_add_le ((a - 1) * (M.prod - 1) + (a - 1)) (M.prod - 1), norm_add_le ((a - 1) * (M.prod - 1)) (a - 1)]
    nlinarith

theorem norm_inv_one_sub_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) : ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have h1 : 1 / 2 ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    rw [norm_one] at this
    linarith
  have hne : (1 - y) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    norm_num at h1
  have hm : (1 - y) * (1 - y)⁻¹ = 1 := mul_inv_cancel₀ hne
  have e : (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by linear_combination hm
  rw [e, norm_mul, norm_inv]
  have hpos : 0 < ‖1 - y‖ := by linarith
  rw [mul_inv_le_iff₀ hpos]
  nlinarith [norm_nonneg y]

theorem one_add_pow_sub_one_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    (1 + c) ^ n - 1 ≤ (2 ^ n - 1) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    rw [pow_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + c),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2) hc0) (sub_nonneg.2 hc1)]

theorem norm_zetaSum_sub_one_le : ∀ (q r t : ℕ), 2 ≤ q → r + 5 ≤ t → ∀ α : Fin (r / 2) → ℂˣ,
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ‖eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) *
      ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) - 1‖ ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro q r t hq hrt α hα
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  set δ : ℝ := ((q : ℝ) ^ 2)⁻¹ with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ, inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have key : ∀ a b : ℕ, a + 2 ≤ b → (q : ℝ) ^ a * ((q : ℝ) ^ b)⁻¹ ≤ δ := by
    intro a b hab
    obtain ⟨k, rfl⟩ : ∃ k, b = a + 2 + k := ⟨b - (a + 2), by omega⟩
    have hpa : (0 : ℝ) < (q : ℝ) ^ a := by positivity
    rw [show (q : ℝ) ^ (a + 2 + k) = (q : ℝ) ^ a * ((q : ℝ) ^ 2 * (q : ℝ) ^ k) by ring, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hpa.ne', one_mul, hδ]
    apply inv_anti₀ (by positivity)
    have : (1 : ℝ) ≤ (q : ℝ) ^ k := one_le_pow₀ hq1
    nlinarith [show (0 : ℝ) < (q : ℝ) ^ 2 by positivity]
  have hbound : ((q : ℝ) ^ 2) ^ (((r : ℝ) - 1) / 2) ≤ (q : ℝ) ^ r := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hent : ∀ b ∈ bcParam r α, ‖(b : ℂ)‖ ≤ (q : ℝ) ^ r := by
    intro b hb
    simp only [bcParam, Multiset.mem_add, Multiset.mem_map, Finset.mem_univ_val, true_and,
      Multiset.mem_replicate] at hb
    have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    rcases hb with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨_, rfl⟩
    · exact (hα i).2.trans hbound
    · rw [Units.val_inv_eq_inv_val, norm_inv]
      have hpos : 0 < ((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hq2 _
      calc ‖(α i : ℂ)‖⁻¹ ≤ (((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)))⁻¹ := inv_anti₀ hpos (hα i).1
        _ = ((q : ℝ) ^ 2) ^ (((r : ℝ) - 1) / 2) := by rw [Real.rpow_neg hq2.le, inv_inv]
        _ ≤ _ := hbound
    · simp only [Units.val_one, norm_one]
      exact one_le_pow₀ hq1
  set x : ℂ := ((q : ℂ) ^ (t + 1))⁻¹ with hx
  have hxn : ‖x‖ = ((q : ℝ) ^ (t + 1))⁻¹ := by rw [hx, norm_inv, norm_pow, Complex.norm_natCast]
  set M1 : Multiset ℂ := (bcParam r α).map fun b : ℂˣ => (1 - (b : ℂ) * x)⁻¹ with hM1
  set M2 : Multiset ℂ := (Finset.range r).val.map fun j => 1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹ with hM2
  have heq : eulerFac (bcParam r α) x * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) =
      (M1 + M2).prod := by
    rw [Multiset.prod_add, eulerFac_eq_prod]
    rfl
  have hcard : (M1 + M2).card = r + r := by
    simp [hM1, hM2, GlobalTheory.LGrp.card_bcParam]
  have hfac : ∀ z ∈ M1 + M2, ‖z - 1‖ ≤ 2 * δ := by
    intro z hz
    rcases Multiset.mem_add.1 hz with hz | hz
    · obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hz
      have hbx : ‖(b : ℂ) * x‖ ≤ δ := by
        rw [norm_mul, hxn]
        exact (mul_le_mul_of_nonneg_right (hent b hb) (by positivity)).trans (key r (t + 1) (by omega))
      exact (norm_inv_one_sub_sub_one_le (by linarith)).trans (by linarith)
    · obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hz
      have hj' : j < r := Finset.mem_range.1 hj
      have : ‖(1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) - 1‖ = (q : ℝ) ^ j * ((q : ℝ) ^ (r + t))⁻¹ := by
        rw [sub_sub_cancel_left, norm_neg, norm_mul, norm_inv, norm_pow, norm_pow, norm_neg, Complex.norm_natCast]
      rw [this]
      linarith [key j (r + t) (by omega)]
  rw [heq]
  refine (norm_prod_sub_one_le _ _ hfac).trans ?_
  rw [hcard]
  refine (one_add_pow_sub_one_le (by linarith) (by linarith) _).trans ?_
  have h4 : (2 : ℝ) ^ (r + r) = 4 ^ r := by rw [← two_mul, pow_mul]; norm_num
  have ha : (1 : ℝ) ≤ 4 ^ r := one_le_pow₀ (by norm_num)
  have h16 : (16 : ℝ) ^ r = (4 ^ r) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h27 : (16 : ℝ) ^ r ≤ 27 ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
  have hk : 2 * ((4 : ℝ) ^ r - 1) ≤ 27 ^ r := by nlinarith
  rw [h4]
  calc ((4 : ℝ) ^ r - 1) * (2 * δ) = (2 * ((4 : ℝ) ^ r - 1)) * δ := by ring
    _ ≤ 27 ^ r * δ := mul_le_mul_of_nonneg_right hk hδ0

end GlobalTheory.FinZeta.UnitaryBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupTranslateHeightBound
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelHeight
open GlobalTheory.HolDict.ShortVec (intRing finPr)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (finCoord)

theorem openSub (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F,
      (∀ i j k, a i j k ∈ intRing D.host.F) →
      (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
        Module.finBasis D.host.F D.host.E k : WO V W) ∈ U :=
  GlobalTheory.T.exists_natMul_integralMatrices_subset_openAddSubgroup D V W U hU

theorem eq_sum_of_infPart (D : D7) (z : AE D) (hz : infPart D z = 0) :
    z = ∑ k, pairA D.host.F 0 (finCoord D (finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k :=
  GlobalTheory.T.eq_sum_finiteCoords_of_infinitePart_zero D z hz

theorem exists_denom_mul (D : D7) : ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
    (∀ k, (e₁ : Af D.host.F) * finCoord D a k ∈ intRing D.host.F) →
    (∀ k, (e₂ : Af D.host.F) * finCoord D b k ∈ intRing D.host.F) →
    ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * finCoord D (a * b) k ∈ intRing D.host.F :=
  GlobalTheory.T.finiteAdeleTensorCoords_mul_denominator_bound D

theorem exists_denom_integral (D : D7) : ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x →
    ∀ k, (d : Af D.host.F) * finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ intRing D.host.F :=
  GlobalTheory.T.exists_fixed_denominator_finiteCoords_integral D

theorem infPart_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) : (finLift z).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i j) = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] z i j := rfl
  simp only [finLift, Matrix.map_apply, Matrix.zero_apply]
  rw [h1, TensorProduct.zero_tmul]

theorem finPr_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) :
    (finLift z).map (finPr D) = z.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  ext i j
  rfl

theorem map_mul_three_alt {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) R)
    (B : Matrix (Fin b) (Fin c) R) (C : Matrix (Fin c) (Fin d) R) : (A * B * C).map f = A.map f * B.map f * C.map f := by
  rw [Matrix.map_mul, Matrix.map_mul]

theorem tmul_natCast_mul {D : D7} (N : ℕ) (e : D.host.E) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  rw [Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finPr_Y {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (N : ℕ)
    (x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) : WO V W).map (finPr D) =
      ((N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e)) *
        P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  have e1 : ((N : D.host.E) • x).map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j
    exact tmul_natCast_mul N (x i j)
  have e2 : (P.map (incA D)).map (finPr D) = P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j; rfl
  rw [Matrix.map_mul, finPr_finLift, e1, e2]

theorem finPr_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W).map (finPr D) =
      Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * Y.map (finPr D) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem infPart_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (z : Matrix (Fin W.rank) (Fin r) D.host.E)
    (g : GA D V) (h : GA D W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) (HMul.hMul (finLift z) (P.map (incA D)) : WO V W))
      (Formalism.L2.Theta.mt V g) : WO V W).map (infPart D) = 0 := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, infPart_finLift]
  simp

theorem actO_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    actO V W g h (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W) = Y := by
  have e1 : Formalism.L2.Theta.mt W h * Formalism.L2.Theta.mt W h⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  simp only [actO, ← Matrix.mul_assoc]
  rw [e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]

theorem entry_of_map_eq {m n : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : Matrix (Fin m) (Fin n) R)
    (c : S) (w : Matrix (Fin m) (Fin n) S) (h : u.map f = c • w) (i : Fin m) (j : Fin n) : f (u i j) = c * w i j := by
  have := congrFun (congrFun h i) j
  simpa using this

theorem openSubY (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U := by
  obtain ⟨M₀, hM₀, hsub⟩ := openSub D V W U hU
  refine ⟨M₀, hM₀, fun y hy hc => ?_⟩
  choose b hb hbe using hc
  convert hsub b hb using 1
  ext i j
  rw [Matrix.of_apply, eq_sum_of_infPart D (y i j) (by simpa using congrFun (congrFun hy i) j)]
  exact Finset.sum_congr rfl fun k _ => by rw [hbe]

def Den (D : D7) (e : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) : Prop :=
  ∀ k, (e : Af D.host.F) * finCoord D z k ∈ intRing D.host.F

theorem den_sum {D : D7} {e : ℕ} {ι : Type} (s : Finset ι) (f : ι → Af D.host.F ⊗[D.host.F] D.host.E)
    (h : ∀ i ∈ s, Den D e (f i)) : Den D e (∑ i ∈ s, f i) := fun k => by
  unfold finCoord
  rw [map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  exact (intRing D.host.F).sum_mem fun i hi => h i hi k

theorem den_matMul {D : D7} {c : ℕ} (hc : ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
      Den D e₁ a → Den D e₂ b → Den D (c * e₁ * e₂) (a * b)) {m n p : ℕ} {e₁ e₂ : ℕ}
    (A : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (B : Matrix (Fin n) (Fin p) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hA : ∀ i j, Den D e₁ (A i j)) (hB : ∀ i j, Den D e₂ (B i j)) : ∀ i j, Den D (c * e₁ * e₂) ((A * B) i j) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact den_sum _ _ fun l _ => hc e₁ e₂ _ _ (hA i l) (hB l j)

theorem mt_mul_inv {D : D7} (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mt_inv_mul {D : D7} (V : HSp D) (g : GA D V) : mt V g⁻¹ * mt V g = 1 := by
  simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem finCoord_natCast_mul (D : D7) (N : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) (k) :
    finCoord D ((N : Af D.host.F ⊗[D.host.F] D.host.E) * z) k = (N : Af D.host.F) * finCoord D z k := by
  unfold finCoord
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem exists_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (U : AddSubgroup (WO V W))
    {M₀ : ℕ} (hsub : ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U)
    (D' : ℕ) (g : GA D V) (h : GA D W) (x : Matrix (Fin W.rank) (Fin r) D.host.E)
    (hden : ∀ i j, Den D D' ((Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g) i j)) :
    ∃ u ∈ U, u.map (infPart D) = 0 ∧
      actO V W g h u = HMul.hMul (finLift (((M₀ * D' : ℕ) : D.host.E) • x)) (P.map (incA D)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = M₀ * D' := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨wf, hwf⟩ : ∃ wf : Matrix (Fin W.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E),
    wf = Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := ⟨_, rfl⟩
  rw [← hwf] at hden
  obtain ⟨Y, hY⟩ : ∃ Y : WO V W, Y = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : WO V W, u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) := ⟨_, rfl⟩
  have hinf : u.map (infPart D) = 0 := by
    rw [hu, hY]; exact infPart_u P _ g h
  have hfin : u.map (finPr D) = (N : Af D.host.F ⊗[D.host.F] D.host.E) • wf := by
    rw [hu, finPr_u, hY, finPr_Y, hwf]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  refine ⟨u, ?_, hinf, ?_⟩
  · refine hsub u hinf fun i j k => ⟨_, hden i j k, ?_⟩
    rw [entry_of_map_eq (finPr D) u _ wf hfin i j, finCoord_natCast_mul, hN, Nat.cast_mul, mul_assoc]
  · rw [hu, actO_u]
    exact hY

theorem levelheight : ∀ (D : D7) (V W : HSp D) (r : ℕ) (P : Matrix (Fin r) (Fin V.rank) D.host.E), ∃ e : ℕ,
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W),
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧
    ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ u ∈ U,
      u.map (infPart D) = 0 ∧ actO V W g h u = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := by
  intro D V W r P
  refine ⟨1, fun U hU => ?_⟩
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).1
  obtain ⟨CV, hCV, hcV⟩ := GlobalTheory.Grow.height_comparison V hθ
  obtain ⟨CW, hCW, hcW⟩ := GlobalTheory.Grow.height_comparison W hθ
  obtain ⟨M₀, hM₀, hsub⟩ := openSubY D V W U hU
  obtain ⟨c, hc0, hc⟩ := exists_denom_mul D
  obtain ⟨dx, hdx, hx⟩ := exists_denom_integral D
  obtain ⟨dP, hdP, hP⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (intRing D.host.F)
    (fun q : Fin r × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] P q.1 q.2.1) q.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  set nV := ⌈CV⌉₊ with hnV
  set nW := ⌈CW⌉₊ with hnW
  have hnV0 : 0 < nV := Nat.ceil_pos.2 hCV
  have hnW0 : 0 < nW := Nat.ceil_pos.2 hCW
  refine ⟨M₀ * c ^ 3 * dx * dP * nW * nV, by positivity, fun g h => ?_⟩
  obtain ⟨dh, hdh0, hdhH, hdh⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := W) h⁻¹
  obtain ⟨dg, hdg0, hdgH, hdg⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := V) g
  set D' := c * (c * (c * dh * dx) * dP) * dg with hD'
  refine ⟨M₀ * D', by positivity, ?_, fun x hxi => ?_⟩
  ·
    have h1 : (dh : ℝ) ≤ nW * GlobalTheory.Grow.height W h := by
      have := (hcW h⁻¹).1
      rw [GlobalTheory.Grow.height_inv] at this
      exact hdhH.trans (this.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _)
        (GlobalTheory.Grow.height_pos W h).le))
    have h2 : (dg : ℝ) ≤ nV * GlobalTheory.Grow.height V g :=
      hdgH.trans ((hcV g).1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (GlobalTheory.Grow.height_pos V g).le))
    rw [pow_one, hD']
    push_cast
    have hpos : (0 : ℝ) ≤ M₀ * c ^ 3 * dx * dP := by positivity
    calc (M₀ : ℝ) * (c * (c * (c * dh * dx) * dP) * dg) = (M₀ * c ^ 3 * dx * dP) * (dh * dg) := by ring
      _ ≤ (M₀ * c ^ 3 * dx * dP) * ((nW * GlobalTheory.Grow.height W h) * (nV * GlobalTheory.Grow.height V g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (mul_nonneg (by positivity) (GlobalTheory.Grow.height_pos W h).le)) hpos
      _ = _ := by ring
  · exact exists_u P U hsub _ g h x (by
      rw [hD']
      refine den_matMul hc _ _ (den_matMul hc _ _ (den_matMul hc _ _ (fun i j => hdh i j) ?_) ?_) (fun i j => hdg i j)
      · intro i j; exact hx _ (hxi i j)
      · intro i j k; exact hP (i, j, k))
end GlobalTheory.LevelHeight
end
end

