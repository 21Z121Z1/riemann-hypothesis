import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralTwistedPlaceEigenvecto
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeTrivialBoundOfBoundedZonalSphericalUnitary
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.ZonalBound

theorem trivialBound_iff {q n : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) (β : Fin (n / 2) → ℂˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n β ↔
      ∀ i, ‖(β i : ℂ)‖ ≤ (q : ℝ) ^ (n - 1) ∧ ‖(β i : ℂ)‖⁻¹ ≤ (q : ℝ) ^ (n - 1) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have e : ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) = (q : ℝ) ^ (n - 1) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast, Nat.cast_sub hn, Nat.cast_one]
  have e' : ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) = ((q : ℝ) ^ (n - 1))⁻¹ := by
    rw [Real.rpow_neg (by positivity), e]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound
  rw [e, e']
  refine forall_congr' fun i => and_congr ?_ Iff.rfl |>.trans and_comm
  have hp : 0 < ‖(β i : ℂ)‖ := norm_pos_iff.2 (β i).ne_zero
  exact ⟨fun h => inv_le_of_inv_le₀ (by positivity) h, fun h => inv_le_of_inv_le₀ hp h⟩

theorem trivialBound_of_ne_zero {q n : ℕ} (hq : 1 ≤ q) (β : Fin (n / 2) → ℂˣ)
    (h : ∀ i, ∀ X : ℂ, ‖X‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ →
      1 - (q : ℂ) ^ (n - 1) * X * (β i : ℂ) ≠ 0 ∧ 1 - (q : ℂ) ^ (n - 1) * X / (β i : ℂ) ≠ 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n β := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · intro i; exact absurd i.2 (by omega)
  rw [trivialBound_iff hq (by omega)]
  intro i
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set c : ℝ := (q : ℝ) ^ (n - 1) with hc
  have hc0 : 0 < c := by positivity
  have hcc : (q : ℝ) ^ (2 * (n - 1)) = c * c := by rw [hc, ← pow_add]; ring_nf
  have hcC : ‖((q : ℂ) ^ (n - 1))‖ = c := by rw [norm_pow, Complex.norm_natCast]
  have hcC0 : ((q : ℂ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
  have hp : 0 < ‖(β i : ℂ)‖ := norm_pos_iff.2 (β i).ne_zero
  have hb0 : (β i : ℂ) ≠ 0 := (β i).ne_zero
  constructor
  · by_contra hlt
    push_neg at hlt
    have hX : ‖((q : ℂ) ^ (n - 1) * (β i : ℂ))⁻¹‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ := by
      rw [norm_inv, norm_mul, hcC, hcc]
      exact inv_strictAnti₀ (by positivity) (mul_lt_mul_of_pos_left hlt hc0)
    apply (h i _ hX).1
    field_simp
    ring
  · by_contra hlt
    push_neg at hlt
    have hX : ‖(β i : ℂ) / (q : ℂ) ^ (n - 1)‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ := by
      rw [norm_div, hcC, hcc, div_lt_iff₀ hc0, mul_inv, mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one]
      exact (lt_inv_comm₀ hp hc0).2 hlt
    apply (h i _ hX).2
    field_simp
    ring

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

def denom (n : ℕ) (c : ℂ) (α : Fin (n / 2) → ℂˣ) (X : ℂ) : ℂ :=
  (∏ i, (1 - c * X * (α i : ℂ)) * (1 - c * X / (α i : ℂ))) * (if Odd n then 1 - c * X else 1)

theorem differentiable_denom (n : ℕ) (c : ℂ) (α : Fin (n / 2) → ℂˣ) : Differentiable ℂ (denom n c α) := by
  unfold denom
  by_cases h : Odd n
  · simp only [if_pos h]; fun_prop
  · simp only [if_neg h]; fun_prop

theorem one_sub_ne_zero {z : ℂ} (h : ‖z‖ < 1) : 1 - z ≠ 0 := fun e => by
  rw [← sub_eq_zero.1 e, norm_one] at h
  exact lt_irrefl _ h

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem closedForm_mul_denom (q n : ℕ) (c X : ℂ) (α : Fin (n / 2) → ℂˣ) (h : Domain (c * X) α) :
    closedForm q n X (c * X) α * denom n c α X = ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X) := by
  have h1 : (∏ i, (1 - c * X * (α i : ℂ))⁻¹ * (1 - c * X / (α i : ℂ))⁻¹) *
      ∏ i, (1 - c * X * (α i : ℂ)) * (1 - c * X / (α i : ℂ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    have a : 1 - c * X * (α i : ℂ) ≠ 0 := one_sub_ne_zero (by rw [norm_mul]; exact (h.2 i).1)
    have b : 1 - c * X / (α i : ℂ) ≠ 0 := one_sub_ne_zero (by rw [norm_div, div_eq_mul_inv]; exact (h.2 i).2)
    rw [mul_mul_mul_comm, inv_mul_cancel₀ a, inv_mul_cancel₀ b, one_mul]
  have h2 : (if Odd n then (1 - c * X)⁻¹ else 1) * (if Odd n then 1 - c * X else 1) = 1 := by
    split_ifs
    · exact inv_mul_cancel₀ (one_sub_ne_zero h.1)
    · exact one_mul _
  rw [closedForm, denom, mul_assoc (∏ j ∈ Finset.range n, _), mul_assoc (∏ j ∈ Finset.range n, _),
    mul_mul_mul_comm, h1, h2, one_mul, mul_one]

theorem numer_ne_zero {q n : ℕ} (hq : 1 ≤ q) {X : ℂ} (hX : ‖X‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹) :
    ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X) ≠ 0 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine Finset.prod_ne_zero_iff.2 fun j hj => one_sub_ne_zero ?_
  have hj' := Finset.mem_range.1 hj
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_natCast]
  calc (q : ℝ) ^ j * ‖X‖ ≤ (q : ℝ) ^ (2 * (n - 1)) * ‖X‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 (by omega)) (norm_nonneg _)
    _ < (q : ℝ) ^ (2 * (n - 1)) * ((q : ℝ) ^ (2 * (n - 1)))⁻¹ := mul_lt_mul_of_pos_left hX (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

theorem domain_of_bound {r : ℕ} {y : ℂ} {α : Fin r → ℂˣ} {M : ℝ} (hM : 1 ≤ M)
    (hα : ∀ i, ‖(α i : ℂ)‖ ≤ M ∧ ‖(α i : ℂ)‖⁻¹ ≤ M) (hy : ‖y‖ * M < 1) : Domain y α := by
  have key : ∀ a : ℝ, a ≤ M → ‖y‖ * a < 1 := fun a ha =>
    (mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans_lt hy
  exact ⟨by simpa using key 1 hM, fun i => ⟨key _ (hα i).1, key _ (hα i).2⟩⟩

theorem exists_bound {r : ℕ} (α : Fin r → ℂˣ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i, ‖(α i : ℂ)‖ ≤ M ∧ ‖(α i : ℂ)‖⁻¹ ≤ M := by
  have h0 : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 ≤ ‖(α i : ℂ)‖ + ‖(α i : ℂ)‖⁻¹ := fun i _ => by positivity
  refine ⟨1 + ∑ i, (‖(α i : ℂ)‖ + ‖(α i : ℂ)‖⁻¹), le_add_of_nonneg_right (Finset.sum_nonneg h0), fun i => ?_⟩
  have h1 := Finset.single_le_sum h0 (Finset.mem_univ i)
  have h2 : 0 ≤ ‖(α i : ℂ)‖ := norm_nonneg _
  have h3 : 0 ≤ ‖(α i : ℂ)‖⁻¹ := by positivity
  constructor <;> linarith

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

theorem exists_deg {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ)
    {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (hn : 1 ≤ n) :
    ∃ deg : GU σ n ⧸ KU σ n → ℕ, ∀ X : ℂ, X ≠ 0 → ∃ (χ : Lˣ →* ℂˣ) (s : ℂ) (Φ : GD σ n → ℂ), IsUnr χ ∧
      IsSphSec σ q n χ s Φ ∧ varX q n (χ ϖ) s = X ∧ varY q (χ ϖ) s = (q : ℂ) ^ (n - 1) * X ∧
      (∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) = Φ (io1 σ n g)) ∧
      ∀ a : GU σ n ⧸ KU σ n, Φ (io1 σ n a.out) = X ^ deg a := by
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : q ≠ 0 := by omega
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hc := GlobalTheory.ZetaSumU.cartan_complete L (ϖ : L) σ q n hU
  choose D t ht k₁ hk₁ k₂ hk₂ e using hc
  refine ⟨fun a => (∑ i, max (D a.out i) 0).toNat, fun X hX => ?_⟩
  obtain ⟨χ, hχ, hχϖ⟩ := GlobalTheory.ZetaSumU.exists_unr_char ϖ hU
    (Units.mk0 (X * (q : ℂ) ^ n) (mul_ne_zero hX (pow_ne_zero _ hqC)))
  obtain ⟨Φ, hΦ⟩ := exists_isSphSec σ hq n hχ (((0 : ℕ) : ℂ) / 2)
  obtain ⟨hXe, hYe⟩ := GlobalTheory.ZetaSumU.varXY_eq q n 0 hq2 (X * (q : ℂ) ^ n)
  have hz : ((χ ϖ : ℂˣ) : ℂ) = X * (q : ℂ) ^ n := by rw [hχϖ]; rfl
  have hvX : varX q n (χ ϖ) (((0 : ℕ) : ℂ) / 2) = X := by
    rw [hz, hXe, add_zero, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hqC), mul_one]
  have hval : ∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) = X ^ (∑ i, max (D g i) 0) := fun g k hk => by
    have h := GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ _ Φ hΦ (D g) (t g) (ht g) (k₁ g) (hk₁ g) (k₂ g * k)
      (mul_mem (hk₂ g) hk)
    rw [hvX, ← mul_assoc, ← e g] at h
    exact h
  have hval1 : ∀ g, Φ (io1 σ n g) = X ^ (∑ i, max (D g i) 0) := fun g => by
    simpa only [mul_one] using hval g 1 (one_mem _)
  refine ⟨χ, _, Φ, hχ, hΦ, hvX, ?_, fun g k hk => (hval g k hk).trans (hval1 g).symm, fun a => ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [hz, hYe, Nat.add_sub_cancel, zero_add, pow_one, pow_succ]
    field_simp
  · rw [hval1, ← zpow_natCast, Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _)]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

theorem trivialBound_of_bounded : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (α : Fin (n / 2) → ℂˣ) (w : GU σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α w → (∃ C : ℝ, ∀ g, ‖w g‖ ≤ C) → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α := by
  intro H L _ _ _ ϖ σ q n hU α w hw hb
  obtain ⟨C, hC⟩ := hb
  rcases Nat.lt_or_ge n 2 with hn | hn
  · intro i; exact absurd i.2 (by omega)
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  obtain ⟨deg, hdeg⟩ := exists_deg ϖ hU (by omega : 1 ≤ n)
  letI : MeasurableSpace (GU σ n) := borel _
  haveI : BorelSpace (GU σ n) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμK⟩ := GlobalTheory.ZetaSumU.exists_haar (ϖ : L) hU n
  have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L (ϖ : L) σ q n hU).1
  have hc1 : (1 : ℝ) ≤ (q : ℝ) ^ (n - 1) := one_le_pow₀ hq1
  have hc0 : (0 : ℝ) < (q : ℝ) ^ (n - 1) := by positivity
  have hny : ∀ x : ℝ, 0 < x → ‖(q : ℂ) ^ (n - 1) * (x : ℂ)‖ = (q : ℝ) ^ (n - 1) * x := fun x hx => by
    rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hx.le]

  obtain ⟨α0, hα0, hw0⟩ := isZonal_one hU n
  have hb0 := (trivialBound_iff (by omega) (by omega) α0).1 (GlobalTheory.ZetaSumU.tb_triv q n hq2 α0 hα0)
  have hsum : ∀ r : ℝ, 0 < r → r < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ → Summable fun a => r ^ deg a := fun r hr hρ => by
    obtain ⟨χ, s, Φ, hχ, hΦ, -, hY, hinv, hval⟩ := hdeg (r : ℂ) (by exact_mod_cast hr.ne')
    have hdom : Domain (varY q (χ ϖ) s) α0 := by
      rw [hY]
      refine domain_of_bound hc1 hb0 ?_
      rw [hny r hr, mul_right_comm, ← pow_add, ← two_mul]
      exact (mul_lt_mul_of_pos_left hρ (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))
    have hint := ((H L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α0 _ hw0).1 hdom).1
    have hs := GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ (fun g k hk => by simp only [hinv g k hk]) hint
    refine hs.congr fun a => ?_
    simp only [hval, mul_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]

  obtain ⟨M, hM, hαM⟩ := exists_bound α
  have heq : ∀ x : ℝ, 0 < x → x < ((q : ℝ) ^ (n - 1) * M)⁻¹ →
      (∑' a : GU σ n ⧸ KU σ n, w a.out * (x : ℂ) ^ deg a) * denom n ((q : ℂ) ^ (n - 1)) α x =
        ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * (x : ℂ)) := fun x hx hδ => by
    obtain ⟨χ, s, Φ, hχ, hΦ, hX, hY, hinv, hval⟩ := hdeg (x : ℂ) (by exact_mod_cast hx.ne')
    have hdom : Domain ((q : ℂ) ^ (n - 1) * (x : ℂ)) α := by
      refine domain_of_bound hM hαM ?_
      rw [hny x hx, mul_right_comm]
      exact (mul_lt_mul_of_pos_left hδ (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))
    obtain ⟨hint, hI, -⟩ := (H L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α w hw).1 (by rw [hY]; exact hdom)
    have hF : ∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) * w (g * k) = Φ (io1 σ n g) * w g := fun g k hk => by
      have h1 := hw.1 1 ⟨k, hk⟩ g
      simp only [OneMemClass.coe_one, one_mul] at h1
      rw [hinv g k hk, h1]
    have hs := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ hF hint).of_norm
    have hci := (GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) hKo hμK (fun g => Φ (io1 σ n g) * w g) _ hF hs.hasSum).2
    rw [hI, hX, hY] at hci
    rw [← closedForm_mul_denom q n _ _ α hdom, hci]
    congr 1
    exact tsum_congr fun a => by rw [hval, mul_comm]
  refine trivialBound_of_ne_zero (by omega) α fun i X hX => ?_
  have hP := GlobalTheory.gradedSeries_mul_ne_zero (GU σ n ⧸ KU σ n) deg (fun a => w a.out) ((q : ℝ) ^ (2 * (n - 1)))⁻¹
    ((q : ℝ) ^ (n - 1) * M)⁻¹ (denom n ((q : ℂ) ^ (n - 1)) α)
    (fun X => ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X)) (by positivity) (differentiable_denom _ _ _)
    (by fun_prop)
    (fun r hr hρ => Summable.of_nonneg_of_le (fun a => by positivity)
      (fun a => mul_le_mul_of_nonneg_right (hC _) (by positivity)) ((hsum r hr hρ).mul_left C))
    heq X hX (numer_ne_zero (by omega) hX)
  exact mul_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 (mul_ne_zero_iff.1 hP).1 i (Finset.mem_univ i))

end GlobalTheory.ZonalBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsDenseContinuousThetaLaw
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisSmoothing

open GlobalTheory.FockCompare

theorem norm_integral_sub_le {X : Type} [MeasurableSpace X] (μ : Measure X) (φ : X → ℝ) (F : X → ℂ) (c : ℂ) (δ : ℝ)
    (h0 : ∀ x, 0 ≤ φ x) (h1 : ∫ x, φ x ∂μ = 1) (hφ : Integrable φ μ) (hF : Integrable (fun x => (φ x : ℂ) * F x) μ)
    (hb : ∀ x, φ x ≠ 0 → ‖F x - c‖ ≤ δ) : ‖∫ x, (φ x : ℂ) * F x ∂μ - c‖ ≤ δ := by
  have hc : Integrable (fun x => (φ x : ℂ) * c) μ := hφ.ofReal.mul_const c
  have e : ∫ x, (φ x : ℂ) * c ∂μ = c := by
    rw [integral_mul_const, integral_complex_ofReal, h1]
    simp
  have e2 : ∫ x, φ x * δ ∂μ = δ := by rw [integral_mul_const, h1, one_mul]
  rw [← e2]
  conv_lhs => rw [← e, ← integral_sub hF hc]
  refine norm_integral_le_of_norm_le (hφ.mul_const δ) (Filter.Eventually.of_forall fun x => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 x)]
  by_cases hx : φ x = 0
  · rw [hx, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hb x hx) (h0 x)

theorem isAddHaarMeasure_volume (ι m n : Type) [Fintype ι] [Fintype m] [Fintype n] :
    (volume : Measure (ι → m → n → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (m → n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem exists_theta_of_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (f : WO A T → ℂ), Continuous f → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), f (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * f u) → (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ A T u f = f) → ∀ N ∈ 𝓝 (0 : WO A T), ∀ δ : ℝ, (∀ a ∈ N, ∀ w, ‖heisO ψ A T a f w - f w‖ ≤ δ) → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ w, ‖g w - f w‖ ≤ δ := by
  intro D ψ hψ A T f hf hlaw hlev N hN δ hδ
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨i1, -⟩ := lattice_Mx D T.rank A.rank
  haveI : (volume : Measure (RW T A)).IsAddHaarMeasure := isAddHaarMeasure_volume _ _ _
  have hι : Continuous (iotaW σ T A) := h.continuous_iota T A
  have hN' : iotaW σ T A ⁻¹' N ∈ 𝓝 (0 : RW T A) :=
    hι.continuousAt.preimage_mem_nhds (by rw [AddMonoidHom.map_zero]; exact hN)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN'
  let b : ContDiffBump (0 : RW T A) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let φ : RW T A → ℝ := b.normed volume
  have hφs : ContDiff ℝ ∞ φ := b.contDiff_normed
  have hφc : HasCompactSupport φ := b.hasCompactSupport_normed
  let g : WO A T → ℂ := fun w => ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
  have hsm : Sm (iotaW σ T A) g := GlobalTheory.T.heisenbergAverage_realPlaces_smooth D θ σ h ψ hψ A T φ hφs hφc f hf
  have hl : ∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ A T u g = g := by
    obtain ⟨U, hU, hUf⟩ := hlev
    refine ⟨U, hU, fun u hu h0 => funext fun w => ?_⟩
    show ψ (symplOH A T w u) * ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (w + u) = _
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e := congrFun (GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (h.real_iota T A x) (hUf u hu h0)) w
    show _ = (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
    rw [← e]
    exact mul_left_comm _ _ _
  refine ⟨g, ⟨fun γ w => ?_, hl, GlobalTheory.OrientedHeis.continuous_of_level h hψ.1.1 g hl hsm,
    ((smooth_iff_sm_and_real_lines D θ σ h T A).1 g).2 hsm⟩, fun w => ?_⟩
  · show ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (ratW T A γ + w) =
      _ * ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (ratW T A γ + w) = _
    rw [GlobalTheory.OrientedHeis.heisO_quasi _ f hlaw]
    exact mul_left_comm _ _ _
  · have hc : Continuous fun x : RW T A => heisO ψ A T (iotaW σ T A x) f w :=
      (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_const hι)).mul
        (hf.comp (continuous_const.add hι))
    have hφℂ : HasCompactSupport fun x => (φ x : ℂ) := hφc.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
    refine norm_integral_sub_le volume φ _ (f w) δ b.nonneg_normed b.integral_normed b.integrable_normed
      (((Complex.continuous_ofReal.comp hφs.continuous).mul hc).integrable_of_hasCompactSupport hφℂ.mul_right)
      fun x hx => hδ _ (hrN ?_) w
    have : x ∈ Function.support φ := hx
    rwa [b.support_normed_eq] at this

theorem exists_theta_near : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ u, ‖q u - g u‖ ≤ ε := by
  have h1 := GlobalTheory.T.heisenbergOperator_thetaLaw_tendsto_uniform_near_zero
  have h2a := GlobalTheory.T.exists_small_compact_level_symplecticCharacter_trivial
  have h2b := GlobalTheory.T.exists_heisenbergAverage_compactSymplecticTrivial
  have h4 := exists_theta_of_level
  intro D ψ hψ A T q hq hlaw ε hε
  obtain ⟨N, hN, hNq⟩ := h1 D ψ hψ A T q hq hlaw (ε / 2) (half_pos hε)
  obtain ⟨K, hKc, hKN, -, ⟨U, hU, hUK⟩, hKψ⟩ := h2a D ψ hψ A T N hN
  obtain ⟨g1, hg1c, hg1law, hg1K, hg1near⟩ := h2b D ψ hψ A T K hKc hKψ q hq hlaw
  have hg1q : ∀ w, ‖g1 w - q w‖ ≤ ε / 2 := hg1near (ε / 2) (fun a ha w => hNq a (hKN ha) w)
  obtain ⟨N2, hN2, hN2g⟩ := h1 D ψ hψ A T g1 hg1c hg1law (ε / 2) (half_pos hε)
  obtain ⟨g, hg, hgg1⟩ := h4 D ψ hψ A T g1 hg1c hg1law ⟨U, hU, fun u hu h0 => hg1K u (hUK u hu h0)⟩ N2 hN2 (ε / 2) hN2g
  refine ⟨g, hg, fun w => ?_⟩
  have e : q w - g w = (g1 w - g w) - (g1 w - q w) := by ring
  rw [e]
  calc ‖(g1 w - g w) - (g1 w - q w)‖ ≤ ‖g1 w - g w‖ + ‖g1 w - q w‖ := norm_sub_le _ _
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · rw [norm_sub_rev]; exact hgg1 w
        · exact hg1q w
    _ = ε := add_halves ε

end GlobalTheory.HeisSmoothing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionIsUnitaryAdelicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvection_isUnitaryAdelic : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D := by
  first | exact @GlobalTheory.TransvAdelic.transv_unitary | exact GlobalTheory.TransvAdelic.transv_unitary | (intros; apply GlobalTheory.TransvAdelic.transv_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexDataRepresentativeDependsOnDoubleCosetStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistIndexData_representative_dependsOnDoubleCoset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (G : ChGlob X R.m), (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 → IdxProd sel mu cst (twIdx Ch sel mu cst m2) := by
  first | exact @GlobalTheory.TwBridge.idxProd_twIdx | exact GlobalTheory.TwBridge.idxProd_twIdx | (intros; apply GlobalTheory.TwBridge.idxProd_twIdx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentativesStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistIndexSet_eq_prod_localRepresentatives : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → IdxIsProd sel mu s L := by
  first | exact @GlobalTheory.TwBridge.idxIsProd_of_ok | exact GlobalTheory.TwBridge.idxIsProd_of_ok | (intros; apply GlobalTheory.TwBridge.idxIsProd_of_ok <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralTwistedPlaceEigenvectoStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_twisted_place_eigenvector : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r t l : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ → IsUnitaryChar μ₀ → ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ) (ρ : ℝ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) → (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) → ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H → ∀ [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)] (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 → ∀ c : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ g, c g = ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ)) → c 1 ≠ 0 ∧ ∃ ζ : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ g, starRingEnd ℂ (c g) * ℓ (π g x) = starRingEnd ℂ (c 1) * ζ g * ℓ x) ∧ (∀ g ∈ parahoric k (Fin r) (Blocks l t), ζ g = 1) ∧ ∀ s : ℂ, ρ - 1 / 2 < s.re → Integrable (fun g => ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2)) m ∧ ∫ g, ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2) ∂m = lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) (l * t) s := by
  first | exact @GlobalTheory.TwistedZeta.local_zeta_twisted | exact GlobalTheory.TwistedZeta.local_zeta_twisted | (intros; apply GlobalTheory.TwistedZeta.local_zeta_twisted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMemSpanHeisenbergTranslatesOfNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsSelfDualC S ΛS → IsSelfDualC T ΛT → f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) → f ≠ 0 → f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  first | exact @GlobalTheory.VacCyclic.vac_mem_span | exact GlobalTheory.VacCyclic.vac_mem_span | (intros; apply GlobalTheory.VacCyclic.vac_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorsWittParabolicOriginToPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WMove

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ x : Mx D T.rank ρ, (∀ h, d.mixS T ψ μ 𝓕 (om (1, h) f) x = d.mixS T ψ μ 𝓕 (om (1, h) (heisO ψ S T (d.extX T (mt T h⁻¹ ⬝ x)) f)) 0) ∧ (∀ a g, d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) x = d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) (heisO ψ S T (d.extX T (x ⬝ a.1)) f)) 0) ∧ ∀ n : GA D S, d.mixS T ψ μ 𝓕 (om (n, 1) f) x = d.mixS T ψ μ 𝓕 (om (n, 1) (heisO ψ S T (d.extX T x ⬝ mt S n) f)) 0 := by
  intro D ψ S S₀ T ρ d χS χT om hω μ 𝓕 hμ f hf x
  have hb := fun F y => ((GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 F y)
  refine ⟨fun h => ?_, fun a g => ?_, fun n => ?_⟩
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.extX_apply, HypDec.extX_apply, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, mt_one, Matrix.one_mul, _root_.mul_inv_rev, ← map_inv d.levi, ← map_inv d.emb0, mt_mul,
      ← Matrix.mul_assoc, d.extX_apply T (x ⬝ a.1), Matrix.mul_assoc _ d.pX, d.wittDecomp_projX_anisotropicEmbedding, ← d.extX_apply T (x ⬝ a.1),
      d.extX_levi, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

end GlobalTheory.WMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnitsStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittLeviDiagonal_mem_latticeStabilizer_of_units : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → d.levi t ∈ grpAt S (· = v) → (∀ i, t.1 i i - 1 ∈ intAt D (· = v) ∧ (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → InK S L (· = v) (d.levi t) := by
  first | exact @GlobalTheory.FinPl.LeviUnitK.inK_levi | exact GlobalTheory.FinPl.LeviUnitK.inK_levi | (intros; apply GlobalTheory.FinPl.LeviUnitK.inK_levi <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlaceStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittLeviTransvection_mem_compactAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (hij : i ≠ j) (r : AE D), r ∈ idAt D (· = v) → (∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → InK S L (· = v) (d.levi (GlobalTheory.GLGen.transvGL hij r)) := by
  first | exact @GlobalTheory.FinPl.RootKeep.inK_levi_transv | exact GlobalTheory.FinPl.RootKeep.inK_levi_transv | (intros; apply GlobalTheory.FinPl.RootKeep.inK_levi_transv <;> assumption)
end
end

