import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeRealSpecialUnitaryEqFlagDomainMass
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedSectionInSpanOfGap
section
open Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
  ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds

noncomputable section

namespace GlobalTheory.SepCusp

theorem exists_threshold {r : ℕ} (p : ℕ) (w : Fin r → ℤ)
    (h : ∀ a b : Fin r, (a : ℕ) < p → p ≤ (b : ℕ) → w a < w b) :
    ∃ M : ℤ, (∀ a : Fin r, (a : ℕ) < p → w a ≤ M) ∧ ∀ b : Fin r, p ≤ (b : ℕ) → M + 1 ≤ w b := by
  classical
  by_cases hne : (Finset.univ.filter fun b : Fin r => p ≤ (b : ℕ)).Nonempty
  · obtain ⟨b0, hb0, hmin⟩ := Finset.exists_min_image _ w hne
    refine ⟨w b0 - 1, fun a ha => ?_, fun b hb => ?_⟩
    · have := h a b0 ha (Finset.mem_filter.mp hb0).2
      omega
    · have := hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
      omega
  · obtain ⟨M, hM⟩ := (Set.finite_range w).bddAbove
    exact ⟨M, fun a _ => hM ⟨a, rfl⟩,
      fun b hb => absurd ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩ hne⟩

theorem sum_le_of_unimodal (a L : ℕ → ℝ) (p r : ℕ) (hp : p ≤ r) (M : ℝ) (h0 : L 0 = 0) (hr : L r = 0)
    (hup : ∀ k < p, L k ≤ L (k + 1)) (hdown : ∀ k, p ≤ k → k < r → L (k + 1) ≤ L k)
    (ha : ∀ k < p, a k ≤ M) (hb : ∀ k, p ≤ k → k < r → M + 1 / 2 ≤ a k) :
    ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k) ≤ -(1 / 2) * L p := by
  rw [← Finset.sum_range_add_sum_Ico _ hp]
  have h1 : ∑ k ∈ Finset.range p, a k * (L (k + 1) - L k) ≤
      ∑ k ∈ Finset.range p, M * (L (k + 1) - L k) :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (ha k (Finset.mem_range.mp hk))
      (sub_nonneg.mpr (hup k (Finset.mem_range.mp hk)))
  have h2 : ∑ k ∈ Finset.Ico p r, a k * (L (k + 1) - L k) ≤
      ∑ k ∈ Finset.Ico p r, (M + 1 / 2) * (L (k + 1) - L k) :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonpos_right
      (hb k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2)
      (sub_nonpos.mpr (hdown k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2))
  rw [← Finset.mul_sum, Finset.sum_range_sub, h0] at h1
  rw [← Finset.mul_sum, Finset.sum_Ico_sub L hp, hr] at h2
  linarith

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

theorem rfac_le_of_sep (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) (τ : X.Ψ) (la : Wt X.Ψ r) (hs : 0 ≤ (s τ).im)
    (hsep : ∀ a b : Fin r, (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ a < la τ b) :
    rfac X la x (X.flowV e s x) τ ≤
      Real.exp (-(1 / 2) * Real.log (1 + (s τ).im / X.ttV e x τ)) := by
  rw [rfac_eq X e he hx s hT τ la]
  apply Real.exp_le_exp.mpr
  have hρ := rho_pos X e he hx s hT τ
  have hsg := hsg_of X hx τ
  have hb : 0 ≤ 2 * X.c τ * (s τ).im := by have := c_pos X τ; positivity
  have hp := X.p0_le
  set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
  have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
  have hLr : L r = 0 := by
    simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
  have hup : ∀ k < X.p0, L k ≤ L (k + 1) := fun k hk => by
    apply Real.log_le_log (hρ k (by omega))
    simp only [rho]
    have := mN_up (hG_of X τ) X.p0 X.p0_le (mat x τ) hsg (e τ) (k + 1) hk k (Nat.le_succ k)
    nlinarith
  have hdown : ∀ k, X.p0 ≤ k → k < r → L (k + 1) ≤ L k := fun k hk hkr => by
    apply Real.log_le_log (hρ (k + 1) hkr)
    simp only [rho]
    have := mN_down (hG_of X τ) X.p0 (mat x τ) hsg (e τ) k hk (k + 1) (Nat.le_succ k) hkr
    nlinarith
  set a : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) / 2 else 0 with ha
  have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
      (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
      ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => a k * (L (k + 1) - L k)) r]
    exact Finset.sum_congr rfl fun i _ => by simp only [a, L, dif_pos i.2]
  obtain ⟨M, hM1, hM2⟩ := exists_threshold X.p0 (la τ) hsep
  have hq : 1 + (s τ).im / X.ttV e x τ = rho X e s x τ X.p0 := by
    rw [Data.ttV, maj_eq X hx e τ (he τ).1, div_div_eq_mul_div, div_one]
    simp only [rho]
    ring
  rw [hsum, hq]
  refine sum_le_of_unimodal a L X.p0 r hp ((M : ℝ) / 2) hL0 hLr hup hdown (fun k hk => ?_)
    (fun k hk hkr => ?_)
  · have hkr : k < r := by omega
    have h1 : (la τ ⟨k, hkr⟩ : ℝ) ≤ M := by exact_mod_cast hM1 ⟨k, hkr⟩ hk
    simp only [a, dif_pos hkr]
    linarith
  · have h1 : (M : ℝ) + 1 ≤ la τ ⟨k, hkr⟩ := by exact_mod_cast hM2 ⟨k, hkr⟩ hk
    simp only [a, dif_pos hkr]
    linarith

theorem mem_SS_of_sep_at (la : Wt X.Ψ r) (τ0 : X.Ψ) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    (hsep : ∀ a b : Fin r, (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ0 a < la τ0 b) :
    P ∈ X.SS la := by
  classical
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  obtain ⟨C, hC⟩ := hP.2
  have hiso : X.IsIsoV (X.embV ξ) := fun τ =>
    ⟨by rw [show X.embV ξ τ = Data.emb τ.1 ξ from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  set G := X.fj la ξ 0 P with hG
  have hGb : ∀ y ∈ X.dom, ‖G y‖ * X.nfac la y ≤ C := fun y hy =>
    FlowCoefficientBounds.fj_bound X la P C hC hξ 0 hy
  have hGd : DifferentiableOn ℂ G X.dom := CuspCoefficientFlow.fj_diffOn X la P hP hξ 0
  have hreal : ∀ s : X.Ψ → ℝ, G (X.flowV (X.embV ξ) (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, (0 : X.Ψ → ℂ) τ * s τ) * G x := by
    intro s
    have := X.fj_flow_real la ξ hξ 0 P hP.1 ⟨C, hC⟩ x hx s
    simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul] at this ⊢
    exact this
  have hcx := holomorphic_periodicity_extension r X (X.embV ξ) hiso G hGd 0 x hx hreal
  by_contra hne
  have hN := FlowCoefficientBounds.nfac_pos X hx la
  have hA : 0 < ‖G x‖ * X.nfac la x := mul_pos (norm_pos_iff.mpr hne) hN
  have hmaj := maj_eq X hx (X.embV ξ) τ0 (hiso τ0).1
  have hmpos := mN_pos (hG_of X τ0) X.p0 X.p0_le (mat x τ0) (hx τ0).1 (hsg_of X hx τ0)
    (X.embV ξ τ0) (hiso τ0).1 (hiso τ0).2
  have htt : 0 < X.ttV (X.embV ξ) x τ0 := by
    rw [Data.ttV, hmaj]
    have := c_pos X τ0
    positivity
  set M : ℝ := |Real.log (C / (‖G x‖ * X.nfac la x))| + 1 with hM
  have hM0 : 0 < M := by positivity
  set t : ℝ := X.ttV (X.embV ξ) x τ0 * (Real.exp (2 * M) - 1) with ht
  have ht0 : 0 < t := mul_pos htt (by linarith [Real.add_one_lt_exp (show (2 * M) ≠ 0 by positivity)])
  let s : X.Ψ → ℂ := fun τ => if τ = τ0 then I * t else 0
  have hs0 : (s τ0).im = t := by simp [s]
  have hdom : X.flowV (X.embV ξ) s x ∈ X.dom := by
    refine (flowDomainCriterion_holds r X _ hiso x hx s).1.mpr fun τ => ?_
    by_cases h : τ = τ0
    · subst h
      rw [hs0]
      have : 0 < t / X.ttV (X.embV ξ) x τ := div_pos ht0 htt
      linarith
    · simp [s, h]
  have hq : 1 + (s τ0).im / X.ttV (X.embV ξ) x τ0 = Real.exp (2 * M) := by
    rw [hs0, ht, mul_div_cancel_left₀ _ htt.ne']
    ring
  have hratio : X.nfac la x / X.nfac la (X.flowV (X.embV ξ) s x) ≤ Real.exp (-M) := by
    rw [nfac_div, Finset.prod_eq_single τ0 (fun τ _ hτ => rfac_of_zero X _ hiso hx s hdom τ la
      (by simp [s, hτ])) (fun h => absurd (Finset.mem_univ τ0) h)]
    refine (rfac_le_of_sep X _ hiso hx s hdom τ0 la (by rw [hs0]; exact ht0.le) hsep).trans
      (le_of_eq ?_)
    rw [hq, Real.log_exp]
    congr 1
    ring
  have hNT := FlowCoefficientBounds.nfac_pos X hdom la
  have hGT : G (X.flowV (X.embV ξ) s x) = G x := by
    rw [hcx s hdom]
    simp
  have h1 : X.nfac la x ≤ X.nfac la (X.flowV (X.embV ξ) s x) * Real.exp (-M) := by
    rw [div_le_iff₀ hNT] at hratio
    rw [mul_comm]
    exact hratio
  have h2 : ‖G x‖ * X.nfac la x ≤ C * Real.exp (-M) := by
    calc ‖G x‖ * X.nfac la x ≤ ‖G x‖ * (X.nfac la (X.flowV (X.embV ξ) s x) * Real.exp (-M)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖G (X.flowV (X.embV ξ) s x)‖ * X.nfac la (X.flowV (X.embV ξ) s x)) *
          Real.exp (-M) := by rw [hGT]; ring
      _ ≤ C * Real.exp (-M) := mul_le_mul_of_nonneg_right (hGb _ hdom) (Real.exp_pos _).le
  rcases le_or_gt C 0 with hC0 | hC0
  · have : C * Real.exp (-M) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (Real.exp_pos _).le
    linarith
  · have hlt : Real.log (C / (‖G x‖ * X.nfac la x)) < M := by
      have := le_abs_self (Real.log (C / (‖G x‖ * X.nfac la x)))
      linarith
    have h3 : C / (‖G x‖ * X.nfac la x) < Real.exp M := by
      rw [← Real.exp_log (div_pos hC0 hA)]
      exact Real.exp_lt_exp.mpr hlt
    have h4 : C * Real.exp (-M) < ‖G x‖ * X.nfac la x := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
      rw [div_lt_iff₀ hA] at h3
      linarith
    linarith

theorem nonempty_type : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : NumberField.ComplexEmbedding.conjugate τ ∈ X.Ψ
  · exact ⟨⟨_, h⟩⟩
  · exact ⟨⟨τ, (X.cmType τ).mpr h⟩⟩

theorem mem_SS_of_sep (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    (hsep : ∀ (τ : X.Ψ) (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ a < la τ b) :
    P ∈ X.SS la := by
  obtain ⟨τ0⟩ := nonempty_type X
  exact mem_SS_of_sep_at X la τ0 P hP (hsep τ0)

end GlobalTheory.SepCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedSubgroupFiniteCosets
section
open Matrix
open scoped Classical

namespace GlobalTheory.LKLoc

theorem inv_mul_entry_mem_intK (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
    (a b : GL (Fin n) L) (C ε : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i j, ‖((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j‖ ≤ C)
    (hab : ∀ i j, ‖(b : Matrix (Fin n) (Fin n) L) i j - (a : Matrix (Fin n) (Fin n) L) i j‖ ≤ ε)
    (hε : n * C * ε ≤ 1) (i j : Fin n) :
    ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intK p L := by
  have key : ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      1 + ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L)) := by
    rw [Units.val_mul, Matrix.mul_sub, Units.inv_mul]
    abel
  have hs : ‖(((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L))) i j‖ ≤ 1 := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i k *
            ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L)) k j‖
        ≤ ∑ _k : Fin n, C * ε := Finset.sum_le_sum fun k _ => by
          rw [norm_mul]
          exact mul_le_mul (ha i k) (by simpa using hab k j) (norm_nonneg _) hC
      _ = n * C * ε := by simp [mul_assoc]
      _ ≤ 1 := hε
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  change ‖(( ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ 1
  rw [key, Matrix.add_apply, IntermediateField.coe_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 hs)

theorem exists_finset_inv_mul_mem_KintK : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (B : Subgroup (GL (Fin n) L)) (c : ℝ),
      (∀ z ∈ B, ∀ i j, ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c) →
      ∃ T : Finset (GL (Fin n) L), (∀ t ∈ T, t ∈ B) ∧ ∀ z ∈ B, ∃ t ∈ T, t⁻¹ * z ∈ GlobalTheory.LKLoc.KintK p L n := by
  intro p _ L hL n B c hB
  haveI : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  set C := max c 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  set ε : ℝ := 1 / (2 * (n * C + 1)) with hεdef
  have hε : 0 < ε := by positivity
  let f : GL (Fin n) L → (Fin n → Fin n → L) := fun z i j => (z : Matrix (Fin n) (Fin n) L) i j
  let S : Set (Fin n → Fin n → L) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : L) C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 hS.totallyBounded ε hε
  let g : (Fin n → Fin n → L) → GL (Fin n) L := fun y =>
    if h : ∃ z ∈ B, dist (f z) y < ε then h.choose else 1
  have hgB : ∀ y, g y ∈ B := fun y => by
    by_cases h : ∃ z ∈ B, dist (f z) y < ε
    · simp only [g, dif_pos h]; exact h.choose_spec.1
    · simp only [g, dif_neg h]; exact B.one_mem
  have hbd : ∀ z ∈ B, ∀ i j, ‖(z : Matrix (Fin n) (Fin n) L) i j‖ ≤ C := fun z hz i j =>
    (hB z hz i j).trans (le_max_left _ _)
  have hnC : (n : ℝ) * C * (2 * ε) ≤ 1 := by
    rw [hεdef]
    have h0 : (0 : ℝ) < n * C + 1 := by positivity
    rw [show (n : ℝ) * C * (2 * (1 / (2 * (n * C + 1)))) = n * C / (n * C + 1) by field_simp]
    rw [div_le_one h0]; linarith
  refine ⟨ht.toFinset.image g, ?_, ?_⟩
  · intro s hs
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hs
    exact hgB y
  · intro z hz
    have hzS : f z ∈ S := by
      simp only [S, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
      intro i j; exact hbd z hz i j
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (hcov hzS)
    have hex : ∃ z ∈ B, dist (f z) y < ε := ⟨z, hz, hzy⟩
    have hgy : g y ∈ B ∧ dist (f (g y)) y < ε := by
      simp only [g, dif_pos hex]; exact hex.choose_spec
    refine ⟨g y, Finset.mem_image.2 ⟨y, ht.mem_toFinset.2 hy, rfl⟩, ?_⟩
    obtain ⟨hwB, hwy⟩ := hgy
    set w := g y
    have hd : dist (f z) (f w) ≤ 2 * ε := by
      have := dist_triangle_right (f z) (f w) y
      have := Metric.mem_ball.1 hzy
      linarith
    have hent : ∀ i j, ‖(z : Matrix (Fin n) (Fin n) L) i j - (w : Matrix (Fin n) (Fin n) L) i j‖ ≤ 2 * ε :=
      fun i j => by
        rw [← dist_eq_norm]
        exact ((dist_le_pi_dist (f z i) (f w i) j).trans (dist_le_pi_dist (f z) (f w) i)).trans hd
    rw [KintK, GlobalTheory.LKRes.mem_range_map_subtype_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact inv_mul_entry_mem_intK p L n w z C (2 * ε) hC (hbd _ (B.inv_mem hwB)) hent hnC i j
    · rw [_root_.mul_inv_rev, inv_inv]
      exact inv_mul_entry_mem_intK p L n z w C (2 * ε) hC (hbd _ (B.inv_mem hz))
        (fun i j => by rw [norm_sub_rev]; exact hent i j) hnC i j

end GlobalTheory.LKLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralOfCountableCommutatorsUnitary
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open scoped Matrix.Norms.Operator in

theorem commute_of_countable_commutators_exp {n : ℕ} (X a : Matrix (Fin n) (Fin n) ℂ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ)) (ha : IsUnit a.det) (hS : S.Countable)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) * a * NormedSpace.exp (-(t • X)) * a⁻¹ ∈ S) :
    X * a = a * X := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X))
      (NormedSpace.exp (t • X) * X) t := fun t => hasDerivAt_exp_smul_const X t
  have hc : Continuous (fun u : ℝ => NormedSpace.exp (u • X)) :=
    continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hc' : Continuous (fun u : ℝ => NormedSpace.exp (-(u • X))) := by
    have := hc.comp continuous_neg
    refine this.congr fun u => ?_
    simp [Function.comp, neg_smul]
  set f : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => NormedSpace.exp (t • X) * a * NormedSpace.exp (-(t • X)) * a⁻¹ with hf
  have hfc : Continuous f := ((hc.mul continuous_const).mul hc').mul continuous_const
  have hcount : (Set.range f).Countable := hS.mono (by rintro _ ⟨t, rfl⟩; exact h t)
  have hsub : (Set.range f).Subsingleton :=
    hcount.isTotallyDisconnected _ subset_rfl (isPreconnected_range hfc)
  have hone : ∀ t, f t = 1 := by
    intro t
    rw [hsub ⟨t, rfl⟩ ⟨0, rfl⟩]
    simp [hf, Matrix.mul_nonsing_inv a ha]
  have hcomm : ∀ t : ℝ, NormedSpace.exp (t • X) * a = a * NormedSpace.exp (t • X) := by
    intro t
    have h1 := hone t
    have h2 : NormedSpace.exp (-(t • X)) * NormedSpace.exp (t • X) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left]
      simp
    have h3 : f t * a * NormedSpace.exp (t • X) = NormedSpace.exp (t • X) * a := by
      simp only [hf]
      rw [Matrix.mul_assoc _ a⁻¹ a, Matrix.nonsing_inv_mul a ha, Matrix.mul_one,
        Matrix.mul_assoc _ (NormedSpace.exp (-(t • X))), h2, Matrix.mul_one]
    rw [← h3, h1, Matrix.one_mul]
  have e1 := (hd 0).mul_const a
  have e2 := (hd 0).const_mul a
  simp only [hcomm] at e1
  have := e1.unique e2
  simpa using this

theorem central_of_countable_commutators_unitary :
    ∀ (n : ℕ) (J a : Matrix (Fin n) (Fin n) ℂ) (S : Set (Matrix (Fin n) (Fin n) ℂ)), Jᴴ = J → IsUnit J.det → IsUnit a.det → S.Countable → (∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, ∀ t : ℝ, NormedSpace.exp (t • X) * a * NormedSpace.exp (-(t • X)) * a⁻¹ ∈ S) → ∀ u, u * a = a * u := by
  intro n J a S hJ hJu ha hS h u
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * J + J * X = 0 → X * a = a * X :=
    fun X hX => commute_of_countable_commutators_exp X a S ha hS (h X hX)
  set v : Matrix (Fin n) (Fin n) ℂ := J⁻¹ * uᴴ * J with hv
  have hJv : J * v = uᴴ * J := by
    rw [hv, Matrix.mul_assoc, ← Matrix.mul_assoc J, Matrix.mul_nonsing_inv J hJu, Matrix.one_mul]
  have hvJ : vᴴ * J = J * u := by
    have := congrArg Matrix.conjTranspose hJv
    simpa [Matrix.conjTranspose_mul, hJ] using this
  have h1 := key (u - v) (by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, hJv, hvJ]; abel)
  have h2 := key (Complex.I • (u + v)) (by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, hJv, hvJ, add_comm (J * u), ← add_smul]
    simp)
  rw [Matrix.smul_mul, Matrix.mul_smul] at h2
  have h3 : (u + v) * a = a * (u + v) := smul_right_injective _ Complex.I_ne_zero h2
  have h4 : (2 : ℂ) • (u * a) = (2 : ℂ) • (a * u) := by
    rw [Matrix.sub_mul, Matrix.mul_sub] at h1
    rw [Matrix.add_mul, Matrix.mul_add] at h3
    rw [two_smul, two_smul]
    calc u * a + u * a = (u * a - v * a) + (u * a + v * a) := by abel
      _ = (a * u - a * v) + (a * u + a * v) := by rw [h1, h3]
      _ = a * u + a * u := by abel
  exact smul_right_injective _ two_ne_zero h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyPsiEqMapMinpoly
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem charpoly_psi_eq_map_minpoly {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (γ : G.C)
    (hdeg : (minpoly G.F γ).natDegree = G.n) :
    (G.psi v γ).charpoly = (minpoly G.F γ).map v.embedding := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a :=
    fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ := { G.psi v with commutes' := hg }
  let L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral ℂ (G.psi v γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℂ (G.psi v γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.psi v γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.psi v γ) ((minpoly G.F γ).map v.embedding) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : ((minpoly G.F γ).map v.embedding).Monic := (minpoly.monic hFint).map _
  have hn1 : ((minpoly G.F γ).map v.embedding).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem charpoly_psi_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (g : G.C),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).Separable → (G.psi v g).charpoly.Separable := by
  intro p _ G v g hdeg hsep
  rw [charpoly_psi_eq_map_minpoly G v g hdeg]
  exact hsep.map

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyTensorLeftMulConjOneTmul
section
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory

theorem conj_one_tmul_charpoly : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (x : (R ⊗[ℚ] A)ˣ) (y : A), (LevelExists.mulMatAlg R A ((x : R ⊗[ℚ] A) * (1 ⊗ₜ[ℚ] y) * ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A))).charpoly = (LinearMap.mulLeft ℚ y).charpoly.map (algebraMap ℚ R) := by
  intro R _ _ A _ _ _ x y
  set b := Module.finBasis ℚ A
  set u := Units.map (LevelExists.mulMatAlg R A).toMonoidHom x with hu
  have h1 : LevelExists.mulMatAlg R A (x : R ⊗[ℚ] A) = (u : Matrix _ _ R) := rfl
  have h2 : LevelExists.mulMatAlg R A ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A) = ((u⁻¹ : (Matrix _ _ R)ˣ) : Matrix _ _ R) := by
    rw [hu, ← map_inv]; rfl
  have hM : LevelExists.mulMatAlg R A (1 ⊗ₜ[ℚ] y) =
      (LinearMap.toMatrix b b (LinearMap.mulLeft ℚ y)).map (algebraMap ℚ R) := by
    ext i j
    simp [LevelExists.mulMatAlg, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_repr_tmul, b, Algebra.leftMulMatrix_eq_repr_mul]
  rw [map_mul, map_mul, h1, h2, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hM, Matrix.charpoly_map,
    LinearMap.charpoly_toMatrix]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactFibrationSectionMeasureStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_fibration_section_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  first | exact @GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod | exact GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod | (intros; apply GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeRealSpecialUnitaryEqFlagDomainMassStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_realSpecialUnitary_eq_flagDomain_mass : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)], 1 ≤ r → (∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) → IsOrth X x → IsFundSet X x FF → ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) * muF X x FF = covolume (inReal X.Ψ X.Gm X.Γ) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) := by
  first | exact @GlobalTheory.SUCovol.covolume_realSU | exact GlobalTheory.SUCovol.covolume_realSU | (intros; apply GlobalTheory.SUCovol.covolume_realSU <;> assumption)
end

