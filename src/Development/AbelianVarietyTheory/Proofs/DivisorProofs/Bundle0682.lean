import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0641
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientJetsFderivDetNeZero
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory

theorem quot_jets_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  intro n
  refine ⟨1 / (4 * ((n : ℝ) + 1)), by positivity, ?_⟩
  intro p w0 w hw0 hw h0 hL0 hwp hLj
  set ε : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hε4 : ε ≤ 1 / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set a := w0 p with ha_def
  have ha_norm : 3 / 4 ≤ ‖a‖ := by
    have h1 : ‖(1:ℂ)‖ ≤ ‖a‖ + ‖a - 1‖ := by
      have := norm_sub_le a (a - 1)
      simpa using this
    simp at h1
    linarith
  have ha : a ≠ 0 := by
    intro h; rw [h] at ha_norm; simp at ha_norm; linarith
  refine ⟨ha, ?_⟩
  set L0 := fderiv ℂ w0 p with hL0_def
  have hL0' : ‖L0‖ ≤ ε := by
    have := hL0; rwa [fderiv_sub_const] at this
  have hproj : ∀ j : Fin n, HasFDerivAt (fun v : V n => v j - p j) (EuclideanSpace.proj (𝕜 := ℂ) j) p := by
    intro j
    have := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt (x := p)
    exact this.sub_const (p j)
  have hLj' : ∀ j : Fin n, ∀ ξ : V n, ‖fderiv ℂ (w j) p ξ - ξ j‖ ≤ ε * ‖ξ‖ := by
    intro j ξ
    have hd : fderiv ℂ (fun v : V n => w j v - (v j - p j)) p
        = fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j :=
      ((hw j).hasFDerivAt.sub (hproj j)).fderiv
    have := (fderiv ℂ (fun v : V n => w j v - (v j - p j)) p).le_opNorm ξ
    rw [hd] at this
    have h2 := hLj j
    rw [hd] at h2
    calc ‖fderiv ℂ (w j) p ξ - ξ j‖ = ‖(fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j) ξ‖ := by simp
      _ ≤ _ := this
      _ ≤ ε * ‖ξ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  set F : V n → V n := fun v => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) with hF
  have hq : ∀ j : Fin n, HasFDerivAt (fun v => w j v / w0 v)
      (w j p • ((-(a ^ 2)⁻¹) • L0) + a⁻¹ • fderiv ℂ (w j) p) p := by
    intro j
    have hinv : HasFDerivAt (fun v => (w0 v)⁻¹) ((-(a ^ 2)⁻¹) • L0) p :=
      (hasDerivAt_inv ha).comp_hasFDerivAt p hw0.hasFDerivAt
    have := HasFDerivAt.mul (hw j).hasFDerivAt hinv
    have e : (fun v => w j v / w0 v) = (w j * fun v => (w0 v)⁻¹) := by
      funext v; simp [div_eq_mul_inv]
    rw [e]; exact this
  have hFd : DifferentiableAt ℂ F p := by
    rw [differentiableAt_piLp]
    intro j
    simpa [hF] using (hq j).differentiableAt
  set D := fderiv ℂ F p with hD
  have hDj : ∀ j : Fin n, ∀ ξ : V n, (D ξ) j = w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ := by
    intro j ξ
    have h1 : HasFDerivAt (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) ((EuclideanSpace.proj (𝕜 := ℂ) j).comp D) p :=
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt.comp p hFd.hasFDerivAt
    have h2 : (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) = fun v => w j v / w0 v := by
      funext v; simp [hF]
    rw [h2] at h1
    have := congrArg (fun T : V n →L[ℂ] ℂ => T ξ) (h1.unique (hq j))
    simpa using this
  have hinj : ∀ ξ : V n, D ξ = 0 → ξ = 0 := by
    intro ξ hξ
    have hcoord : ∀ j : Fin n, ‖ξ j‖ ≤ 2 * ε * ‖ξ‖ := by
      intro j
      have e := hDj j ξ
      rw [hξ] at e
      simp only [PiLp.zero_apply] at e
      have e2 : a * fderiv ℂ (w j) p ξ = w j p * L0 ξ := by
        have : a ^ 2 * (w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ) = 0 := by
          rw [← e]; ring
        field_simp at this
        linear_combination this
      have hL0ξ : ‖L0 ξ‖ ≤ ε * ‖ξ‖ := (L0.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hL0' (norm_nonneg _))
      have e3 : ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ ≤ ε * (ε * ‖ξ‖) := by
        rw [← norm_mul, e2, norm_mul]
        exact mul_le_mul (hwp j) hL0ξ (norm_nonneg _) hεpos.le
      have e4 : ‖fderiv ℂ (w j) p ξ‖ ≤ ε * ‖ξ‖ := by
        by_contra hc
        push_neg at hc
        have : (3/4) * (ε * ‖ξ‖) < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := by
          calc (3/4) * (ε * ‖ξ‖) ≤ ‖a‖ * (ε * ‖ξ‖) := mul_le_mul_of_nonneg_right ha_norm (by positivity)
            _ < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := mul_lt_mul_of_pos_left hc (by linarith)
        have : ε * (ε * ‖ξ‖) ≤ (3/4) * (ε * ‖ξ‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
      have e5 := hLj' j ξ
      have : ‖ξ j‖ ≤ ‖fderiv ℂ (w j) p ξ‖ + ‖fderiv ℂ (w j) p ξ - ξ j‖ := by
        have := norm_sub_le (fderiv ℂ (w j) p ξ) (fderiv ℂ (w j) p ξ - ξ j)
        simpa using this
      linarith
    have hsq : ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖ξ.ofLp i‖ ^ 2 ≤ ∑ _i : Fin n, (2 * ε * ‖ξ‖) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
        _ = (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by simp
    have hc : (n : ℝ) * (2 * ε) ^ 2 ≤ 1 / 4 := by
      rw [hε]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      rw [show (2 * (1 / (4 * ((n:ℝ) + 1)))) ^ 2 = 1 / (4 * ((n:ℝ)+1)^2) by field_simp; ring]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : ‖ξ‖ ^ 2 ≤ (1/4) * ‖ξ‖ ^ 2 := by
      calc ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := hsq
        _ = ((n : ℝ) * (2 * ε) ^ 2) * ‖ξ‖ ^ 2 := by ring
        _ ≤ (1/4) * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have : ‖ξ‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖ξ‖]
    simpa using this
  intro hdet
  have h := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (D : V n →ₗ[ℂ] V n))).1 hdet
  apply h
  rw [LinearMap.ker_eq_bot']
  intro m hm
  exact hinj m hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundaries
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz.RedCob

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ τ : Type} {d : ℕ}

def Pt (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ τ : Type}
    (u : σ → MvPowerSeries τ (Fr p k)) (u' : σ → MvPowerSeries τ k) : Prop :=
  (∀ i, constantCoeff (u i) = 0) ∧ ∀ i, Red p (u i) (u' i)

variable [PerfectRing k p]

theorem red_subst [Finite σ] {u : σ → MvPowerSeries τ (Fr p k)} {u' : σ → MvPowerSeries τ k}
    (h : Pt p u u') {f : MvPowerSeries σ (Fr p k)} {f' : MvPowerSeries σ k} (hf : Red p f f') :
    Red p (subst u f) (subst u' f') :=
  (GlobalTheory.Katz.red_subst p k σ τ u u' h.1 h.2).1 f f' hf

end GlobalTheory.Katz.RedCob

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_lift_self [CharP k p] {σ : Type} (f : MvPowerSeries σ k) :
    _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.lift p f) f := by
  unfold _root_.GlobalTheory.Katz.Red
  intro α
  exact ⟨WittVector.teichmuller p (coeff α f), _root_.GlobalTheory.Katz.coeff_lift p f α,
    by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
omit [CharP k p] [PerfectRing k p] in
private theorem constantCoeff_at2_eq_zero {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) R} {a b : Fin d → MvPowerSeries τ R}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (hf : constantCoeff f = 0) : constantCoeff (_root_.GlobalTheory.Katz.at2 f a b) = 0 := by
  have h : ∀ s, constantCoeff (Sum.elim a b s) = 0 := by
    rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h hf

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
private theorem red_at2_of_red {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    {f' : MvPowerSeries (Fin d ⊕ Fin d) k}
    {a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k)} {a' b' : Fin d → MvPowerSeries τ k}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (ha : ∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i))
    (hb : ∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i))
    (hf : _root_.GlobalTheory.Katz.Red p f f') :
    _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.at2 f a b)
      (_root_.GlobalTheory.Katz.at2 f' a' b') := by
  unfold _root_.GlobalTheory.Katz.at2
  refine (_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b)
    (Sum.elim a' b') ?_ ?_).1 f f' hf
  · rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  · rintro (i | i)
    · exact ha i
    · exact hb i

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_X' {σ : Type} (s : σ) :
    _root_.GlobalTheory.Katz.Red p (X s : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k))
      (X s) := by
  classical
  unfold _root_.GlobalTheory.Katz.Red
  intro α
  refine ⟨if α = Finsupp.single s 1 then 1 else 0, ?_, ?_⟩
  · rw [coeff_X]; split_ifs <;> simp
  · rw [coeff_X]; split_ifs <;> simp

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_sub_divisor {σ : Type} {f g : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k)}
    {f' g' : MvPowerSeries σ k} (hf : _root_.GlobalTheory.Katz.Red p f f')
    (hg : _root_.GlobalTheory.Katz.Red p g g') :
    _root_.GlobalTheory.Katz.Red p (f - g) (f' - g') := by
  unfold _root_.GlobalTheory.Katz.Red at *
  intro α
  obtain ⟨v, hv, hv'⟩ := hf α
  obtain ⟨w, hw, hw'⟩ := hg α
  exact ⟨v - w, by rw [map_sub, map_sub, hv, hw], by rw [map_sub, map_sub, hv', hw']⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_add_divisor {σ : Type} {f g : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k)}
    {f' g' : MvPowerSeries σ k} (hf : _root_.GlobalTheory.Katz.Red p f f')
    (hg : _root_.GlobalTheory.Katz.Red p g g') :
    _root_.GlobalTheory.Katz.Red p (f + g) (f' + g') := by
  unfold _root_.GlobalTheory.Katz.Red at *
  intro α
  obtain ⟨v, hv, hv'⟩ := hf α
  obtain ⟨w, hw, hw'⟩ := hg α
  exact ⟨v + w, by rw [map_add, map_add, hv, hw], by rw [map_add, map_add, hv', hw']⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
private theorem at2_mem_intBy_of_red {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    {a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k)} {a' b' : Fin d → MvPowerSeries τ k}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (ha : ∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i))
    (hb : ∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i)) (c : WittVector p k)
    (hf : f ∈ _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) c) :
    _root_.GlobalTheory.Katz.at2 f a b ∈ _root_.GlobalTheory.Katz.intBy p k τ c := by
  unfold _root_.GlobalTheory.Katz.at2
  refine (_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b)
    (Sum.elim a' b') ?_ ?_).2 c f hf
  · rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  · rintro (i | i)
    · exact ha i
    · exact hb i

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in

theorem _root_.GlobalTheory.Katz.red_coboundaries : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ i, constantCoeff (μ i) = 0) → (∀ g c, _root_.GlobalTheory.Katz.Red p g c → _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob2 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) g) (_root_.GlobalTheory.Katz.cob2 μ c) ∧ _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.swap g) (_root_.GlobalTheory.Katz.swap c)) ∧ (∀ b b', _root_.GlobalTheory.Katz.Red p b b' → _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) b) (_root_.GlobalTheory.Katz.cob1 μ b') ∧ _root_.GlobalTheory.Katz.RedV p (_root_.GlobalTheory.Katz.lin b) (_root_.GlobalTheory.Katz.lin b')) ∧ (∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3) i) (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3) i) ∧ _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3 i) (_root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3 i)) ∧ ∀ (c : WittVector p k) g, g ∈ _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) c → _root_.GlobalTheory.Katz.cob2 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) g ∈ _root_.GlobalTheory.Katz.intBy p k _ c ∧ _root_.GlobalTheory.Katz.swap g ∈ _root_.GlobalTheory.Katz.intBy p k _ c := by
  intro p _ k _ _ _ d μ hμ
  have hL₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.lift p (μ i)) = 0 := fun i =>
    _root_.GlobalTheory.Katz.constantCoeff_lift p (hμ i)
  have hL : ∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.lift p (μ i)) (μ i) :=
    fun i => red_lift_self (μ i)
  have hop : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k))
      (a' b' : Fin d → MvPowerSeries τ k),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      (∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i)) →
      (∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i)) →
      (∀ i, constantCoeff (_root_.GlobalTheory.Katz.op
        (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) a b i) = 0) ∧
      ∀ i, _root_.GlobalTheory.Katz.Red p
        (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) a b i)
        (_root_.GlobalTheory.Katz.op μ a' b' i) := by
    intro τ a b a' b' ha₀ hb₀ ha hb
    exact ⟨fun i => constantCoeff_at2_eq_zero ha₀ hb₀ (hL₀ i),
      fun i => red_at2_of_red ha₀ hb₀ ha hb (hL i)⟩
  have hx₁₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x1 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₂₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x2 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₃₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x3 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₁ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x1 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x1 (R := k) i) := fun i => red_X' _
  have hx₂ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x2 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x2 (R := k) i) := fun i => red_X' _
  have hx₃ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x3 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x3 (R := k) i) := fun i => red_X' _
  obtain ⟨h₁₂₀, h₁₂⟩ := hop _ _ _ _ hx₁₀ hx₂₀ hx₁ hx₂
  obtain ⟨h₂₃₀, h₂₃⟩ := hop _ _ _ _ hx₂₀ hx₃₀ hx₂ hx₃
  have hl₀ : ∀ i, constantCoeff (X (Sum.inl i) :
      MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i => constantCoeff_X _
  have hr₀ : ∀ i, constantCoeff (X (Sum.inr i) :
      MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i => constantCoeff_X _
  have hl : ∀ i, _root_.GlobalTheory.Katz.Red p
      (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k))
      (X (Sum.inl i)) := fun i => red_X' _
  have hr : ∀ i, _root_.GlobalTheory.Katz.Red p
      (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k))
      (X (Sum.inr i)) := fun i => red_X' _
  refine ⟨fun g c hg => ⟨?_, ?_⟩, fun b b' hb => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩,
    fun c g hg => ⟨?_, ?_⟩⟩
  · unfold _root_.GlobalTheory.Katz.cob2
    exact red_sub_divisor (red_add_divisor (red_sub_divisor
      (red_at2_of_red hx₂₀ hx₃₀ hx₂ hx₃ hg)
      (red_at2_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ hg))
      (red_at2_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ hg))
      (red_at2_of_red hx₁₀ hx₂₀ hx₁ hx₂ hg)
  · unfold _root_.GlobalTheory.Katz.swap
    exact red_at2_of_red hr₀ hl₀ hr hl hg
  · unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
    exact red_sub_divisor (red_sub_divisor
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hL₀ hL).1 b b' hb)
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ hl₀ hl).1 b b' hb))
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ hr₀ hr).1 b b' hb)
  · unfold _root_.GlobalTheory.Katz.lin _root_.GlobalTheory.Katz.RedV
    unfold _root_.GlobalTheory.Katz.Red at hb
    intro i
    exact hb _
  · exact (hop _ _ _ _ hx₁₀ h₂₃₀ hx₁ h₂₃).2 i
  · exact (hop _ _ _ _ h₁₂₀ hx₃₀ h₁₂ hx₃).2 i
  · unfold _root_.GlobalTheory.Katz.cob2
    exact sub_mem (add_mem (sub_mem
      (at2_mem_intBy_of_red hx₂₀ hx₃₀ hx₂ hx₃ c hg)
      (at2_mem_intBy_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ c hg))
      (at2_mem_intBy_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ c hg))
      (at2_mem_intBy_of_red hx₁₀ hx₂₀ hx₁ hx₂ c hg)
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_mem_intBy_of_red hr₀ hl₀ hr hl c hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearLiftBijectiveLocalization
section
open GlobalTheory.DeRham TensorProduct

namespace GlobalTheory

theorem DeRham.localisation_of_liftSemi_bijective :
    ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R) [IsLocalization.Away f R']
      {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']
      (ρ : M →ₛₗ[algebraMap R R'] M'), Function.Bijective (GlobalTheory.DeRham.liftSemi ρ) →
      (∀ m' : M', ∃ (n : ℕ) (x : M), algebraMap R R' f ^ n • m' = ρ x) ∧
        ∀ x : M, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0 := by
  intro R R' _ _ _ f _ M M' _ _ _ _ ρ hρ
  have hloc : IsLocalizedModule (Submonoid.powers f) (TensorProduct.mk R R' M 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) R' _).2
      (TensorProduct.isBaseChange R M R')
  refine ⟨fun m' ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := hρ.2 m'
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (TensorProduct.mk R R' M 1) z
    refine ⟨n, x, ?_⟩
    have h' : (algebraMap R R' f ^ n) • z = (1 : R') ⊗ₜ[R] x := by
      rw [← map_pow, algebraMap_smul]
      exact h
    rw [← map_smul, h', liftSemi_tmul, one_smul]
  · have h0 : TensorProduct.mk R R' M 1 x = TensorProduct.mk R R' M 1 0 := by
      apply hρ.1
      simp [hx]
    obtain ⟨⟨_, n, rfl⟩, h⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h0
    exact ⟨n, by simpa [Submonoid.smul_def] using h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTw
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sh_eqv_tw : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  intro q i A B _ _ φ hA hB hq
  obtain ⟨hAl, _⟩ := hA
  obtain ⟨hBl, _⟩ := hB
  obtain ⟨ζ⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A ⟨hAl, ‹_›⟩ hq
  let S : Scheme.{0} := Spec (CommRingCat.of A)
  let ζS : Prim q Γ(S, ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ζ
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i S ζS
  have hac : ∀ (C : Type) [CommRing C], SH C → AcycF (ZMod q) (sch.obj (Spec (CommRingCat.of C))) (tw q i) :=
    fun C _ hC n hn => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) C hC (tw q i) n hn
  refine GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) S (twGen i ζS) hgen S (Spec (CommRingCat.of B)) (𝟙 S)
    (Spec.map (CommRingCat.ofHom φ)) (hac A ⟨hAl, ‹_›⟩) (hac B ⟨hBl, ‹_›⟩) ?_
  have cA := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) A
  have cB := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) B
  have hcomp : (fun φ' : LocallyConstant S (ZMod q) => φ'.comap (Spec.map (CommRingCat.ofHom φ)).base.hom) ∘
      (fun c : ZMod q => LocallyConstant.const S c) = fun c => LocallyConstant.const _ c := by
    funext c; ext x; rfl
  refine (Function.Bijective.of_comp_iff _ cA).1 ?_
  rw [hcomp]
  exact cB
end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionElementMulZeroClassEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem tMul_zero_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, TMul h₀.w t 0 y → y = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF y hy
  have iφ : IsClosedImmersion φ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hE.1)
  have iφ₀ : IsClosedImmersion φ₀ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hE.2.2.1)
  obtain ⟨f, c, hc, rfl, hred⟩ := hy
  obtain ⟨c₀, hc₀, hcl⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).1 f 0).1 hred
  rw [map_zero, CatCoh.H1.mk_eq_zero] at hcl
  obtain ⟨g₀, hg₀⟩ := hcl
  have hS := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF
  choose g hg using fun U => (hS U).2.2.1 (g₀ U)
  have key : ∀ U V (a : U ⟶ V), t • (f U V a - d0 (OAff s) g U V a) = 0 := by
    intro U V a
    rw [← (hS V).2.2.2]
    have hn := (preCoef h₀.w).naturality a (g U)
    have e := congrFun (congrFun (congrFun hg₀ U) V) a
    change preα φ₀ s s₀ V (mp (OAff s) a (g U)) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U (g U)) at hn
    rw [amitsur_d0_apply, hc₀] at e
    rw [amitsur_d0_apply, map_sub, map_sub, hn, hg, hg, ← e]
    ring
  refine CatCoh.H1.mk_eq_zero.2 ⟨t • g, ?_⟩
  rw [hc, map_smul]
  funext U V a
  have := key U V a
  simp only [Pi.smul_apply]
  rw [smul_sub, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothBumpChartBallHalfOne
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem smooth_bump_chart_ball : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (i : ι) (p : V n) (ρ : ℝ), 0 < ρ → closedBall p ρ ⊆ (A.chart i).target → ∃ χ : Y → ℝ, A.SmoothFn χ ∧ tsupport χ ⊆ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball p (ρ / 2) → χ y = 1 := by
  intro n Y _ _ _ _ _ ι La _ A i p ρ hρ hK
  let b : ContDiffBump p := ⟨ρ / 2, 3 * ρ / 4, by linarith, by linarith⟩
  have hK0 : IsCompact (closedBall p (3 * ρ / 4)) := isCompact_closedBall p _
  have hK0t : closedBall p (3 * ρ / 4) ⊆ (A.chart i).target :=
    (closedBall_subset_closedBall (by linarith)).trans hK
  have hβs : ∀ u, (b : V n → ℝ) u ≠ 0 → u ∈ closedBall p (3 * ρ / 4) := by
    intro u hu
    have : u ∈ Function.support (b : V n → ℝ) := hu
    rw [b.support_eq] at this
    exact ball_subset_closedBall this
  refine ⟨A.chiC i b, A.chiC_smooth b.contDiff hβs hK0 hK0t, ?_, ?_⟩
  · have hC := (A.isCompact_chartImage hK0 hK0t).isClosed
    have hsup : Function.support (A.chiC i b) ⊆ (A.chart i).symm '' closedBall p (3 * ρ / 4) := by
      intro y hy
      by_contra h
      exact hy (A.chiC_eq_zero hβs h)
    refine (closure_minimal hsup hC).trans ?_
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨(A.chart i).map_target (hK0t hu), ?_⟩
    show A.chart i ((A.chart i).symm u) ∈ ball p ρ
    rw [(A.chart i).right_inv (hK0t hu)]
    exact closedBall_subset_ball (by linarith) hu
  · intro y hy hb
    rw [A.chiC_of_mem hy]
    exact b.one_of_mem_closedBall (ball_subset_closedBall hb)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticSimilitudeInvertibleModNStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticSimilitude_invertible_modN : ∀ (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)), N ≠ 0 → m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) → (∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b) ∧ (∀ a, ∃ a' b, T a' = a + N • b) ∧ ∃ T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x, ∃ b, T (T' x) = x + N • b) ∧ ∀ m' : ℕ, m * m' ≡ 1 [MOD N] → ∀ x y, omegaStd (T' x) (T' y) ≡ m' * omegaStd x y [ZMOD N] := by
  first | exact @GlobalTheory.SympModN.symplecticSimilitude_modN | exact GlobalTheory.SympModN.symplecticSimilitude_modN | (intros; apply GlobalTheory.SympModN.symplecticSimilitude_modN <;> assumption)
end

