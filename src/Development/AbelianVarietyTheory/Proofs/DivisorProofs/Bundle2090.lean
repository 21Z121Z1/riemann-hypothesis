import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt
open scoped ENNReal Classical

theorem eLpNorm_sq_le_add {α : Type} [MeasurableSpace α] {μ : Measure α} (hμ : μ Set.univ ≤ 1) {f g : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ a, f a ^ 2 ≤ g a ^ 2 + C) : eLpNorm f 2 μ ^ 2 ≤ eLpNorm g 2 μ ^ 2 + ENNReal.ofReal C := by
  have key : ∀ u : α → ℝ, eLpNorm u 2 μ ^ 2 = ∫⁻ a, ENNReal.ofReal (u a ^ 2) ∂μ := fun u => by
    have e := eLpNorm_nnreal_pow_eq_lintegral (f := u) (μ := μ) (p := 2) two_ne_zero
    simp only [NNReal.coe_ofNat, ENNReal.rpow_ofNat, ENNReal.coe_ofNat] at e
    rw [e]
    refine lintegral_congr fun a => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [key, key]
  calc ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ ≤ ∫⁻ a, ENNReal.ofReal (g a ^ 2) + ENNReal.ofReal C ∂μ :=
        lintegral_mono fun a => by
          rw [← ENNReal.ofReal_add (sq_nonneg _) hC]
          exact ENNReal.ofReal_le_ofReal (h a)
    _ = ∫⁻ a, ENNReal.ofReal (g a ^ 2) ∂μ + ENNReal.ofReal C * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hμ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem denseRange_of_goodEmb {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) : DenseRange σ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h
  · exfalso
    have h1 : H.rt0 ∈ σ.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨_, hσ⟩
    rw [h] at h1
    obtain ⟨t, ht⟩ := h1
    have h2 := H.sqrt_neg_disc_sq
    rw [← ht] at h2
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h3 : t ^ 2 = -(H.d : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact h2
    nlinarith [sq_nonneg t]
  · rw [denseRange_iff_closure_range]
    exact congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h

section Model

variable {r : ℕ} {Cp : Type} [Fintype Cp] {X : Cp → FD.Data E r} {la : ∀ k, FD.Wt (X k).Ψ r}

theorem exists_ptN_le {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : FPt X, ptN la P ⟨p.1, p.2.1⟩ ≤ M :=
  ⟨(supE X la P).toReal, ENNReal.toReal_nonneg, fun p => (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top X la hP)).1
    (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p)⟩

omit [Fintype Cp] in

theorem ptN_add_le (P Q : FDSec X) (z : Σ k, FD.Frame (X k).Ψ r) : ptN la (P + Q) z ≤ ptN la P z + ptN la Q z :=
  pnorm_add_le _ _ _ _ _

omit [Fintype Cp] in

theorem ptN_smul (a : ℂ) (P : FDSec X) (z : Σ k, FD.Frame (X k).Ψ r) : ptN la (a • P) z = ‖a‖ * ptN la P z :=
  pnorm_smul _ _ _ _ _

theorem exists_ptN_sub_le {K W : Type} [Field K] [AddCommGroup W] [Module K W] {σ : K →+* ℂ} (hσ : DenseRange σ)
    (rd : W →ₛₗ[σ] FDSec X) (C : Submodule K W) (hC : ∀ f ∈ C, rd f ∈ holSub X la) {Q : FDSec X}
    (hQ : Q ∈ Submodule.span ℂ (rd '' C)) :
    ∀ ε : ℝ, 0 < ε → ∃ f ∈ C, ∀ p : FPt X, ptN la (Q - rd f) ⟨p.1, p.2.1⟩ ≤ ε := by
  have h0 : ∀ z, ptN la (0 : FDSec X) z = 0 := fun z => pnorm_zero _ _ _
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact fun ε hε => ⟨f, hf, fun p => by rw [sub_self, h0]; exact hε.le⟩
  | zero => exact fun ε hε => ⟨0, zero_mem _, fun p => by rw [map_zero, sub_self, h0]; exact hε.le⟩
  | add P Q _ _ hP hQ =>
    intro ε hε
    obtain ⟨f, hf, h₁⟩ := hP (ε / 2) (half_pos hε)
    obtain ⟨g, hg, h₂⟩ := hQ (ε / 2) (half_pos hε)
    refine ⟨f + g, add_mem hf hg, fun p => ?_⟩
    rw [map_add, show P + Q - (rd f + rd g) = (P - rd f) + (Q - rd g) by abel]
    exact (ptN_add_le _ _ _).trans (by linarith [h₁ p, h₂ p])
  | smul a P _ hP =>
    intro ε hε
    have ha : 0 < ‖a‖ + 1 := by positivity
    obtain ⟨f, hf, h₁⟩ := hP (ε / 2 / (‖a‖ + 1)) (by positivity)
    obtain ⟨M, hM, h₂⟩ := exists_ptN_le (hC f hf)
    obtain ⟨b, hb⟩ := hσ.exists_dist_lt a (show 0 < ε / 2 / (M + 1) by positivity)
    rw [dist_eq_norm, lt_div_iff₀ (by positivity)] at hb
    refine ⟨b • f, C.smul_mem b hf, fun p => ?_⟩
    rw [map_smulₛₗ, show a • P - σ b • rd f = a • (P - rd f) + (a - σ b) • rd f by
      rw [smul_sub, sub_smul]; abel]
    refine (ptN_add_le _ _ _).trans ?_
    rw [ptN_smul, ptN_smul]
    have e₁ := (le_div_iff₀ ha).1 (h₁ p)
    have e₂ := mul_le_mul_of_nonneg_left (h₂ p) (norm_nonneg (a - σ b))
    nlinarith [ptN_nonneg la (P - rd f) ⟨p.1, p.2.1⟩, norm_nonneg (a - σ b)]

variable {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (dict : Formalism.L2.Theta.GA D V → Σ k, FD.Frame (X k).Ψ r)
  (μ : Measure (AutQ V))

theorem ptN_sq_le_of_mem_span (hμ : μ Set.univ ≤ 1) (hd : ∀ g, (dict g).2 ∈ (X (dict g).1).dom)
    {K W : Type} [Field K] [AddCommGroup W] [Module K W] {σ : K →+* ℂ} (hσ : DenseRange σ)
    (rd : W →ₛₗ[σ] FDSec X) (C : Submodule K W) (hC : ∀ f ∈ C, rd f ∈ holSub X la) (z : FPt X) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ f ∈ C, ptN la (rd f) ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (petE V dict μ la (rd f)).toReal ^ 2) {Q : FDSec X}
    (hQ : Q ∈ Submodule.span ℂ (rd '' C)) :
    ptN la Q ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (petE V dict μ la Q).toReal ^ 2 := by
  have hQ' : Q ∈ holSub X la := (Submodule.span_le.2 (by rintro _ ⟨f, hf, rfl⟩; exact hC f hf)) hQ
  obtain ⟨M, hM, h₂⟩ := exists_ptN_le hQ'
  have hfin := petE_ne_top V dict μ hμ hd hQ'
  set A := (petE V dict μ la Q).toReal with hA
  have step : ∀ ε : ℝ, 0 < ε →
      ptN la Q ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2) := fun ε hε => by
    obtain ⟨f, hf, h₁⟩ := exists_ptN_sub_le hσ rd C hC hQ ε hε
    have up : ∀ p : FPt X, ptN la (rd f) ⟨p.1, p.2.1⟩ ≤ ptN la Q ⟨p.1, p.2.1⟩ + ε := fun p => by
      have e := ptN_add_le (la := la) Q ((-1 : ℂ) • (Q - rd f)) ⟨p.1, p.2.1⟩
      rw [ptN_smul, show Q + (-1 : ℂ) • (Q - rd f) = rd f by rw [neg_one_smul]; abel, norm_neg, norm_one,
        one_mul] at e
      linarith [h₁ p]
    have dn : ptN la Q ⟨z.1, z.2.1⟩ ≤ ptN la (rd f) ⟨z.1, z.2.1⟩ + ε := by
      have e := ptN_add_le (la := la) (rd f) (Q - rd f) ⟨z.1, z.2.1⟩
      rw [add_sub_cancel] at e
      linarith [h₁ z]
    have hC0 : 0 ≤ 2 * M * ε + ε ^ 2 := by positivity
    have e₁ : petE V dict μ la (rd f) ^ 2 ≤ petE V dict μ la Q ^ 2 + ENNReal.ofReal (2 * M * ε + ε ^ 2) :=
      eLpNorm_sq_le_add hμ hC0 fun q => by
        have a₁ : ptN la (rd f) (dict q.out) ≤ ptN la Q (dict q.out) + ε := up ⟨_, _, hd q.out⟩
        have a₂ : ptN la Q (dict q.out) ≤ M := h₂ ⟨_, _, hd q.out⟩
        have a₃ := pow_le_pow_left₀ (ptN_nonneg _ _ _) a₁ 2
        nlinarith
    have e₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top hfin, ENNReal.ofReal_ne_top⟩) e₁
    rw [ENNReal.toReal_add (ENNReal.pow_ne_top hfin) ENNReal.ofReal_ne_top, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hC0] at e₂
    have e₃ := (h f hf).trans (mul_le_mul_of_nonneg_left e₂ hB)
    have e₄ := pow_le_pow_left₀ (ptN_nonneg _ _ _) dn 2
    have e₅ : ptN la (rd f) ⟨z.1, z.2.1⟩ ≤ M + ε := by linarith [up z, h₂ z]
    nlinarith
  have lim : Filter.Tendsto (fun ε : ℝ => B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (B * A ^ 2)) := by
    refine Filter.Tendsto.mono_left (Continuous.tendsto' (by fun_prop) _ _ (by simp)) nhdsWithin_le_nhds
  exact ge_of_tendsto lim (eventually_nhdsWithin_of_forall step)

end Model

section Berg

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : Formalism.BasicNotions.D7}
  {V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D}
  {dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r} {Z : Comp Xo c}

theorem eq_zero_of_mem_span_cuspOn {G : WTZ E} {σ : c.F →+* ℂ} {Q : FDSec (U σ).X}
    (hQ : Q ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z G : Set (Rul Xo c))))
    {z : Σ k, FD.Frame ((U σ).X k).Ψ r} (hz : z ∉ framesOn (U σ) Z) : Q z.1 z.2 = 0 := by
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact rdU_eq_zero _ hf.2 hz
  | zero => rfl
  | add P Q _ _ hP hQ => rw [Pi.add_apply, Pi.add_apply, hP, hQ, add_zero]
  | smul a P _ hP => rw [Pi.smul_apply, Pi.smul_apply, hP, smul_zero]

theorem bergOn_le_bergCusp {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    (z : FPt (U (goodOf c σ)).X)
    (hz : (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) ∈ framesOn (U (goodOf c σ)) Z) :
    bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z ≤ bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ := by
  by_cases h : bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ = ⊤
  · exact h ▸ le_top
  have hB := (bergCusp_le_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal h).ge
  rw [← ENNReal.ofReal_toReal h]
  set B := (bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩).toReal
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  set μ := muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z
  have hμ : μ Set.univ ≤ 1 := muPart_univ_le _ _ _
  have hfin := fun P (hP : P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G)) =>
    petE_ne_top (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd hP
  refine (bergE_le_iff _ _ μ hfin z ENNReal.ofReal_ne_top).2 fun P hP => ?_
  obtain ⟨Q, hQ, hPQ⟩ := hspan P hP
  have key := ptN_sq_le_of_mem_span (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd
    (denseRange_of_goodEmb (goodEmb_goodOf c σ)) (rdU (U (goodOf c σ))) (cuspOn U Z G)
    (fun f hf => (mem_cuspW.1 hf.1).2 _ (goodEmb_goodOf c σ)) z hB0 (fun f hf => by
      have e := hB f hf
      have hl := lieFacZ_pos (Dw := Dw) x G
      simp only [homN, petOn, petAt, mul_pow] at e
      exact le_of_mul_le_mul_left (e.trans_eq (by ring)) (pow_pos hl 2)) hQ
  have hle : ∀ w, ptN (modelWt (U (goodOf c σ)) G) Q w ≤ ptN (modelWt (U (goodOf c σ)) G) P w := fun w => by
    by_cases hw : w ∈ framesOn (U (goodOf c σ)) Z
    · simp only [ptN, FD.Data.pnorm, hPQ w hw, le_refl]
    · refine le_trans (le_of_eq ?_) (ptN_nonneg _ P w)
      simp only [ptN, FD.Data.pnorm, eq_zero_of_mem_span_cuspOn hQ hw, norm_zero, zero_mul]
  have hpet : petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) Q ≤
      petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) P :=
    eLpNorm_mono fun q => by
      rw [Real.norm_of_nonneg (ptN_nonneg _ _ _), Real.norm_of_nonneg (ptN_nonneg _ _ _)]
      exact hle _
  have hz' : ptN (modelWt (U (goodOf c σ)) G) P ⟨z.1, z.2.1⟩ = ptN (modelWt (U (goodOf c σ)) G) Q ⟨z.1, z.2.1⟩ := by
    have := hPQ _ hz
    simp only [ptN, FD.Data.pnorm] at this ⊢
    rw [this]
  have e := key.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono (hfin P hP) hpet) 2) hB0)
  rw [hz', ← ENNReal.ofReal_toReal (hfin P hP), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _),
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hB0]
  exact ENNReal.ofReal_le_ofReal e

theorem bergCusp_eq_bergOn {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    (z : FPt (U (goodOf c σ)).X)
    (hz : (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) ∈ framesOn (U (goodOf c σ)) Z) :
    bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ = bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z :=
  le_antisymm (bergCusp_le_bergOn hd z) (bergOn_le_bergCusp hd hspan z hz)

end Berg

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharZeroEigenformSurvivingCompositionFacto
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.ExpFrame.Eigenform

theorem mem_of_ann {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (m : Ideal R) [m.IsPrime]
    (hne : ¬ Subsingleton (LocalizedModule m.primeCompl M)) (p : R) (hp : ∀ x : M, p • x = 0) : p ∈ m := by
  by_contra hpm
  apply hne
  have key : ∀ z : LocalizedModule m.primeCompl M, z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h f s =>
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨p, hpm⟩, ?_⟩
      show (p : R) • ((s : R) • f) = (p : R) • ((s : R) • (0 : M))
      rw [smul_zero, smul_zero, hp]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem loc_subsingleton {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (S : Submonoid R)
    (h : ∀ x : M, x = 0) : Subsingleton (LocalizedModule S M) := by
  have key : ∀ z : LocalizedModule S M, z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h f s => rw [h f, LocalizedModule.zero_mk]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem nabla_zero_of_not_antitone {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (τ0 : ι) (hτ0 : ¬ Antitone (res N (mu τ0))) : ∀ z : NablaT F.O N mu, z = 0 := by
  have hbot := GlobalTheory.T.dualWeyl_eq_bot_of_not_antitone' F.O N (res N (mu τ0)) hτ0
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hx : x τ0 = 0 :=
      Subtype.ext ((Submodule.eq_bot_iff _).1 hbot ((x τ0 : Formalism.GradedWeylDivisibility.dualWeyl F.O N N (res N (mu τ0))) : MvPolynomial _ F.O) (x τ0).2)
    rw [(PiTensorProduct.tprod F.O).map_coord_zero τ0 hx, smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem quot_ker_stable {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (jKm : F.K →* alg F.O N mu) (ϖ : F.O) (κ : F.K) (x : NablaT F.O N mu)
    (hx : x ∈ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu))) :
    repOf F.O (A := alg F.O N mu) jKm (NablaT F.O N mu) κ x ∈ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)) := by
  have hle : (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)).map (repOf F.O (A := alg F.O N mu) jKm (NablaT F.O N mu) κ) ≤
      (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨x, hx, rfl⟩

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Lift
variable {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam mu : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) (jKm : F.K →* alg F.O N mu) (ϖ : F.O)
  (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm]
  [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)] [Module F.T (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu))]

theorem hecke_compat (hH : F.IsHecke lam jK Gm) (hHm : F.IsHecke mu jKm (NablaT F.O N mu))
    (π : NablaT F.O N mu →ₗ[F.O] (NablaT F.O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu))))
    (ψ : Gm →+ (NablaT F.O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu))))
    (hψs : ∀ (c : F.O) (w : Gm), ψ (c • w) = c • ψ w) (q : F.T)
    (x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) (z : Forms F.O (A := alg F.O N lam) F.Γ jK Gm)
    (hxz : ∀ g, π ((x : F.G → NablaT F.O N mu) g) = ψ ((z : F.G → Gm) g)) (g : F.G) :
    π (((q • x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) : F.G → NablaT F.O N mu) g) =
      ψ (((q • z : Forms F.O (A := alg F.O N lam) F.Γ jK Gm) : F.G → Gm) g) := by
  induction q using MvPolynomial.induction_on generalizing x z g with
  | C c =>
    rw [hHm.1, hH.1]
    simp only [Submodule.coe_smul, Pi.smul_apply]
    rw [map_smul, hxz, hψs]
  | add p q hp hq =>
    rw [add_smul, add_smul]
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    rw [hp x z hxz g, hq x z hxz g]
  | mul_X p i hp =>
    rw [mul_comm, mul_smul, mul_smul, hHm.2, hH.2, map_smul, hψs, map_sum, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => hp x z hxz (g * s)

theorem ann_lift (hOk : F.Ok) (hJ : F.IsJ lam jK) (hJm : F.IsJ mu jKm)
    (hH : F.IsHecke lam jK Gm) (hHm : F.IsHecke mu jKm (NablaT F.O N mu)) (hE : Embeds F.O N lam mu ϖ Gm) (p : F.T)
    (hp : ∀ x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu), p • x = 0)
    (y : Forms F.O (A := alg F.O N lam) F.Γ jK Gm) : p • y = 0 := by
  obtain ⟨ψ, hψi, hψc, hψg, -⟩ := hE
  have hψs : ∀ (c : F.O) (w : Gm), ψ (c • w) = c • ψ w := by
    intro c w
    rw [← algebraMap_smul (alg F.O N lam) c w, hψc]
  obtain ⟨Fm, hFm, hFπ⟩ := GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers F.O F.G F.Γ F.K (NablaT F.O N mu)
      (NablaT F.O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)))
      (repOf F.O (A := alg F.O N mu) jKm (NablaT F.O N mu)) (Submodule.mkQ _) (Submodule.mkQ_surjective _)
      (by
        intro κ x hx
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
        exact quot_ker_stable F mu jKm ϖ κ x hx)
      (fun g => ⟨(hOk.tame g).1, GlobalTheory.T.isUnit_natCast_frameCoeffRing_not_dvd l ι N F hOk _ (hOk.tame g).2⟩)
      (fun g => ψ ((y : F.G → Gm) g))
      (by
        intro γ g κ yy hyy
        have hy := y.2 γ g κ
        show ψ ((y : F.G → Gm) ((γ : F.G) * g * κ)) = _
        rw [hy]
        show ψ (jK κ⁻¹ • (y : F.G → Gm) g) = Submodule.mkQ _ (jKm κ⁻¹ • yy)
        rw [hJ κ⁻¹, hJm κ⁻¹, smul_assoc, hψs, hψg _ _ _ hyy, smul_assoc, Submodule.mkQ_apply,
          Submodule.Quotient.mk_smul]
        rfl)
  apply Subtype.ext
  funext g
  apply hψi
  have := hecke_compat F lam mu jK jKm ϖ Gm hH hHm (Submodule.mkQ _) ψ hψs p ⟨Fm, hFm⟩ y (fun g => hFπ g) g
  rw [hp] at this
  simp only [Submodule.coe_zero, Pi.zero_apply, map_zero] at this ⊢
  exact this.symm

end Lift

section Eig
variable {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (mu : ι → ℕ → ℕ)
  (jKm : F.K →* alg F.O N mu)

theorem tf_forms (hOk : F.Ok) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu) (hbi : Function.Injective b)
    (c : F.O) (x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) (hcx : c • x = 0) : c = 0 ∨ x = 0 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  apply Subtype.ext
  funext g
  have h1 : c • (x : F.G → NablaT F.O N mu) g = 0 := by
    have := congrArg (fun y : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu) => (y : F.G → NablaT F.O N mu) g) hcx
    simpa using this
  have h2 : F.emb c • b ((x : F.G → NablaT F.O N mu) g) = 0 := by rw [← map_smulₛₗ, h1, map_zero]
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd (hOk.ring.1 (h.trans (map_zero _).symm)) hc
  · exact hbi (h.trans (map_zero b).symm)

def jmap (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu) :
    Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu) →ₛₗ[F.emb] (F.G → NablaT (PadicAlgCl l) N mu) where
  toFun x g := b ((x : F.G → NablaT F.O N mu) g)
  map_add' x y := by funext g; simp
  map_smul' c x := by funext g; simp [map_smulₛₗ]

def heckeQ (i : F.I) : (F.G → NablaT (PadicAlgCl l) N mu) →ₗ[PadicAlgCl l] (F.G → NablaT (PadicAlgCl l) N mu) where
  toFun h g := F.emb (F.cst i) • ∑ s ∈ F.tr i, h (g * s)
  map_add' h h' := by funext g; simp [Finset.sum_add_distrib, smul_add]
  map_smul' c h := by funext g; simp [Finset.smul_sum, smul_comm c]

theorem form_of_mem_span (hJm : F.IsJ mu jKm) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu)
    (hbg : ∀ g x, b (grp F.O N mu g x) = grp (PadicAlgCl l) N mu (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x))
    (w : F.G → NablaT (PadicAlgCl l) N mu) (hw : w ∈ Submodule.span (PadicAlgCl l) (Set.range (jmap F mu jKm b))) :
    F.IsForm mu w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    constructor
    · intro γ hγ g
      have hx := x.2 ⟨γ, hγ⟩ g 1
      show b ((x : F.G → NablaT F.O N mu) (γ * g)) = b ((x : F.G → NablaT F.O N mu) g)
      simp only [OneMemClass.coe_one, mul_one, inv_one, map_one] at hx
      rw [hx]
      rfl
    · intro κ g
      have hx := x.2 1 g κ
      simp only [OneMemClass.coe_one, one_mul] at hx
      show F.emb (F.chi κ) • grp (PadicAlgCl l) N mu _ (b ((x : F.G → NablaT F.O N mu) (g * κ))) =
        b ((x : F.G → NablaT F.O N mu) g)
      rw [← hbg, ← map_smulₛₗ, hx]
      congr 1
      show (F.chi κ : F.O) • grp F.O N mu (F.kap κ) (jKm κ⁻¹ • (x : F.G → NablaT F.O N mu) g) = _
      have h2 : (F.chi κ : F.O) • grp F.O N mu (F.kap κ) (jKm κ⁻¹ • (x : F.G → NablaT F.O N mu) g) =
          jKm κ • jKm κ⁻¹ • (x : F.G → NablaT F.O N mu) g := by
        rw [hJm κ, smul_assoc]
        rfl
      rw [h2, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  | zero => exact ⟨fun _ _ _ => rfl, fun _ _ => by simp⟩
  | add w w' _ _ hw hw' =>
    refine ⟨fun γ hγ g => by simp [hw.1 γ hγ g, hw'.1 γ hγ g], fun κ g => ?_⟩
    simp only [Pi.add_apply, map_add, smul_add]
    rw [hw.2 κ g, hw'.2 κ g]
  | smul c w _ hw =>
    refine ⟨fun γ hγ g => by simp [hw.1 γ hγ g], fun κ g => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [smul_comm, hw.2 κ g]

variable [Module F.T (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu))]
  [IsScalarTower F.O F.T (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu))]

theorem jmap_equiv (hHm : F.IsHecke mu jKm (NablaT F.O N mu)) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu)
    (i : F.I) (x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) :
    jmap F mu jKm b ((MvPolynomial.X i : F.T) • x) = heckeQ F mu i (jmap F mu jKm b x) := by
  funext g
  show b ((((MvPolynomial.X i : F.T) • x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) : F.G → NablaT F.O N mu) g) =
    F.emb (F.cst i) • ∑ s ∈ F.tr i, b ((x : F.G → NablaT F.O N mu) (g * s))
  rw [hHm.2 i x g, map_smulₛₗ, map_sum]

theorem eig_of_ann (hOk : F.Ok) (hJm : F.IsJ mu jKm) (hHm : F.IsHecke mu jKm (NablaT F.O N mu))
    (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu) (hbi : Function.Injective b)
    (hbg : ∀ g x, b (grp F.O N mu g x) = grp (PadicAlgCl l) N mu (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x))
    (hbli : ∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a))
    (m : Ideal F.T) [m.IsMaximal]
    (hannM : ∀ p : F.T, (∀ x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu), p • x = 0) → p ∈ m) :
    ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  have h1 := GlobalTheory.T.module_finite_frameLatticeForms l ι N F mu jKm hOk
  have h2 := tf_forms F mu jKm hOk b hbi
  have h3 := GlobalTheory.T.linearIndependent_frameForms_baseChange l ι N F mu jKm b hbi hOk hbli
  have h4 := jmap_equiv F mu jKm hHm b
  have h5 := @GlobalTheory.T.exists_integral_hecke_eigensystem_deligne_serre l _ F.O _ _ _ F.emb hOk.ring.1 hOk.ring.2 F.I (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) _ _ _ _ h1
  obtain ⟨θ, hθ1, hθ2, v, hvspan, hv0, hvT⟩ := h5 h2 (F.G → NablaT (PadicAlgCl l) N mu) (jmap F mu jKm b) (heckeQ F mu) h3 h4 m inferInstance hannM
  exact ⟨θ, ⟨v, hv0, form_of_mem_span F mu jKm hJm b hbg v hvspan, fun i g => congrFun (hvT i) g⟩, hθ1, hθ2⟩

end Eig

theorem eigenform_of_surviving : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (ϖ : F.O), F.Ok → F.IsJ lam jK → Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)], F.IsHecke lam jK Gm → Embeds F.O N lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal], ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)) → ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  intro l _ ι _ _ N F lam mu jK ϖ hOk hJ hϖ Gm _ _ _ _ _ hH hE m _ hne
  have hann := mem_of_ann m hne
  by_cases hdom : ∀ τ, Antitone (res N (mu τ))
  swap
  · exfalso
    push_neg at hdom
    obtain ⟨τ0, hτ0⟩ := hdom
    have h0 := nabla_zero_of_not_antitone F mu τ0 hτ0
    obtain ⟨ψ, hψi, -, -, -⟩ := hE
    have hG : ∀ a : Gm, a = 0 := by
      intro a
      apply hψi
      obtain ⟨ya, hya⟩ := Submodule.Quotient.mk_surjective _ (ψ a)
      rw [map_zero, ← hya, h0 ya, Submodule.Quotient.mk_zero]
    exact hne (loc_subsingleton _ fun f => Subtype.ext (funext fun g => hG _))
  obtain ⟨jKm, hJm⟩ := GlobalTheory.ExpFrame.levelMap_exists l ι N F mu
  obtain ⟨instT, instTS, hHm⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module l ι N F mu jKm hOk hJm (NablaT F.O N mu)
  obtain ⟨b, hbi, -, -, hbg, hbli, -⟩ := GlobalTheory.LatBC.baseChange_lattices l ι N F mu hOk.ring.1 hdom
  exact eig_of_ann F mu jKm hOk hJm hHm b hbi hbg hbli m
    (fun p hp => hann p (ann_lift F lam mu jK jKm ϖ Gm hOk hJ hJm hH hHm hE p hp))

end GlobalTheory.ExpFrame.Eigenform

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponentStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_upperLevel_subgroup_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  first | exact @GlobalTheory.upperLevel_isSubgroup | exact GlobalTheory.upperLevel_isSubgroup | (intros; apply GlobalTheory.upperLevel_isSubgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentDatumLeOfPrimePowerLatticeInclusionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ), LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  first | exact @GlobalTheory.ExpTie.jexpU_le_of_lIncl | exact GlobalTheory.ExpTie.jexpU_le_of_lIncl | (intros; apply GlobalTheory.ExpTie.jexpU_le_of_lIncl <;> assumption)
end

