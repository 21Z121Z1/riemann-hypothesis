import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubAbscissaEqOneOfUnitDiscrIntegralChords
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar

variable {p : ℕ} [Fact p.Prime]

theorem norm_le_one_of_quad {a c m : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (h : ‖m ^ 2 + a * m - c‖ ≤ 1) : ‖m‖ ≤ 1 := by
  by_contra hm
  push_neg at hm
  have e : m ^ 2 = (m ^ 2 + a * m - c) + (-(a * m) + c) := by ring
  have hb : ‖m ^ 2‖ ≤ ‖m‖ := by
    rw [e]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (h.trans hm.le) ?_)
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (hc.trans hm.le))
    rw [norm_neg, norm_mul]
    calc ‖a‖ * ‖m‖ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ = ‖m‖ := one_mul _
  rw [norm_pow, sq] at hb
  have : 1 * ‖m‖ < ‖m‖ * ‖m‖ := mul_lt_mul_of_pos_right hm (by linarith)
  linarith

theorem norm_sub_x_eq_one : ∀ {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x₁ y₁ x₂ y₂ m m' : ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.Δ‖ = 1 → W.toAffine.Equation x₁ y₁ → W.toAffine.Equation x₂ y₂ → ‖x₁‖ ≤ 1 → ‖x₂‖ ≤ 1 → x₁ ≠ x₂ → m * (x₁ - x₂) = y₁ - y₂ → m' * (x₁ - x₂) = y₁ - W.toAffine.negY x₂ y₂ → ‖m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖x₁ - x₂‖ = 1 := by
  intro p _ W x₁ y₁ x₂ y₂ m m' h1 h2 hΔ he1 he2 hx1 hx2 hne hm hm' hq hq'
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hle : ‖x₁ - x₂‖ ≤ 1 := by
    rw [sub_eq_add_neg]; exact it_add hx1 (by rwa [norm_neg])
  refine le_antisymm hle (not_lt.mp fun hs => ?_)
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2
  have c12 : ‖W.a₂ + x₁ + x₂‖ ≤ 1 := it_add (it_add h2 hx1) hx2
  have mb : ‖m‖ ≤ 1 := norm_le_one_of_quad h1 c12
    (by rwa [show m ^ 2 + W.a₁ * m - (W.a₂ + x₁ + x₂) = m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂ by ring])
  have mb' : ‖m'‖ ≤ 1 := norm_le_one_of_quad h1 c12
    (by rwa [show m' ^ 2 + W.a₁ * m' - (W.a₂ + x₁ + x₂) = m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂ by ring])
  have s1 : ‖y₁ - y₂‖ < 1 := by rw [← hm, mul_comm]; exact sm_mul' hs mb
  have s2 : ‖y₁ + y₂ + W.a₁ * x₂ + W.a₃‖ < 1 := by
    have e : y₁ + y₂ + W.a₁ * x₂ + W.a₃ = m' * (x₁ - x₂) := by
      rw [hm']; simp only [WeierstrassCurve.Affine.negY]; ring
    rw [e, mul_comm]; exact sm_mul' hs mb'
  have s3 : ‖W.a₁ * (x₁ - x₂)‖ < 1 := sm_mul h1 hs
  have hy : ‖2 * y₁ + W.a₁ * x₁ + W.a₃‖ < 1 := by
    rw [show 2 * y₁ + W.a₁ * x₁ + W.a₃ =
      (y₁ - y₂) + (y₁ + y₂ + W.a₁ * x₂ + W.a₃) + W.a₁ * (x₁ - x₂) by ring]
    exact sm_add (sm_add s1 s2) s3
  have s4 : ‖y₁ + y₂ + W.a₁ * x₁ + W.a₃‖ < 1 := by
    rw [show y₁ + y₂ + W.a₁ * x₁ + W.a₃ = (y₁ + y₂ + W.a₁ * x₂ + W.a₃) + W.a₁ * (x₁ - x₂) by ring]
    exact sm_add s2 s3
  have e1 := he1
  have e2 := he2
  rw [WeierstrassCurve.Affine.equation_iff] at e1 e2
  have hN : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂ =
      m * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) := by
    apply mul_right_cancel₀ hd
    have hsub : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) = (x₁ - x₂) *
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) := by
      linear_combination e1 - e2
    linear_combination -hsub - (y₁ + y₂ + W.a₁ * x₁ + W.a₃) * hm
  have hN' : ‖x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂‖ < 1 := by
    rw [hN]; exact sm_mul mb s4
  have hx' : ‖3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁‖ < 1 := by
    rw [show 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ =
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) -
        ((x₂ - x₁) * (x₂ + 2 * x₁ + W.a₂) + W.a₁ * (y₁ - y₂)) by ring]
    refine sm_sub hN' (sm_add ?_ (sm_mul h1 s1))
    exact sm_mul' (by rw [← norm_neg, neg_sub]; exact hs) (it_add (it_add hx2 (it_mul n2 hx1)) h2)
  have hc := disc_small W x₁ y₁ h1 h2 hx1 he1 hy hx'
  rw [hΔ] at hc
  exact lt_irrefl _ hc

end GlobalTheory.ThetaPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormTangentDenominatorEqOneOfUnitDiscrDouble
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaPar

theorem padicComplex_norm_le_max_norm_add_norm {p : ℕ} [Fact p.Prime] {a b : ℂ_[p]} :
    ‖a‖ ≤ max ‖a + b‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max (a + b) (-b)
  simpa using this

theorem unit_of_double_integral_sub {p : ℕ} [Fact p.Prime] (a b : ℂ_[p]) :
    ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max a (-b)
  simpa [sub_eq_add_neg] using this

theorem unit_of_double_integral {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x y m : ℂ_[p])
    (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1)
    (hΔ : ‖W.Δ‖ = 1) (he : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1)
    (_hη : 2 * y + W.a₁ * x + W.a₃ ≠ 0)
    (hm : m * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hm2 : ‖m ^ 2 + W.a₁ * m - W.a₂ - 2 * x‖ ≤ 1) :
    ‖2 * y + W.a₁ * x + W.a₃‖ = 1 := by
  have he' := he
  rw [WeierstrassCurve.Affine.equation_iff] at he'
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2

  have hy : ‖y‖ ≤ 1 := by
    by_contra hy
    push_neg at hy
    have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 := by
      refine it_add (it_add (it_add ?_ (it_mul h2 ?_)) (it_mul h4 hx)) h6
      · rw [show x ^ 3 = x * x * x by ring]; exact it_mul (it_mul hx hx) hx
      · rw [sq]; exact it_mul hx hx
    have hS : ‖(W.a₁ * x + W.a₃) * y‖ ≤ ‖y‖ := by
      rw [norm_mul]
      calc ‖W.a₁ * x + W.a₃‖ * ‖y‖ ≤ 1 * ‖y‖ :=
            mul_le_mul_of_nonneg_right (it_add (it_mul h1 hx) h3) (norm_nonneg _)
        _ = ‖y‖ := one_mul _
    have hyy : ‖y‖ < ‖y ^ 2‖ := by
      rw [norm_pow, sq]; nlinarith
    have key := padicComplex_norm_le_max_norm_add_norm (a := y ^ 2) (b := (W.a₁ * x + W.a₃) * y)
    have hsum : y ^ 2 + (W.a₁ * x + W.a₃) * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
      linear_combination he'
    rw [hsum] at key
    have : ‖y ^ 2‖ ≤ 1 := by
      rcases le_max_iff.mp key with h | h
      · exact h.trans hR
      · exact absurd (h.trans hS) (not_le.mpr hyy)
    linarith
  have hηle : ‖2 * y + W.a₁ * x + W.a₃‖ ≤ 1 :=
    it_add (it_add (it_mul n2 hy) (it_mul h1 hx)) h3
  refine le_antisymm hηle (not_lt.mp fun hlt => ?_)

  have hmi : ‖m‖ ≤ 1 := by
    by_contra hmg
    push_neg at hmg
    have hT : ‖W.a₁ * m - W.a₂ - 2 * x‖ ≤ ‖m‖ := by
      have hm1 : (1 : ℝ) ≤ ‖m‖ := hmg.le
      refine le_trans (unit_of_double_integral_sub _ _) (max_le ?_ ?_)
      · refine le_trans (unit_of_double_integral_sub _ _) (max_le ?_ (h2.trans hm1))
        rw [norm_mul]
        calc ‖W.a₁‖ * ‖m‖ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = ‖m‖ := one_mul _
      · exact (it_mul n2 hx).trans hm1
    have hmm : ‖m‖ < ‖m ^ 2‖ := by rw [norm_pow, sq]; nlinarith
    have key := padicComplex_norm_le_max_norm_add_norm (a := m ^ 2) (b := W.a₁ * m - W.a₂ - 2 * x)
    rw [show m ^ 2 + (W.a₁ * m - W.a₂ - 2 * x) = m ^ 2 + W.a₁ * m - W.a₂ - 2 * x by ring] at key
    have : ‖m ^ 2‖ ≤ 1 := by
      rcases le_max_iff.mp key with h | h
      · exact h.trans hm2
      · exact absurd (h.trans hT) (not_le.mpr hmm)
    nlinarith [norm_nonneg m, show ‖m ^ 2‖ = ‖m‖ * ‖m‖ by rw [norm_pow, sq]]
  have hsmall : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ < 1 := by
    rw [← hm]; exact sm_mul hmi hlt
  have := disc_small W x y h1 h2 hx he hlt hsmall
  linarith

end GlobalTheory.ThetaPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalisedThetaPullbackMemTorsionTranslatesSpanAStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullB_th0_mem_tr : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ Tr D (tor0 D cc δ) b := by
  first | exact @GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan | exact GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan | (intros; apply GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelChordLawSumAndDifference
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.Chord

theorem chord_change {K : Type*} [Field K] [CharZero K] (e r s t a b c d : K) (he : e ≠ 0)
    (hac : a - c ≠ 0) :
    e ^ 2 * ((((b - d) / (a - c)) ^ 2 / 4 - a - c) - r) =
      ((e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
          (e ^ 2 * (a - r) - e ^ 2 * (c - r))) ^ 2 +
        (e * (2 * s)) * ((e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
          (e ^ 2 * (a - r) - e ^ 2 * (c - r))) - e ^ 2 * (3 * r - s ^ 2) -
        e ^ 2 * (a - r) - e ^ 2 * (c - r) := by
  have hm : (e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
      (e ^ 2 * (a - r) - e ^ 2 * (c - r)) = e * ((b - d) / (a - c) / 2 - s) := by
    rw [show e ^ 2 * (a - r) - e ^ 2 * (c - r) = e ^ 2 * (a - c) by ring]
    field_simp
    ring
  rw [hm]
  ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe' (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  unfold lamC
  rw [dif_pos x.2]

theorem W_a₁ (g : GL3Theta.G1 p) : g.W.a₁ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (2 * g.C.s) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₁]

theorem W_a₂ (g : GL3Theta.G1 p) :
    g.W.a₂ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (3 * g.C.r - g.C.s ^ 2) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₂]

theorem W_a₃ (g : GL3Theta.G1 p) :
    g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * (2 * g.C.t) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₃]

theorem xAt_add (g : GL3Theta.G1 p) (P Q : ℂ) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (hP : P ∉ g.abelian₂)
    (hQ : Q ∉ g.abelian₂) (h1 : P + Q ∉ g.abelian₂) (h2 : P - Q ∉ g.abelian₂) (a1 : wpF g.abelian₂ P ∈ Qbar)
    (a2 : wpD g.abelian₂ P ∈ Qbar) (a3 : wpF g.abelian₂ Q ∈ Qbar) (a4 : wpD g.abelian₂ Q ∈ Qbar) :
    GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) =
      ((yAt g P - yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 +
        g.W.a₁ * ((yAt g P - yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) -
        g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  have hne : wpF g.abelian₂ P ≠ wpF g.abelian₂ Q := fun e => by
    rcases (h.wp_eq_iff hP hQ).1 e.symm with h' | h'
    exacts [h1 h', h2 h']
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair g.abelian₂ h
  have hadd : wpF g.abelian₂ (P + Q) =
      ((wpD g.abelian₂ P - wpD g.abelian₂ Q) / (wpF g.abelian₂ P - wpF g.abelian₂ Q)) ^ 2 / 4 -
        wpF g.abelian₂ P - wpF g.abelian₂ Q := by
    simp only [GlobalTheory.LatticeInvariants.wpF_eq hL, GlobalTheory.LatticeInvariants.wpD_eq hL] at hne ⊢
    exact (GlobalTheory.weierstrassP_add L ((hL P).not.1 hP) ((hL Q).not.1 hQ) hne).1
  set A : Qbar := ⟨_, a1⟩
  set B : Qbar := ⟨_, a2⟩
  set C : Qbar := ⟨_, a3⟩
  set D : Qbar := ⟨_, a4⟩
  have eA : lamC g.lam (wpF g.abelian₂ P) = g.lam A := lamC_coe' g.lam A
  have eB : lamC g.lam (wpD g.abelian₂ P) = g.lam B := lamC_coe' g.lam B
  have eC : lamC g.lam (wpF g.abelian₂ Q) = g.lam C := lamC_coe' g.lam C
  have eD : lamC g.lam (wpD g.abelian₂ Q) = g.lam D := lamC_coe' g.lam D
  have eS : lamC g.lam (wpF g.abelian₂ (P + Q)) =
      ((g.lam B - g.lam D) / (g.lam A - g.lam C)) ^ 2 / 4 - g.lam A - g.lam C := by
    have : wpF g.abelian₂ (P + Q) = ((((B - D) / (A - C)) ^ 2 / 4 - A - C : Qbar) : ℂ) := by
      rw [hadd]; push_cast; rfl
    rw [this, lamC_coe']
    simp only [map_sub, map_div₀, map_pow, map_ofNat]
  have hAC : g.lam A - g.lam C ≠ 0 := fun e =>
    hne (congrArg Subtype.val (g.lam.injective (sub_eq_zero.1 e)))
  have he : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  rw [W_a₁, W_a₂]
  simp only [GlobalTheory.EvenTheta.xAt, yAt, eA, eB, eC, eD, eS]
  refine ⟨fun e => hAC ?_, chord_change _ _ _ _ _ _ _ _ he hAC⟩
  have := mul_left_cancel₀ (pow_ne_zero 2 he) e
  linear_combination this

theorem wpF_neg' {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) (z : ℂ) :
    wpF Λ (-z) = wpF Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  simp only [GlobalTheory.LatticeInvariants.wpF_eq hL, PeriodPair.weierstrassP_neg]

theorem wpD_neg' {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) (z : ℂ) :
    wpD Λ (-z) = -wpD Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  simp only [GlobalTheory.LatticeInvariants.wpD_eq hL, PeriodPair.derivWeierstrassP_neg]

theorem xAt_neg (g : GL3Theta.G1 p) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (Q : ℂ) :
    GlobalTheory.EvenTheta.xAt g (-Q) = GlobalTheory.EvenTheta.xAt g Q := by
  simp only [GlobalTheory.EvenTheta.xAt, wpF_neg' h]

theorem yAt_neg (g : GL3Theta.G1 p) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (Q : ℂ)
    (a4 : wpD g.abelian₂ Q ∈ Qbar) :
    yAt g (-Q) = g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (yAt g Q) := by
  have e : lamC g.lam (-wpD g.abelian₂ Q) = -lamC g.lam (wpD g.abelian₂ Q) := by
    have e1 := lamC_coe' g.lam (-(⟨_, a4⟩ : Qbar))
    have e2 := lamC_coe' g.lam (⟨_, a4⟩ : Qbar)
    rw [map_neg, ← e2] at e1
    exact e1
  have e1 : g.W.toAffine.a₁ = _ := W_a₁ g
  have e3 : g.W.toAffine.a₃ = _ := W_a₃ g
  rw [WeierstrassCurve.Affine.negY, e1, e3]
  simp only [GlobalTheory.EvenTheta.xAt, yAt, wpF_neg' h, wpD_neg' h, e]
  ring

theorem model_chord : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P Q : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → Q ∉ g.abelian₂ → P + Q ∉ g.abelian₂ → P - Q ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → wpF g.abelian₂ Q ∈ Qbar → wpD g.abelian₂ Q ∈ Qbar → GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) = ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P - Q) = ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  intro p _ g P Q h _ _ hP hQ h1 h2 a1 a2 a3 a4
  obtain ⟨n, e⟩ := xAt_add g P Q h hP hQ h1 h2 a1 a2 a3 a4
  refine ⟨n, e, ?_⟩
  have := (xAt_add g P (-Q) h hP (by simpa using hQ) (by rwa [← sub_eq_add_neg])
    (by rwa [sub_neg_eq_add]) a1 a2 (by rwa [wpF_neg' h])
    (by rw [wpD_neg' h]; exact neg_mem a4)).2
  rwa [← sub_eq_add_neg, xAt_neg g h, yAt_neg g h Q a4] at this

end GlobalTheory.ThetaPar.Chord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelEquationTangentAtLatticeParameter
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.ModelPoint

theorem wpD_sq {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    wpD Λ v ^ 2 = 4 * wpF Λ v ^ 3 - g2 Λ * wpF Λ v - g3 Λ := by
  obtain ⟨w₁, w₂, hi, hΛ⟩ := h
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  rw [GlobalTheory.LatticeInvariants.wpD_eq hL, GlobalTheory.LatticeInvariants.wpF_eq hL,
    GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL]
  exact L.derivWeierstrassP_sq v fun h => hv ((hL v).2 h)

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := dif_pos x.2

theorem lamC_neg_div_four (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) :
    lamC lam (-x / 4) = -lamC lam x / 4 := by
  lift x to Qbar using hx
  have e : (-(x : ℂ) / 4) = ((-x / 4 : Qbar) : ℂ) := by push_cast; rfl
  rw [e, lamC_coe, lamC_coe, map_div₀, map_neg, map_ofNat]

theorem lamC_eqn (lam : Qbar →+* ℂ_[p]) {x y a b : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar)
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (h : y ^ 2 = 4 * x ^ 3 - a * x - b) :
    lamC lam y ^ 2 = 4 * lamC lam x ^ 3 - lamC lam a * lamC lam x - lamC lam b := by
  lift x to Qbar using hx
  lift y to Qbar using hy
  lift a to Qbar using ha
  lift b to Qbar using hb
  have e : y ^ 2 = 4 * x ^ 3 - a * x - b := by
    apply Subtype.ext
    push_cast
    exact h
  have := congrArg lam e
  simpa only [lamC_coe, map_sub, map_mul, map_pow, map_ofNat] using this

theorem model_point : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → wpD g.abelian₂ v ∈ Qbar → g.W.toAffine.Equation (GlobalTheory.EvenTheta.xAt g v) (GlobalTheory.ThetaPar.yAt g v) ∧ 2 * GlobalTheory.ThetaPar.yAt g v + g.W.a₁ * GlobalTheory.EvenTheta.xAt g v + g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * lamC g.lam (wpD g.abelian₂ v) := by
  intro p _ g v hL h2 h3 hv hx hy
  have key := lamC_eqn g.lam hx hy h2 h3 (wpD_sq hL hv)
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt,
      lamC_neg_div_four g.lam h2, lamC_neg_div_four g.lam h3]
    linear_combination ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 / 4 * key
  · simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₃, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt]
    ring

end GlobalTheory.ThetaPar.ModelPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelTangentLawAtDouble
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ModelDouble

open WeierstrassCurve

theorem weierstrassP_two_mul (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) (h2 : 2 * P ∉ L.lattice) :
    L.derivWeierstrassP P ≠ 0 ∧
      L.weierstrassP (2 * P) =
        ((3 * L.weierstrassP P ^ 2 - L.g₂ / 4) / L.derivWeierstrassP P) ^ 2 - 2 * L.weierstrassP P := by
  have hPP : P + P ∉ L.lattice := by rwa [← two_mul]
  have hd : L.derivWeierstrassP P ≠ 0 := (GlobalTheory.derivWeierstrassP_eq_zero_iff L hP).not.mpr hPP
  refine ⟨hd, ?_⟩
  have h := GlobalTheory.latticePoint_add L P P
  have hy : L.derivWeierstrassP P / 2 ≠
      (GlobalTheory.latticeCurve L).toAffine.negY (L.weierstrassP P) (L.derivWeierstrassP P / 2) := by
    simp only [Affine.negY, GlobalTheory.latticeCurve]
    intro e; apply hd; linear_combination e
  rw [GlobalTheory.latticePoint_of_notMem L hP, GlobalTheory.latticePoint_of_notMem L hPP,
    Affine.Point.add_of_Y_ne hy, Affine.Point.some.injEq] at h
  rw [two_mul, h.1, Affine.slope_of_Y_ne rfl hy]
  simp only [Affine.addX, Affine.negY, GlobalTheory.latticeCurve]
  rw [show L.derivWeierstrassP P / 2 - (-(L.derivWeierstrassP P / 2) - 0 * L.weierstrassP P - 0) = L.derivWeierstrassP P by ring]
  field_simp
  ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : Qbar} (hx : x ≠ 0) : lam x ≠ 0 :=
  (map_ne_zero lam).mpr hx

theorem tangent_law : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → 2 * P ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → 2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃ ≠ 0 ∧ GlobalTheory.EvenTheta.xAt g (2 * P) = ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) ^ 2 + g.W.a₁ * ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) - g.W.a₂ - 2 * GlobalTheory.EvenTheta.xAt g P := by
  intro p _ g P hlat hg2 _ hP h2P hwF hwD
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair _ hlat
  obtain ⟨hd, hdup⟩ := weierstrassP_two_mul L ((hL P).not.mp hP) ((hL _).not.mp h2P)
  simp only [← GlobalTheory.LatticeInvariants.wpF_eq hL, ← GlobalTheory.LatticeInvariants.wpD_eq hL,
    ← GlobalTheory.LatticeInvariants.g2_eq hL] at hd hdup
  set a : Qbar := ⟨wpF g.abelian₂ P, hwF⟩ with ha
  set d : Qbar := ⟨wpD g.abelian₂ P, hwD⟩ with hd'
  set G : Qbar := ⟨g2 g.abelian₂, hg2⟩ with hG
  have hd0 : d ≠ 0 := fun h => hd (congrArg Subtype.val h)
  have he : wpF g.abelian₂ (2 * P) = (((((3 * a ^ 2 - G / 4) / d) ^ 2 - 2 * a : Qbar)) : ℂ) := by
    rw [hdup]; simp [a, d, G]; norm_cast
  have lX : lamC g.lam (wpF g.abelian₂ P) = g.lam a := lamC_coe _ a
  have lD : lamC g.lam (wpD g.abelian₂ P) = g.lam d := lamC_coe _ d
  have l2 : lamC g.lam (wpF g.abelian₂ (2 * P)) = ((3 * g.lam a ^ 2 - g.lam G / 4) / g.lam d) ^ 2 - 2 * g.lam a := by
    rw [he, lamC_coe]; simp [map_div₀, map_ofNat]
  have lA : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam G) / 4 := by
    rw [show -(g2 g.abelian₂) / 4 = ((-G / 4 : Qbar) : ℂ) by simp [G]; norm_cast, lamC_coe]; simp [map_div₀, map_ofNat]
  have lD0 : g.lam d ≠ 0 := lamC_ne_zero _ hd0
  have ε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  simp only [GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt, GL3Theta.G1.W, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, wModel, lX, lD, l2, lA]
  set ε := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])
  set X := g.lam a
  set D := g.lam d
  have hden : 2 * (ε ^ 3 * (D / 2 - g.C.s * (X - g.C.r) - g.C.t)) + ε * (0 + 2 * g.C.s) * (ε ^ 2 * (X - g.C.r)) +
      ε ^ 3 * (0 + g.C.r * 0 + 2 * g.C.t) = ε ^ 3 * D := by ring
  rw [hden]
  refine ⟨mul_ne_zero (pow_ne_zero _ ε0) lD0, ?_⟩
  field_simp
  ring

end GlobalTheory.ModelDouble
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeDerivWeierstrassPParameterSeriesBouStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  first | exact @GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | exact GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | (intros; apply GlobalTheory.ThetaTransl.CubeSer.sqThD_atU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPairCoordinatesConjugateBoundStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPair_coordinates_conjugate_bound : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  first | exact @GlobalTheory.NormSum.CoordConj.coord_conj_le | exact GlobalTheory.NormSum.CoordConj.coord_conj_le | (intros; apply GlobalTheory.NormSum.CoordConj.coord_conj_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatioStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication : ∀ D : D7, useAlg D := by
  first | exact @GlobalTheory.ThetaAlgebraic.taylor_algebraic | exact GlobalTheory.ThetaAlgebraic.taylor_algebraic | (intros; apply GlobalTheory.ThetaAlgebraic.taylor_algebraic <;> assumption)
end

