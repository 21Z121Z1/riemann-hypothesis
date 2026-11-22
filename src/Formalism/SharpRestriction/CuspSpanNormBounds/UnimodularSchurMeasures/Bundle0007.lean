import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0006
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0001

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnMeasurableSetReg
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cn_measurableSet_Reg (a : ℕ) : MeasurableSet (cn_Reg a) := by
  have h : cn_Reg a = (⋂ x : Fin a, ⋂ y : Fin a, ⋂ _ : x < y, {t : Fin a → ℝ | t x < t y}) ∩
      ⋂ x : Fin a, ({t : Fin a → ℝ | 0 < t x} ∩ {t | t x < 1 / 2}) := by
    ext t
    simp only [cn_Reg, StrictMono, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_pi_apply x) (measurable_pi_apply y)
  · exact MeasurableSet.iInter fun x => (measurableSet_lt measurable_const (measurable_pi_apply x)).inter
      (measurableSet_lt (measurable_pi_apply x) measurable_const)

theorem cn_measurable_la {a : ℕ} (r : cn_Root a) : Measurable fun t : Fin a → ℝ => cn_la t r := by
  rcases r with (p | p) | (x | x)
  · exact (measurable_pi_apply p.1.1).div (measurable_pi_apply p.1.2)
  · exact (measurable_pi_apply p.1.1).mul (measurable_pi_apply p.1.2)
  · exact (measurable_pi_apply x).pow_const 2
  · exact measurable_pi_apply x

theorem cn_measurable_cnt {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (de : ℝ) : Measurable (cn_cnt j n0 f de) := by
  unfold cn_cnt
  exact Finset.measurable_prod _ fun r _ => ((measurable_const.div (cn_measurable_la r)).const_add 1).pow_const _

def cn_wt {a : ℕ} (j : Fin a → ℕ) (f : ℕ) (t : Fin a → ℝ) : ℝ := ∏ x, (2 * (f : ℝ) * j x / t x)

namespace CSize

variable {X : CData} (S : CSize X)

def Density : Prop :=
  ∀ (J : ℕ) (c : Composition J), 1 ≤ J → J ≤ X.qq → ∀ Ψ : (Fin c.length → ℝ) → ℝ≥0∞, Measurable Ψ →
    ∫⁻ x in S.str J c, Ψ (S.tau J c x) ∂X.μ ≤
      ENNReal.ofReal (X.I.vol X.μf X.fund * S.kap J c) *
        ∫⁻ t in cn_Reg c.length, Ψ t * ENNReal.ofReal
          (cn_dens c.blocksFun (X.I.n - 2 * J) X.I.f t * cn_wt c.blocksFun X.I.f t)

def NearCount (εN δ : ℝ) : Prop :=
  (∀ x ∈ S.I0, ∀ γ : X.I.GFset, γ ≠ X.one' → (∀ v, X.dist x γ v ≤ εN) → X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0) ∧
    ∀ (J : ℕ) (c : Composition J), ∀ x ∈ S.str J c, ∀ T : Finset X.I.GFset,
      (∀ γ ∈ T, (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) →
      (T.card : ℝ) ≤ cn_cnt c.blocksFun (X.I.n - 2 * J) X.I.f δ (S.tau J c x)

end CSize

theorem cn_norm_φ_le (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (y : X.I.GA) :
    ‖X.φ y‖ ≤ fdegAll X.I X.σ X.w * (X.e 1).re := by
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  have he : ‖X.e y.2‖ ≤ (X.e 1).re := Formalism.HermitianLatticeCounting.Final.S7.posTypeBound X.I.Gf X.e (positive_type_notation_eq X.I hp) y.2
  have hm : ∀ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖ ≤ 1 := by
    intro v
    have hU : IsURepOn (UJset (X.I.ε v)) (X.σ v) := (hX.2.1.1 v).2.2.1
    have hw : ‖X.w v‖ = 1 := (hX.2.1.2.1 v).1
    unfold coefOn
    refine le_trans (norm_inner_le_norm _ _) ?_
    rw [hU.2.1 _ (y.1 v).2, hw]
    norm_num
  unfold CData.φ phe phOf
  rw [norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg X.fdegAll_nonneg]
  have h1 : ∏ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖ ≤ 1 :=
    Finset.prod_le_one (fun v _ => norm_nonneg _) fun v _ => hm v
  have h2 := X.fdegAll_nonneg
  have h3 : 0 ≤ ∏ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖ := Finset.prod_nonneg fun v _ => norm_nonneg _
  calc fdegAll X.I X.σ X.w * (∏ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖) * ‖X.e y.2‖
      ≤ fdegAll X.I X.σ X.w * 1 * (X.e 1).re := by gcongr
    _ = _ := by ring

open Classical in

theorem cn_nearS_le (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (εN : ℝ) (x : X.I.GA) (N : ℝ)
    (hN : ∀ T : Finset X.I.GFset,
      (∀ γ ∈ T, (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) → (T.card : ℝ) ≤ N) :
    X.nearS εN x ≤ ENNReal.ofReal (fdegAll X.I X.σ X.w * (X.e 1).re) * ENNReal.ofReal N := by
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  set k0 : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hk0
  have hk0n : 0 ≤ k0 := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  unfold CData.nearS
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set T := s.filter (fun γ => (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) with hT
  have hterm : ∀ γ ∈ s, (if γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN then ‖X.φ (x⁻¹ * (γ : X.I.GA) * x)‖ₑ else 0) ≤
      (if (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 then
        ENNReal.ofReal k0 else 0) := by
    intro γ _
    by_cases hP : γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN
    · by_cases h0 : X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0
      · simp [h0]
      · rw [if_pos hP, if_pos ⟨hP, h0⟩, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (cn_norm_φ_le X hX _)
    · rw [if_neg hP]
      exact zero_le
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_right ?_ _
  have := hN T fun γ hγ => (Finset.mem_filter.1 hγ).2
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal this

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndRefine
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (P0 b1 Ydat)

theorem cnd_refine (C : ℝ) (hC : 1 ≤ C) (n q f : ℕ) (hq : 1 ≤ q) (hf : 1 ≤ f)
    (rd g b τ₁ D volK Kxx : ℝ) (hrd : 1 ≤ rd) (hg : 1 ≤ g) (hτ : 0 < τ₁) (hτ2 : τ₁ < 1 / 2) (hD : 0 ≤ D)
    (hvK : 0 < volK) (a : ℕ) (τ : ℕ → ℝ) (ha : 1 ≤ a) (haq : a ≤ q) (hpos : ∀ i, 0 < τ i)
    (htop : τ (a + 1) = 1 / 2) (h1 : τ 1 = τ₁)
    (H : ∀ b' : ℕ, 1 ≤ b' → b' ≤ a → ∃ (ρ : ℝ) (s : ℕ → ℝ) (mult : ℝ), 0 ≤ ρ ∧
      ρ ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (τ b' / τ (b' + 1)) ∧ (∀ P, 0 ≤ s P) ∧ Kxx ≤ s 0 ^ 2 ∧
      (∀ P < P0 n q f, s P ≤ ρ * Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) * (C * (n : ℝ) * (b ^ 2 + (P : ℝ) * (n : ℝ))) * s (P + 1)) ∧
      s (P0 n q f) ^ 2 ≤ (4 / (1 / (C * (n : ℝ) * b1 n q f b))) ^ (n ^ 2 * f) * mult * (D / volK) ∧
      mult ≤ (C * Real.sqrt (n : ℝ) / τ₁ ^ 2) ^ (2 * n ^ 2 * f)) :
    ∃ ρ Bs : ℝ, 0 ≤ ρ ∧ ρ ≤ (4 * C) * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) ∧
      Kxx ≤ ((4 * C) * ρ * (n : ℝ) ^ 2 * (f : ℝ) * b1 n q f b) ^ (2 * P0 n q f) * Bs ∧
      Bs ≤ D * volK⁻¹ * ((4 * C) * (n : ℝ) ^ 2 * b1 n q f b) ^ (n ^ 2 * f) * ((4 * C) / τ₁) ^ (4 * n ^ 2 * f) := by
  obtain ⟨b', hb1, hb2, hr⟩ := Formalism.HermitianLatticeCounting.Final.S7.gapPigeonhole a q τ ha haq hpos htop (h1 ▸ hτ2)
  obtain ⟨ρ, s, mult, h0, hρ, hs, hK, hstep, hB, hm⟩ := H b' hb1 hb2
  rw [h1] at hr
  have hC0 : 0 ≤ C := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hrd0 : 0 ≤ rd := by linarith
  have hfR : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hb₁ : 0 ≤ b1 n q f b := by
    unfold Formalism.HermitianLatticeCounting.S7.b1
    positivity
  refine ⟨ρ, s (P0 n q f) ^ 2, h0, ?_, ?_, ?_⟩
  · have hco : 0 ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd := by positivity
    have hpw : 0 ≤ (2 * τ₁) ^ (1 / (q : ℝ)) := Real.rpow_nonneg (by linarith) _
    calc ρ ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (τ b' / τ (b' + 1)) := hρ
      _ ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) := mul_le_mul_of_nonneg_left hr hco
      _ ≤ (4 * C) * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) := by
          have : 0 ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) := mul_nonneg hco hpw
          nlinarith
  · have hsq : Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) ≤ (n : ℝ) * (f : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : (n : ℝ) ^ 2 * (f : ℝ) * 1 ≤ (n : ℝ) ^ 2 * (f : ℝ) * (f : ℝ) :=
        mul_le_mul_of_nonneg_left hfR (by positivity)
      nlinarith
    have hsq0 : 0 ≤ Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) := Real.sqrt_nonneg _
    set Θ : ℝ := ρ * Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) * (C * (n : ℝ) * b1 n q f b) with hΘ
    have hΘ0 : 0 ≤ Θ := by positivity
    have hit := Formalism.HermitianLatticeCounting.Final.S7.iterSup s
      (fun P => ρ * Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) * (C * (n : ℝ) * (b ^ 2 + (P : ℝ) * (n : ℝ)))) Θ (P0 n q f)
      (fun P hP => ⟨by positivity, by
        have h2 := (Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.stepsRoom n q f P b hq).2 (by omega)
        have hc : 0 ≤ ρ * Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) := by positivity
        have hc2 : 0 ≤ C * (n : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hc2) hc⟩) hs hstep
    have hΘle : Θ ≤ (4 * C) * ρ * (n : ℝ) ^ 2 * (f : ℝ) * b1 n q f b := by
      have e1 : Θ ≤ ρ * ((n : ℝ) * (f : ℝ)) * (C * (n : ℝ) * b1 n q f b) := by
        rw [hΘ]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq h0) (by positivity)
      have e2 : 0 ≤ C * ρ * (n : ℝ) ^ 2 * (f : ℝ) * b1 n q f b := by positivity
      nlinarith
    have hs0 : s 0 ^ 2 ≤ (Θ ^ P0 n q f * s (P0 n q f)) ^ 2 := pow_le_pow_left₀ (hs 0) hit 2
    calc Kxx ≤ s 0 ^ 2 := hK
      _ ≤ (Θ ^ P0 n q f * s (P0 n q f)) ^ 2 := hs0
      _ = Θ ^ (2 * P0 n q f) * s (P0 n q f) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm (P0 n q f) 2]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hΘ0 hΘle _) (by positivity)
  · have hcm := Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.cubeMult C n f (b1 n q f b) τ₁ hC hb₁ hτ
    have hDv : 0 ≤ D / volK := div_nonneg hD hvK.le
    have hfac : 0 ≤ (4 / (1 / (C * (n : ℝ) * b1 n q f b))) ^ (n ^ 2 * f) :=
      pow_nonneg (div_nonneg (by norm_num) (div_nonneg zero_le_one (by positivity))) _
    calc s (P0 n q f) ^ 2 ≤ (4 / (1 / (C * (n : ℝ) * b1 n q f b))) ^ (n ^ 2 * f) * mult * (D / volK) := hB
      _ ≤ (4 / (1 / (C * (n : ℝ) * b1 n q f b))) ^ (n ^ 2 * f) * (C * Real.sqrt (n : ℝ) / τ₁ ^ 2) ^ (2 * n ^ 2 * f) *
            (D / volK) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hfac) hDv
      _ ≤ (4 * C * (n : ℝ) ^ 2 * b1 n q f b) ^ (n ^ 2 * f) * (4 * C / τ₁) ^ (4 * n ^ 2 * f) * (D / volK) :=
          mul_le_mul_of_nonneg_right hcm hDv
      _ = _ := by rw [div_eq_mul_inv]; ring

def CSize.DeepStepsT {X : CData} (S : CSize X) (volK C : ℝ) : Prop :=
  0 < volK ∧ X.I.vol X.μf X.fund / volK ≤ cn_Y X ^ (C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) ∧
    ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
      ∃ (a : ℕ) (τ : ℕ → ℝ), 1 ≤ a ∧ a ≤ X.qq ∧ (∀ i, 0 < τ i) ∧ τ (a + 1) = 1 / 2 ∧ τ 1 = S.tau1 x ∧
        ∀ b' : ℕ, 1 ≤ b' → b' ≤ a → ∃ (ρ : ℝ) (s : ℕ → ℝ) (mult : ℝ), 0 ≤ ρ ∧
          ρ ≤ C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * (X.g : ℝ) * X.I.rd * (τ b' / τ (b' + 1)) ∧ (∀ P, 0 ≤ s P) ∧
          |(X.kerD x).re| ≤ s 0 ^ 2 ∧
          (∀ P < P0 X.I.n X.qq X.I.f, s P ≤ ρ * Real.sqrt ((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) *
            (C * (X.I.n : ℝ) * (X.b ^ 2 + (P : ℝ) * (X.I.n : ℝ))) * s (P + 1)) ∧
          s (P0 X.I.n X.qq X.I.f) ^ 2 ≤ (4 / (1 / (C * (X.I.n : ℝ) * b1 X.I.n X.qq X.I.f X.b))) ^ (X.I.n ^ 2 * X.I.f) * mult *
            (X.Dc / volK) ∧
          mult ≤ (C * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f)

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentIntegrableOfCoeff
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

namespace BData

variable {X : BData}

theorem integral_tr {P : Mat X.k X.r} {ε : Fin (2 * X.r + X.k + 1) → Bool} (hP : IsCayleyU X.k X.r ε P) {c : ℝ≥0∞}
    (hμ : X.μG = c • (Formalism.REAL.muG ε).map (cayleyEmbedding P)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Formalism.QuantumDeterminants.Mt X.k X.r → E) :
    ∫ x, F x ∂X.μG = c.toReal • ∫ g, F (cayleyEmbedding P g) ∂(Formalism.REAL.muG ε) := by
  rw [hμ, integral_smul_measure, (cayleyEmbedding_measurable hP).integral_map]

end BData

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelConditionsIffWithoutRegularRep
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem adelic_unimodular_of_finite_covolume (X : CData) (hd : RegData X) (hV : X.FinVol) : UnimodA X := by
  obtain ⟨hH, hF, -⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  exact rr_right_of_finite (rr_FD_of X.I X.μf X.fund hF) hV

theorem UnimodF_of_UnimodA (X : CData) (h : UnimodA X) : UnimodF X := by
  have : (X.I.muA X.μf).IsMulRightInvariant := h
  refine ⟨fun g => ?_⟩
  set B : Set X.I.Ginf := Set.pi univ fun v => {y : Formalism.REAL.UJ (X.I.ε v) | Formalism.REAL.hsG y ≤ (X.I.n : ℝ) + 1} with hBdef
  have hB : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) B =
      ∏ v, Formalism.REAL.muG (X.I.ε v) {y : Formalism.REAL.UJ (X.I.ε v) | Formalism.REAL.hsG y ≤ (X.I.n : ℝ) + 1} := Measure.pi_pi _ _
  have hB0 : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) B ≠ 0 := by
    rw [hB]
    exact Finset.prod_ne_zero_iff.2 fun v _ => (Formalism.REAL.frobenius_ball_compact_pos_finite (X.I.ε v)).2.1.ne'
  have hBt : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.prod_ne_top fun v _ => (Formalism.REAL.frobenius_ball_compact_pos_finite (X.I.ε v)).2.2.ne
  ext A hA
  rw [Measure.map_apply (measurable_mul_const g) hA]
  have key : (X.I.muA X.μf) ((fun x : X.I.GA => x * ((1 : X.I.Ginf), g)) ⁻¹' (B ×ˢ A)) = (X.I.muA X.μf) (B ×ˢ A) :=
    measure_preimage_mul_right _ _ _
  have e1 : (fun x : X.I.GA => x * ((1 : X.I.Ginf), g)) ⁻¹' (B ×ˢ A) = B ×ˢ ((fun y => y * g) ⁻¹' A) := by
    ext ⟨a, b⟩
    simp
  rw [e1] at key
  unfold AutInst.muA at key
  rw [Measure.prod_prod, Measure.prod_prod] at key
  exact (ENNReal.mul_right_inj hB0 hBt).1 key

theorem regularRep_measurable_of_finite_volume (X : CData) (hd : RegData X) (hV : X.FinVol) : X.RegRep :=
  regularRep_isometric_weaklyMeasurable X hd (adelic_unimodular_of_finite_covolume X hd hV)

def KernelDiagonalVolumeModulusConditions (n₀ : ℕ) (A C cb c₁ A₂ cε C₁ : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.KernelDiag ∧ X.FinVol ∧
    ∃ Mod : Set X.I.GA, MeasurableSet Mod ∧ X.ProbMod c₁ Mod ∧
      X.NearStep (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) c₁ A₂ Mod ∧
      X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) Mod ∧ X.DeepInt (A₂ + 1) Mod

theorem kernel_conditions_iff_without_regular_rep (n₀ : ℕ) (A C cb c₁ A₂ cε C₁ : ℝ) :
    StepsC'' n₀ A C cb c₁ A₂ cε C₁ ↔ KernelDiagonalVolumeModulusConditions n₀ A C cb c₁ A₂ cε C₁ :=
  ⟨fun h X hX => (h X hX).2, fun h X hX =>
    ⟨regularRep_measurable_of_finite_volume X (RegData_of_HypB X hX.1) (h X hX).2.1, h X hX⟩⟩

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfL2UnfoldIdempotent
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def ker2 (X : CData) (x y : X.I.GA) : ℂ := ∑' γ : X.I.GFset, X.φ (x⁻¹ * (γ : X.I.GA) * y)

def KernelL2RowsColumns (X : CData) : Prop := ∀ᵐ x ∂X.μ, MemLp (fun y => ker2 X x y) 2 X.μ

def KerUnfold (X : CData) : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → ∀ f : X.L2, ∀ᵐ x ∂X.μ,
    ((T f : X.L2) : X.I.GA → ℂ) x = ∫ y, ker2 X x y * (f : X.I.GA → ℂ) y ∂X.μ

def KerIdem (X : CData) : Prop :=
  ∀ᵐ x ∂X.μ, Summable (fun γ : X.I.GFset => X.φ (x⁻¹ * (γ : X.I.GA) * x)) ∧
    X.kerD x = ((∫ y, ‖ker2 X x y‖ ^ 2 ∂X.μ : ℝ) : ℂ)

theorem rrk_separable (X : CData) (hH : X.μf.IsHaarMeasure) : SeparableSpace X.L2 := by
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 ((X.I.muA X.μf).restrict X.fund)) := inferInstance
  infer_instance

open Classical in

def rrk_kap (X : CData) (x : X.I.GA) : X.L2 :=
  if h : MemLp (fun y => star (ker2 X x y)) 2 ((X.I.muA X.μf).restrict X.fund) then h.toLp _ else 0

theorem rrk_kap_coe (X : CData) {x : X.I.GA} (h : MemLp (fun y => ker2 X x y) 2 ((X.I.muA X.μf).restrict X.fund)) :
    ((rrk_kap X x : X.L2) : X.I.GA → ℂ) =ᵐ[(X.I.muA X.μf).restrict X.fund] fun y => star (ker2 X x y) := by
  have h' : MemLp (fun y => star (ker2 X x y)) 2 ((X.I.muA X.μf).restrict X.fund) := h.star
  unfold rrk_kap
  rw [dif_pos h']
  exact h'.coeFn_toLp

theorem kernel_diagonal_of_L2_unfold_idempotent (X : CData) (hH : X.μf.IsHaarMeasure) (h1 : KernelL2RowsColumns X) (h2 : KerUnfold X) (h3 : KerIdem X) :
    X.KernelDiag := by
  intro T hT hP N F
  unfold KernelL2RowsColumns CData.μ at h1
  unfold KerUnfold CData.μ at h2
  unfold KerIdem CData.μ at h3
  unfold CData.μ
  have := rrk_separable X hH
  have hκ : ∀ f : X.L2, ∀ᵐ x ∂(X.I.muA X.μf).restrict X.fund, ((T f : X.L2) : X.I.GA → ℂ) x = ⟪rrk_kap X x, f⟫_ℂ := by
    intro f
    filter_upwards [h1, h2 T hT f] with x a1 a2
    rw [a2, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [rrk_kap_coe X a1] with y b1
    rw [b1, RCLike.inner_apply]
    simp [mul_comm]
  have hd := rrk_diag ((X.I.muA X.μf).restrict X.fund) T hP F (rrk_kap X) hκ
  filter_upwards [h1, h3, hd] with x a1 a3 ad
  refine ⟨a3.1, ?_⟩
  rw [a3.2, ← ad]
  congr 1
  have e1 : ((‖rrk_kap X x‖ ^ 2 : ℝ) : ℂ) = ⟪rrk_kap X x, rrk_kap X x⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have e2 : ⟪rrk_kap X x, rrk_kap X x⟫_ℂ = ((∫ y, ‖ker2 X x y‖ ^ 2 ∂(X.I.muA X.μf).restrict X.fund : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [rrk_kap_coe X a1] with y b1
    rw [b1, inner_self_eq_norm_sq_to_K, norm_star]
    norm_cast
  exact_mod_cast (e1.trans e2).symm

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.LeftTranslateSet
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory TopologicalSpace
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

def leftTranslateSet (W : Set G) (x : G) : Set G := (fun z => x⁻¹ * z) ⁻¹' W

theorem pj_sep_T_open {W : Set G} (hW : IsOpen W) (x : G) : IsOpen (leftTranslateSet W x) :=
  hW.preimage (continuous_const.mul continuous_id)

theorem pj_sep_cover (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [SFinite μ] (W : Set G)
    (hW : IsOpen W) (h1 : (1 : G) ∈ W) :
    ∃ S : Set G, S.Countable ∧ ∀ y : G, ∃ x ∈ S, ∃ a ∈ W, ∃ b ∈ W, y * a = x * b := by
  obtain ⟨A, hA⟩ := zorn_subset {A : Set G | A.PairwiseDisjoint (leftTranslateSet W)} (fun c hc hch =>
    ⟨⋃₀ c, (Set.pairwiseDisjoint_sUnion hch.directedOn).2 (fun a ha => hc ha), fun s hs => Set.subset_sUnion_of_mem hs⟩)
  have hAd : A.PairwiseDisjoint (leftTranslateSet W) := hA.prop
  refine ⟨A, ?_, ?_⟩
  · have hc := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) (As := fun x : A => leftTranslateSet W (x : G))
      (fun i => (pj_sep_T_open hW _).measurableSet)
      (fun i j hij => hAd i.2 j.2 (fun h => hij (Subtype.ext h)))
    have hall : {i : A | 0 < μ (leftTranslateSet W (i : G))} = Set.univ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      unfold leftTranslateSet
      rw [measure_preimage_mul]
      exact hW.measure_pos μ ⟨1, h1⟩
    rw [hall] at hc
    exact Set.countable_coe_iff.1 (Set.countable_univ_iff.1 hc)
  · intro y
    by_contra hcon
    push Not at hcon
    have hins : (insert y A).PairwiseDisjoint (leftTranslateSet W) := by
      refine hAd.insert fun x hx _ => ?_
      rw [Set.disjoint_left]
      intro z hz1 hz2
      refine hcon x hx _ hz1 _ hz2 ?_
      group
    have hsub : insert y A ⊆ A := hA.le_of_ge hins (Set.subset_insert y A)
    exact hcon y (hsub (Set.mem_insert y A)) 1 h1 1 h1 rfl

theorem pj_sep_nbhd (U : ℕ → Set G) (hUb : ∀ V ∈ nhds (1 : G), ∃ n, U n ⊆ V) (V : Set G) (hV : V ∈ nhds (1 : G)) :
    ∃ n, ∀ a ∈ U n, ∀ b ∈ U n, a * b⁻¹ ∈ V ∧ a⁻¹ * b ∈ V := by
  have c1 : Filter.Tendsto (fun p : G × G => p.1 * p.2⁻¹) (nhds ((1 : G), (1 : G))) (nhds 1) := by
    have : Continuous (fun p : G × G => p.1 * p.2⁻¹) := continuous_fst.mul continuous_snd.inv
    simpa using this.tendsto ((1 : G), (1 : G))
  have c2 : Filter.Tendsto (fun p : G × G => p.1⁻¹ * p.2) (nhds ((1 : G), (1 : G))) (nhds 1) := by
    have : Continuous (fun p : G × G => p.1⁻¹ * p.2) := continuous_fst.inv.mul continuous_snd
    simpa using this.tendsto ((1 : G), (1 : G))
  have h : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' V ∩ (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' V ∈ nhds ((1 : G), (1 : G)) :=
    Filter.inter_mem (Filter.mem_map.1 (c1 hV)) (Filter.mem_map.1 (c2 hV))
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 h
  obtain ⟨n, hn⟩ := hUb (u ∩ v) (Filter.inter_mem hu hv)
  refine ⟨n, fun a ha b hb => ?_⟩
  exact huv (Set.mk_mem_prod (hn ha).1 (hn hb).2)

theorem pj_sep_second (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [SFinite μ] (U : ℕ → Set G)
    (hUo : ∀ n, IsOpen (U n)) (hU1 : ∀ n, (1 : G) ∈ U n) (hUb : ∀ V ∈ nhds (1 : G), ∃ n, U n ⊆ V) :
    SecondCountableTopology G := by
  choose S hSc hS using fun n => pj_sep_cover μ (U n) (hUo n) (hU1 n)
  set B : Set (Set G) := ⋃ n, ⋃ m, (fun x => leftTranslateSet (U m) x) '' (S n) with hB
  have hBc : B.Countable := Set.countable_iUnion fun n => Set.countable_iUnion fun m => (hSc n).image _
  refine IsTopologicalBasis.secondCountableTopology (b := B) ?_ hBc
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro u hu
    simp only [hB, Set.mem_iUnion, Set.mem_image] at hu
    obtain ⟨n, m, x, -, rfl⟩ := hu
    exact pj_sep_T_open (hUo m) x
  · intro y O hy hO
    have hV : (fun z => y * z) ⁻¹' O ∈ nhds (1 : G) :=
      (hO.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using hy)
    obtain ⟨m, hm⟩ := pj_sep_nbhd U hUb _ hV
    have hV2 : (fun z : G => z⁻¹) ⁻¹' (U m) ∈ nhds (1 : G) :=
      ((hUo m).preimage continuous_inv).mem_nhds (by simpa using hU1 m)
    obtain ⟨n, hn⟩ := pj_sep_nbhd U hUb _ hV2
    obtain ⟨x, hx, a, ha, b, hb, hab⟩ := hS n y
    have hxy : x⁻¹ * y ∈ U m := by
      have h1 := (hn a ha b hb).1
      have h2 : (a * b⁻¹)⁻¹ = x⁻¹ * y := by
        have : y = x * b * a⁻¹ := by rw [← hab]; group
        rw [this]; group
      have h3 : (a * b⁻¹)⁻¹ ∈ U m := h1
      rwa [h2] at h3
    refine ⟨leftTranslateSet (U m) x, ?_, hxy, ?_⟩
    · simp only [hB, Set.mem_iUnion, Set.mem_image]
      exact ⟨n, m, x, hx, rfl⟩
    · intro z hz
      have h1 := (hm _ hxy _ hz).2
      have h2 : y * ((x⁻¹ * y)⁻¹ * (x⁻¹ * z)) = z := by group
      have h3 : y * ((x⁻¹ * y)⁻¹ * (x⁻¹ * z)) ∈ O := h1
      rwa [h2] at h3

end General

theorem pj_sepF (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : SepF X := by
  have : X.μf.IsHaarMeasure := hX.2.1.2.2.2.1
  unfold SepF
  refine pj_sep_second X.μf (fun n => _) (fun n => X.I.topf_open (n + 1) (Nat.succ_le_succ (Nat.zero_le n))) ?_ ?_
  · intro n
    refine ⟨one_mem _, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
    simp
  · intro V hV
    obtain ⟨g, hg, hsub⟩ := X.I.topf_basis V hV
    refine ⟨g - 1, ?_⟩
    have : g - 1 + 1 = g := by omega
    simp only [this]
    exact hsub

end Formalism.MainNotions.LeviCoordinates

end
end

