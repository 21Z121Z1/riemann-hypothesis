import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0078
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BridgeQminor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermFibreKernels
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section propG

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure GermBlockL2 {ι : Type} (μ : Measure ℂ) (Y : Finset ι) (U A : ι × ℂ → ℂ → H) (N : ℂ → ι → ι → ℂ) : Prop where
  memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (U (h, x)) 2 μ
  memA : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (A (h, x)) 2 μ
  sup : ∃ B : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ∫ D, ‖U (h, x) D‖ ^ 2 ∂μ ≤ B
  dom : ∀ h ∈ Y, ∃ ab : ℂ → ℝ, MemLp ab 2 μ ∧ ∀ x : ℂ, x ≠ 0 → ∀ᵐ D ∂μ, ‖A (h, x) D‖ ≤ ab D
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D ∂μ, D ∈ K → ‖U (h, x) D - A (h, x) D‖ ≤ C * ‖x‖⁻¹
  lim : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
    Tendsto (fun x => ∫ D, ⟪A (h, x) D, A (h', x + σ) D⟫_ℂ ∂μ) (cocompact ℂ) (𝓝 (N σ h h'))

theorem eventually_ne_cocompact (c : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ c := by
  filter_upwards [(isCompact_singleton : IsCompact ({c} : Set ℂ)).compl_mem_cocompact] with x hx
  simpa using hx

theorem eventually_rate_cocompact (σ : ℂ) (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in cocompact ℂ, C * ‖x + σ‖⁻¹ ≤ δ := by
  have h0 : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h := h0.eventually_ge_atTop (‖σ‖ + |C| / δ + 1)
  filter_upwards [h] with x hx
  have h1 : |C| / δ + 1 ≤ ‖x + σ‖ := by
    have := norm_sub_norm_le x (-σ)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hpos : 0 < ‖x + σ‖ := lt_of_lt_of_le (by positivity) h1
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  have h2 : |C| = δ * (|C| / δ) := by
    first
    | (field_simp; ring)
    | field_simp
  calc C ≤ |C| := le_abs_self C
    _ = δ * (|C| / δ) := h2
    _ ≤ δ * ‖x + σ‖ := by
        apply mul_le_mul_of_nonneg_left _ hδ.le
        linarith

theorem integral_sq_sub_le {μ : Measure ℂ} {u a : ℂ → H} {ab : ℂ → ℝ} (hu : MemLp u 2 μ) (ha : MemLp a 2 μ)
    (hab : MemLp ab 2 μ) (hd : ∀ᵐ D ∂μ, ‖a D‖ ≤ ab D) :
    ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
  have i1 : Integrable (fun D => ‖u D - a D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hu.sub ha).1).1 (hu.sub ha)
  have i2 : Integrable (fun D => ‖u D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have i3 : Integrable (fun D => ab D ^ 2) μ := (memLp_two_iff_integrable_sq hab.1).1 hab
  calc ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ ∫ D, (2 * ‖u D‖ ^ 2 + 2 * ab D ^ 2) ∂μ := by
        refine integral_mono_ae i1 ((i2.const_mul 2).add (i3.const_mul 2)) ?_
        filter_upwards [hd] with D hD
        have h1 : ‖u D - a D‖ ≤ ‖u D‖ + ‖a D‖ := norm_sub_le _ _
        have h2 : 0 ≤ ‖a D‖ := norm_nonneg _
        have h3 : 0 ≤ ‖u D - a D‖ := norm_nonneg _
        have e1 : ‖u D - a D‖ ^ 2 ≤ (‖u D‖ + ‖a D‖) ^ 2 := pow_le_pow_left₀ h3 h1 2
        have e2 : ‖a D‖ ^ 2 ≤ ab D ^ 2 := pow_le_pow_left₀ h2 hD 2
        nlinarith [sq_nonneg (‖u D‖ - ‖a D‖)]
    _ = 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
        rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul, integral_const_mul]

variable {ι : Type} {μ : Measure ℂ} {Y : Finset ι} {U A : ι × ℂ → ℂ → H} {N : ℂ → ι → ι → ℂ}

theorem GermBlockL2.tendsto_rem [IsFiniteMeasureOnCompacts μ] [NullSingletonClass μ] (hG : GermBlockL2 μ Y U A N)
    {h h' : ι} (hh : h ∈ Y) (hh' : h' ∈ Y) (σ τ : ℂ) :
    Tendsto (fun x => ∫ D, ⟪U (h, x + σ) D - A (h, x + σ) D, A (h', x + τ) D⟫_ℂ ∂μ) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨B, hB⟩ := hG.sup
  obtain ⟨ab, hab, hdom⟩ := hG.dom h' hh'
  obtain ⟨ab0, hab0, hdom0⟩ := hG.dom h hh
  refine tendsto_integral_inner_germ μ (fun x => fun D => U (h, x + σ) D - A (h, x + σ) D)
    (fun x => A (h', x + τ)) ab hab (2 * B + 2 * ∫ D, ab0 D ^ 2 ∂μ) ?_ ?_ ?_
  · filter_upwards [eventually_ne_cocompact (-σ)] with x hx
    have hx' : x + σ ≠ 0 := fun h0 => hx (eq_neg_of_add_eq_zero_left h0)
    have hu := hG.memU h hh _ hx'
    have ha := hG.memA h hh _ hx'
    refine ⟨hu.sub ha, ?_⟩
    have h1 := integral_sq_sub_le hu ha hab0 (hdom0 _ hx')
    have hb := hB h hh _ hx'
    beta_reduce
    linarith
  · filter_upwards [eventually_ne_cocompact (-τ)] with x hx
    exact hdom _ (fun h0 => hx (eq_neg_of_add_eq_zero_left h0))
  · intro K hK hK0 δ hδ
    obtain ⟨C, hC⟩ := hG.germ h hh K hK hK0
    filter_upwards [eventually_ne_cocompact (-σ), eventually_rate_cocompact σ C δ hδ] with x hx hr
    have hx' : x + σ ≠ 0 := fun h0 => hx (eq_neg_of_add_eq_zero_left h0)
    filter_upwards [hC _ hx'] with D hD hDK
    exact (hD hDK).trans hr

theorem GermBlockL2.propG [IsFiniteMeasureOnCompacts μ] [NullSingletonClass μ] (hG : GermBlockL2 μ Y U A N) :
    (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) →
      KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (gramL μ U U) (gramL μ U A) (gramL μ A A)) ∧
    (∃ B' : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖gramL μ A A (h, x) (h, x)‖ ≤ B') ∧
    ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => gramL μ A A (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (N σ h h')) ∧
      Tendsto (fun x => gramL μ U A (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (N σ h h')) ∧
      Tendsto (fun x => conj (gramL μ U A (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (N σ h h')) := by
  refine ⟨fun Xs hXs => blockPSD_gramL μ Y U A hG.memU hG.memA Xs hXs, ?_, ?_⟩
  · choose! ab hab hdom using hG.dom
    refine ⟨∑ h ∈ Y, ∫ D, ab h D ^ 2 ∂μ, fun h hh x hx => ?_⟩
    have hA := hG.memA h hh x hx
    have i1 : Integrable (fun D => ‖A (h, x) D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hA.1).1 hA
    have i2 : Integrable (fun D => ab h D ^ 2) μ :=
      (memLp_two_iff_integrable_sq (hab h hh).1).1 (hab h hh)
    unfold gramL
    calc ‖∫ D, ⟪A (h, x) D, A (h, x) D⟫_ℂ ∂μ‖ ≤ ∫ D, ‖⟪A (h, x) D, A (h, x) D⟫_ℂ‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ = ∫ D, ‖A (h, x) D‖ ^ 2 ∂μ := by
          congr 1
          funext D
          rw [inner_self_eq_norm_sq_to_K]
          simp
      _ ≤ ∫ D, ab h D ^ 2 ∂μ := by
          refine integral_mono_ae i1 i2 ?_
          filter_upwards [hdom h hh x hx] with D hD
          exact pow_le_pow_left₀ (norm_nonneg _) hD 2
      _ ≤ ∑ h ∈ Y, ∫ D, ab h D ^ 2 ∂μ :=
          Finset.single_le_sum (f := fun h => ∫ D, ab h D ^ 2 ∂μ)
            (fun i _ => integral_nonneg fun _ => sq_nonneg _) hh
  · intro h hh h' hh' σ
    refine ⟨hG.lim h hh h' hh' σ, ?_, ?_⟩
    · have h1 := hG.tendsto_rem hh hh' 0 σ
      simp only [add_zero] at h1
      have h2 := h1.add (hG.lim h hh h' hh' σ)
      rw [zero_add] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ne_cocompact 0, eventually_ne_cocompact (-σ)] with x hx hxσ
      have hxσ' : x + σ ≠ 0 := fun h0 => hxσ (eq_neg_of_add_eq_zero_left h0)
      have i1 : Integrable (fun D => ⟪U (h, x) D - A (h, x) D, A (h', x + σ) D⟫_ℂ) μ :=
        integrable_inner_of_memLp ((hG.memU h hh x hx).sub (hG.memA h hh x hx)) (hG.memA h' hh' _ hxσ')
      have ia : Integrable (fun D => ⟪A (h, x) D, A (h', x + σ) D⟫_ℂ) μ :=
        integrable_inner_of_memLp (hG.memA h hh x hx) (hG.memA h' hh' _ hxσ')
      unfold gramL
      rw [← integral_add i1 ia]
      congr 1
      funext D
      rw [inner_sub_left]
      ring
    · have h1 := hG.tendsto_rem hh' hh σ 0
      simp only [add_zero] at h1
      have h1c := (Complex.continuous_conj.tendsto 0).comp h1
      rw [map_zero] at h1c
      have h2 := h1c.add (hG.lim h hh h' hh' σ)
      rw [zero_add] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ne_cocompact 0, eventually_ne_cocompact (-σ)] with x hx hxσ
      have hxσ' : x + σ ≠ 0 := fun h0 => hxσ (eq_neg_of_add_eq_zero_left h0)
      have i1 : Integrable (fun D => ⟪U (h', x + σ) D - A (h', x + σ) D, A (h, x) D⟫_ℂ) μ :=
        integrable_inner_of_memLp ((hG.memU h' hh' _ hxσ').sub (hG.memA h' hh' _ hxσ'))
          (hG.memA h hh x hx)
      have ia : Integrable (fun D => ⟪A (h', x + σ) D, A (h, x) D⟫_ℂ) μ :=
        integrable_inner_of_memLp (hG.memA h' hh' _ hxσ') (hG.memA h hh x hx)
      have hsplit : ∫ D, ⟪U (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ
          = ∫ D, ⟪U (h', x + σ) D - A (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ
            + ∫ D, ⟪A (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ := by
        rw [← integral_add i1 ia]
        congr 1
        funext D
        rw [inner_sub_left]
        ring
      have hswap : (starRingEnd ℂ) (∫ D, ⟪A (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ)
          = ∫ D, ⟪A (h, x) D, A (h', x + σ) D⟫_ℂ ∂μ := by
        rw [← integral_conj]
        congr 1
        funext D
        exact inner_conj_symm _ _
      show (starRingEnd ℂ) (∫ D, ⟪U (h', x + σ) D - A (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ)
          + ∫ D, ⟪A (h, x) D, A (h', x + σ) D⟫_ℂ ∂μ = (starRingEnd ℂ) (gramL μ U A (h', x + σ) (h, x))
      unfold gramL
      rw [hsplit, map_add, hswap]

end propG

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Hpart2EqZeroOfInLie
section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Hinv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (Hsq k r)

theorem lie_inv {X : Mat k r} (hX : inLie k r X) : (Hpk k r)⁻¹ * Xᴴ * Hpk k r = -X := by
  have hX0 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX0
  rw [Hinv, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, Hsq, Matrix.one_mul]

theorem hermPart_eq_self_of_mem_lie {X : Mat k r} (hX : inLie k r X) : hpart1 (Hpk k r) X = X := by
  simp only [hpart1]
  rw [lie_inv hX, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

theorem hpart2_eq_zero_of_inLie {X : Mat k r} (hX : inLie k r X) : hpart2 (Hpk k r) X = 0 := by
  simp only [hpart2]
  rw [lie_inv hX]
  simp

theorem two_I_inv : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
  rw [div_eq_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  linear_combination Complex.I_sq

theorem hp_decomp (Z : Mat k r) : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
  simp only [hpart1, hpart2]
  have e : Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  rw [two_I_inv, smul_smul, e, ← smul_add, sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem hpart1_add' (Z W : Mat k r) : hpart1 (Hpk k r) (Z + W) = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) W := by
  simp only [hpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  rw [← smul_add]
  congr 1
  abel

theorem hpart2_add' (Z W : Mat k r) : hpart2 (Hpk k r) (Z + W) = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) W := by
  simp only [hpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  rw [← smul_add]
  congr 1
  abel

theorem hp1_real (x : ℝ) (Z : Mat k r) : hpart1 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart1 (Hpk k r) Z := by
  have hs : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [hpart1, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub, smul_comm]

theorem hpart2_ofReal_smul (x : ℝ) (Z : Mat k r) : hpart2 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart2 (Hpk k r) Z := by
  have hs : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_add, smul_comm]

theorem hpart1_I_smul (Z : Mat k r) : hpart1 (Hpk k r) (Complex.I • Z) = -hpart2 (Hpk k r) Z := by
  have hs : star Complex.I = -Complex.I := Complex.conj_I
  simp only [hpart1, hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul, two_I_inv]
  simp only [neg_smul, neg_neg, sub_neg_eq_add]
  rw [← smul_add, smul_smul, show (1 / 2 : ℂ) * Complex.I = Complex.I / 2 by ring]

theorem hpart2_I_smul (Z : Mat k r) : hpart2 (Hpk k r) (Complex.I • Z) = hpart1 (Hpk k r) Z := by
  have hs : star Complex.I = -Complex.I := Complex.conj_I
  simp only [hpart1, hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul, two_I_inv]
  have e1 : -(Complex.I / 2) * Complex.I = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  have e2 : -(Complex.I / 2) * -Complex.I = -(1 / 2) := by
    linear_combination (1 / 2 : ℂ) * Complex.I_sq
  rw [smul_add, smul_smul, smul_smul, smul_sub, e1, e2, neg_smul, sub_eq_add_neg]

theorem lie_bracket {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X * Y - Y * X) := by
  have hX0 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hY0 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX0
  have hY' : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY0
  have hX'' : ∀ M : Mat k r, Xᴴ * (Hpk k r * M) = -(Hpk k r * (X * M)) := by
    intro M
    rw [← Matrix.mul_assoc, hX', Matrix.neg_mul, Matrix.mul_assoc]
  have hY'' : ∀ M : Mat k r, Yᴴ * (Hpk k r * M) = -(Hpk k r * (Y * M)) := by
    intro M
    rw [← Matrix.mul_assoc, hY', Matrix.neg_mul, Matrix.mul_assoc]
  show (X * Y - Y * X)ᴴ * Hpk k r + Hpk k r * (X * Y - Y * X) = 0
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, hX', hY', Matrix.mul_neg, hX'', hY'', neg_neg]
  abel

theorem hp_of_parts {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) :
    hpart1 (Hpk k r) (X + Complex.I • Y) = X ∧ hpart2 (Hpk k r) (X + Complex.I • Y) = Y := by
  refine ⟨?_, ?_⟩
  · rw [hpart1_add', hpart1_I_smul, hermPart_eq_self_of_mem_lie hX, hpart2_eq_zero_of_inLie hY, neg_zero, add_zero]
  · rw [hpart2_add', hpart2_I_smul, hpart2_eq_zero_of_inLie hX, hermPart_eq_self_of_mem_lie hY, zero_add]

def Psi (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : E :=
  D (g * hpart1 (Hpk k r) Z) + Complex.I • D (g * hpart2 (Hpk k r) Z)

theorem Psi_add (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z + W) = Psi D g Z + Psi D g W := by
  simp only [Psi, hpart1_add', hpart2_add', Matrix.mul_add, map_add, smul_add]
  abel

theorem D_real (D : Mat k r →L[ℝ] E) (g M : Mat k r) (x : ℝ) : D (g * ((x : ℂ) • M)) = (x : ℂ) • D (g * M) := by
  rw [Matrix.mul_smul]
  exact (map_smul D x (g * M)).trans (Complex.coe_smul x _).symm

theorem Psi_real (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (x : ℝ) : Psi D g ((x : ℂ) • Z) = (x : ℂ) • Psi D g Z := by
  simp only [Psi, hp1_real, hpart2_ofReal_smul, D_real, smul_add]
  rw [smul_comm (x : ℂ) Complex.I]

theorem Psi_I (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : Psi D g (Complex.I • Z) = Complex.I • Psi D g Z := by
  simp only [Psi, hpart1_I_smul, hpart2_I_smul, Matrix.mul_neg, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem Psi_smul (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (c : ℂ) : Psi D g (c • Z) = c • Psi D g Z := by
  have hc := Complex.re_add_im c
  calc Psi D g (c • Z) = Psi D g ((c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z)) := by
        rw [smul_smul, ← add_smul, hc]
    _ = (c.re : ℂ) • Psi D g Z + (c.im : ℂ) • (Complex.I • Psi D g Z) := by
        rw [Psi_add, Psi_real, Psi_real, Psi_I]
    _ = c • Psi D g Z := by
        rw [smul_smul, ← add_smul, hc]

theorem Psi_zero (D : Mat k r →L[ℝ] E) (g : Mat k r) : Psi D g 0 = 0 := by
  simpa using Psi_smul D g 0 0

theorem Psi_sub (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z - W) = Psi D g Z - Psi D g W := by
  rw [sub_eq_add_neg, Psi_add, ← neg_one_smul ℂ W, Psi_smul, neg_one_smul, ← sub_eq_add_neg]

end Formalism.FourierDecayAlt.P.JFxE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section gen

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cptInCC_G {F : Mat k r → E} {C : Set (Mat k r)} (hF : CkOn ⊤ (GV k r) F) (hC : IsCompact C)
    (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) (A : ℝ) (m : ℕ) : InCC A m F := by
  classical
  set F₂ : Mat k r → E := fun g => if g ∈ GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hF₂c : CkOn ⊤ (GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, fun g hg hgG => (he g hgG).trans (hff g hg hgG)⟩
  obtain ⟨c, hc1, hc2⟩ := Formalism.FourierDecayAlt.P.compact_support_finite_class k r E F₂ C hF₂c hC (fun g hg => by
    by_cases hgG : g ∈ GV k r
    · rw [he g hgG]; exact hz g hgG hg
    · simp [hF₂, hgG]) A m
  refine ⟨c, B5.ckOn_mono le_top hF, fun u v hu hv hl g hg => ?_⟩
  have := hc2 u v hu hv hl g hg
  rwa [dLR_eq, W_congr (lr u v) (fun y hy => by
      simp only [lr, List.mem_append, List.mem_map] at hy
      rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1
      · exact (hv X hX).1) he g hg, ← dLR_eq] at this

theorem ckOn_Rw_top {f : Mat k r → E} (h : CkOn ⊤ (GV k r) f) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → CkOn ⊤ (GV k r) (Rw w f) := by
  intro w
  induction w with
  | nil => intro _; exact h
  | cons X w ih =>
    intro hw
    show CkOn ⊤ (GV k r) (RdV X (Rw w f))
    have h1 : CkOn (⊤ + 1) (GV k r) (Rw w f) := by
      rw [top_add]; exact ih fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    exact B5.ckOn_RdV (hw X List.mem_cons_self) h1

end gen

theorem om_stable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) :
    IsStableOpen D (Om k r D.z D.z') := by
  refine ⟨⟨Q.OmPlus k r D.z D.z', PositiveOrbitOpen.omPlus_open D.z D.z', Set.inter_comm _ _⟩, ?_⟩
  intro s hs s' hs' g hg
  refine ⟨BetaSesquilinearity.gv_mul (BetaSesquilinearity.gv_mul (BetaSesquilinearity.Sset_sub hs) hg.1) (BetaSesquilinearity.Sset_sub hs'), fun l hl => ?_, ?_⟩
  · rw [dInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g l]; exact hg.2.1 l hl
  · show 0 < Gf k r D.z D.z' (s * g * s')
    rw [gInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g]; exact hg.2.2

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jf_betaAdjC_of_lemmaBNorm : Formalism.FourierDecayAlt.B2.LemmaBNorm → Formalism.FourierDecayAlt.P.JFxG.BetaAdjC := by
  intro hL k r Wp Wq _ _ _ _ _ _ D Θ F F' hI hS hC hF hF' hFc hF'c
  obtain ⟨C, hCc, hCO, hCF⟩ := hFc
  obtain ⟨C', hC'c, hC'O, hC'F⟩ := hF'c
  have hL3 := (hL k r Wp Wq D (AB k r) le_rfl hI).2.2.1
  have supp : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K → K ⊆ Om k r D.z D.z' →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → closure {g | g ∈ GV k r ∧ φ g ≠ 0} ⊆ Om k r D.z D.z' :=
    fun hK hKO hz => (closure_minimal (fun g hg => by
      by_contra hgK
      exact hg.2 (hz g hg.1 hgK)) hK.isClosed).trans hKO
  have rwz : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → ∀ w : List (Mat k r), (∀ X ∈ w, inLie k r X) →
        ∀ g ∈ GV k r, g ∉ K → Rw w φ g = 0 :=
    fun hK hz w hw g hg hgK => BetaSesquilinearity.Rw_vanish hK.isClosed.isOpen_compl hw (fun x hx hxK => hz x hx hxK) g hg hgK
  have hFz : ∀ g ∈ GV k r, g ∉ C → F g = 0 := fun g _ h => hCF g h
  have hF'z : ∀ g ∈ GV k r, g ∉ C' → F' g = 0 := fun g _ h => hC'F g h
  have hap : ∀ T ∈ Θ, CkOn ⊤ (GV k r) (fun x => T.coefAdj x (F' x)) ∧
      ∀ g ∈ GV k r, g ∉ C' → T.coefAdj g (F' g) = 0 := fun T hT =>
    ⟨B5.ckOn_coef (hS T hT).2 hF' (supp hC'c hC'O hF'z), fun g hg hgK => by rw [hF'z g hg hgK, map_zero]⟩
  have hrev : ∀ T ∈ Θ, ∀ X ∈ T.word.reverse, inLie k r X := fun T _ X hX => T.word_lie X (List.mem_reverse.1 hX)

  have hΘF : InCC (AB k r) 5 (opApply Θ F) := by
    show InCC _ 5 (fun g => (Θ.map fun T => T.coef g (Rw T.word F g)).sum)
    refine BetaSesquilinearity.InCC_opsum Θ (fun T g => T.coef g (Rw T.word F g)) fun T hT => ?_
    exact cptInCC_G (B5.ckOn_coef (hS T hT).1 (ckOn_Rw_top hF T.word T.word_lie)
        (supp hCc hCO (rwz hCc hFz T.word T.word_lie))) hCc
      (fun g hg hgK => by
        show T.coef g (Rw T.word F g) = 0
        rw [rwz hCc hFz T.word T.word_lie g hg hgK, map_zero]) _ 5
  have hΘF' : InCC (AB k r) 5 (opAdj Θ F') := by
    show InCC _ 5 (fun g => (Θ.map fun T =>
      ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g).sum)
    refine BetaSesquilinearity.InCC_opsum Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g)
      fun T hT => ?_
    exact cptInCC_G (B4.ckOn_smul ((-1 : ℂ) ^ T.word.length) (ckOn_Rw_top (hap T hT).1 _ (hrev T hT))) hC'c
      (fun g hg hgK => by
        show ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g = 0
        rw [rwz hC'c (hap T hT).2 _ (hrev T hT) g hg hgK, smul_zero]) _ 5

  have hIC : IntClause D Θ F F' := by
    intro p hp T hT i j hij hj
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (fun x => T.coefAdj x (F' x)) with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hf₁c : CkOn ⊤ (GV k r) f₁ := ckOn_Rw_top (hap T hT).1 _ hlie1
    have hf₁z : ∀ g ∈ GV k r, g ∉ C' → f₁ g = 0 := rwz hC'c (hap T hT).2 _ hlie1
    obtain ⟨K₁, hK₁⟩ := cptInCC_G hf₁c hC'c hf₁z 0 0
    have hb₁ : ∀ g ∈ GV k r, ‖f₁ g‖ ≤ K₁ := by
      intro g hg
      have := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      simpa [Real.rpow_zero, dLR, Rw] using this
    have hf₂c : ContinuousOn f₂ (GV k r) :=
      BetaSesquilinearity.CkOn_cont subset_rfl (B5.ckOn_mono bot_le (ckOn_Rw_top (B5.ckOn_rho D hp hF) _ hlie2))
    have hf₁cont : ContinuousOn f₁ (GV k r) := BetaSesquilinearity.CkOn_cont subset_rfl (B5.ckOn_mono bot_le hf₁c)
    obtain ⟨K₂, hK₂⟩ := (hC'c.inter_right B5.GV_closed).exists_bound_of_continuousOn (hf₂c.mono Set.inter_subset_right)
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hf₂c.norm).smul hf₁cont
    have hGm := BetaSesquilinearity.aesm_of_continuousOn D hGc
    have hfin : D.μG (C' : Set (Mt k r)) ≠ ⊤ := (D.haarG.finite_compact C' hC'c).ne
    have hind : Integrable ((C' : Set (Mt k r)).indicator fun _ => K₁ * K₂) D.μG :=
      (integrableOn_const hfin).integrable_indicator (IsClosed.measurableSet (α := Mt k r) hC'c.isClosed)
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := by
      refine hind.mono' hGm ?_
      filter_upwards [B5.haar_ae D.haarG] with x hx
      by_cases hxC : x ∈ (C' : Set (Mt k r))
      · rw [Set.indicator_of_mem hxC, hGn]
        have h1 := hb₁ (Matrix.of x) hx
        have h2 := hK₂ (Matrix.of x) ⟨hxC, hx⟩
        exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      · rw [Set.indicator_of_notMem hxC, hGn, hf₁z (Matrix.of x) hx hxC, norm_zero, zero_mul]
    exact hint.norm.congr (Filter.Eventually.of_forall fun g => hGn _)
  exact hL3 (Om k r D.z D.z') Θ (om_stable D) hS hC F F' (B5.ckOn_mono le_top hF) (B5.ckOn_mono le_top hF')
    (supp hCc hCO hFz) (supp hC'c hC'O hF'z) (cptInCC_G hF hCc hFz _ 5) (cptInCC_G hF' hC'c hF'z _ 5) hΘF hΘF' hIC

theorem jf_radAdj_of_parts2 : Formalism.FourierDecayAlt.P.JFxG.Exhaust → Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC →
    Formalism.FourierDecayAlt.B2.LemmaBNorm → Formalism.FourierDecayAlt.JF.RadAdj := fun hE hD hA hL =>
  jf_radAdj_of_parts hE hD hA (jf_betaAdjC_of_lemmaBNorm hL)

theorem jf_radAdj_of_parts3 : Formalism.FourierDecayAlt.P.JFxG.Exhaust → Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC →
    Formalism.FourierDecayAlt.B.XiExists → Formalism.FourierDecayAlt.JF.RadAdj := fun hE hD hA hX =>
  jf_radAdj_of_parts2 hE hD hA (Formalism.FourierDecayAlt.P.lemma_b_from_xi hX).1

end Formalism.FourierDecayAlt.P
end
end

