import Formalism.HermitianCurvature.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0026
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0044
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0101
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0060
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordKeyIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RttUpperRelationsFromDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0073
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0084
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0100
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerAveragingInputOfSliceData
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6 Formalism.FourierDecayAlt.DensityAveraging Formalism.FourierDecayAlt.OrbitalSlices

theorem norm_eq_of_pow_eq_same {s : ℕ} (hs : 0 < s) {a z z₀ : ℂ} (hz : z ^ s = a) (hz₀ : z₀ ^ s = a) : ‖z‖ = ‖z₀‖ := by
  have h : ‖z‖ ^ s = ‖z₀‖ ^ s := by rw [← norm_pow, ← norm_pow, hz, hz₀]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hs.ne').mp h

theorem mem_rootSet_iff_pow_eq {s : ℕ} (hs : 0 < s) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by
  rw [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots hs]

theorem germ_leading_term_root_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Ψ : G.Mat (m + 1 + 1) → V) (t Dd z₀ : ℂ) (hz₀ : z₀ ^ (m + 2) = (-1) ^ (m + 3) * Dd) :
    G.mainTerm β m (fun _ => 1) Ψ t Dd =
      (((m : ℂ) + 2)⁻¹ * ((‖z₀‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ)) •
        ∑ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dd), G.psi β (((m : ℂ) + 2) * z / t) • G.OmLong β (m + 1) Ψ z := by
  unfold G.mainTerm
  rw [mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [mem_rootSet_iff_pow_eq (by omega)] at hz
  rw [norm_eq_of_pow_eq_same (by omega) hz hz₀, mul_one, mul_smul]

def germDecayRateAt (C₁ C₂ : ℕ) : Prop :=
  ∀ (m : ℕ) (β : ℂ), β ≠ 0 → ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∃ Cst : ℝ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
      (Φ : G.Mat (m + 1 + 1) → V) (A K : ℝ) (k : ℕ),
      (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ A → C₂ * (m + 2) ^ 2 ≤ k →
      G.DerivBound k (G.detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t c : ℂ, t ≠ 0 → c * t ^ (m + 1) ∈ Kc → ‖G.remainder β m (fun _ => 1) Φ t c‖ ≤ Cst * K * ‖t‖

theorem averaging_datum_of_slice_point {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {D : B.RealPlaceData k r Wp Wq} {F' : B.Mat k r → (Wq →L[ℂ] Wp)} {γ : B.Mat k r}
    {C₁ C₂ : ℕ} (hR : germDecayRateAt C₁ C₂) (S : SlicePt D F' γ) (hS : S.Good C₁ C₂) :
    ∃ T : AvgDatum D F' γ, MoreBlocks D F' γ → T.GermBound := by
  obtain ⟨A, K, kk, hA, hk, hDec, hL, hDg, hRel⟩ := hS
  unfold SlicePt.Decay at hDec
  unfold SlicePt.OrbitalIntegralLongElement at hL
  unfold SlicePt.OrbitalIntegralDiagonalSlice at hDg
  unfold SlicePt.DiagRel at hRel
  unfold germDecayRateAt at hR
  have hz₀ : S.z₀ ∈ G.rootSet (S.m + 2) ((-1) ^ (S.m + 3) * S.Dd) :=
    (mem_rootSet_iff_pow_eq (by omega)).mpr S.z₀_pow
  let R := G.rootSet (S.m + 2) ((-1) ^ (S.m + 3) * S.Dd)
  let e := R.equivFin
  have hm2 : ((S.m : ℂ) + 2) ≠ 0 := by
    have h : ((S.m + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have hinj : Function.Injective (fun j : Fin R.card => ((S.m : ℂ) + 2) * (e.symm j : ℂ)) := by
    intro i j hij
    exact e.symm.injective.eq_iff.mp (Subtype.ext (mul_left_cancel₀ hm2 hij))
  have htie : ‖G.OmLong S.β (S.m + 1) S.Ψ (e.symm (e ⟨S.z₀, hz₀⟩) : ℂ)‖ = 0 → VanAt D F' γ := by
    intro h0
    rw [e.symm_apply_apply, norm_eq_zero] at h0
    unfold VanAt
    intro O
    rw [hL O]
    exact h0
  refine ⟨⟨Wq →L[ℂ] Wp, normSeminorm ℂ (Wq →L[ℂ] Wp), S.β, S.β_ne, R.card,
    fun j => ((S.m : ℂ) + 2) * (e.symm j : ℂ), hinj, fun j => G.OmLong S.β (S.m + 1) S.Ψ (e.symm j : ℂ),
    e ⟨S.z₀, hz₀⟩, htie⟩, ?_⟩
  · intro hMB
    unfold MoreBlocks at hMB
    unfold AvgDatum.GermBound
    dsimp only
    obtain ⟨Cst, hCst⟩ := hR S.m S.β S.β_ne {S.Dd} isCompact_singleton
      (fun h => S.Dd_ne (Set.mem_singleton_iff.mp h).symm)
    have hz0ne : S.z₀ ≠ 0 := by
      intro h
      have hp := S.z₀_pow
      rw [h, zero_pow (by omega)] at hp
      exact S.Dd_ne (by simpa using hp.symm)
    have hc0 : ((S.m : ℂ) + 2)⁻¹ * ((‖S.z₀‖ ^ ((S.m + 1) ^ 2) : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (inv_ne_zero hm2) (Complex.ofReal_ne_zero.mpr (pow_pos (norm_pos_iff.mpr hz0ne) _).ne')
    refine ⟨Cst * K / ‖((S.m : ℂ) + 2)⁻¹ * ((‖S.z₀‖ ^ ((S.m + 1) ^ 2) : ℝ) : ℂ)‖, 2 / S.δ, fun x hx => ?_⟩
    have hδ := S.δ_pos
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
    have htδ : ‖x⁻¹‖ < S.δ := by
      rw [norm_inv, inv_lt_comm₀ hxpos hδ]
      calc S.δ⁻¹ < 2 / S.δ := by rw [div_eq_mul_inv]; linarith [inv_pos.mpr hδ]
        _ ≤ ‖x‖ := hx
    have hct : S.Dd * x ^ (S.m + 1) * x⁻¹ ^ (S.m + 1) = S.Dd := by
      rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx0), mul_one]
    have hblock : G.OmBlock S.β (S.m + 1) S.Ψ x⁻¹ (S.Dd * x ^ (S.m + 1)) = 0 := by
      obtain ⟨O, hO⟩ := hDg x⁻¹ _ (inv_ne_zero hx0) htδ hct
      obtain ⟨h1, h2, h3⟩ := hRel x⁻¹ _ (inv_ne_zero hx0) htδ hct
      have hv := hMB _ h1 h2 h3
      unfold VanAt at hv
      rw [← hO]
      exact hv O
    have hbound := hCst (Wq →L[ℂ] Wp) S.Ψ A K kk hA hk hDec x⁻¹ (S.Dd * x ^ (S.m + 1)) (inv_ne_zero hx0)
      (by rw [Set.mem_singleton_iff]; exact hct)
    unfold G.remainder at hbound
    rw [hblock, smul_zero, zero_sub, norm_neg, hct, germ_leading_term_root_sum S.β S.m S.Ψ x⁻¹ S.Dd S.z₀ S.z₀_pow,
      norm_smul, norm_inv x] at hbound
    have hsum : (∑ j : Fin R.card, G.psi S.β (((S.m : ℂ) + 2) * (e.symm j : ℂ) * x) •
        G.OmLong S.β (S.m + 1) S.Ψ (e.symm j : ℂ)) =
        ∑ z ∈ R, G.psi S.β (((S.m : ℂ) + 2) * z / x⁻¹) • G.OmLong S.β (S.m + 1) S.Ψ z := by
      rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e.symm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_inv_eq_mul]
    change ‖(_ : Wq →L[ℂ] Wp)‖ ≤ _
    rw [hsum, div_div,
      le_div_iff₀ (mul_pos (norm_pos_iff.mpr hc0) hxpos)]
    have hb2 := mul_le_mul_of_nonneg_right hbound hxpos.le
    rw [mul_assoc (Cst * K), inv_mul_cancel₀ hxpos.ne', mul_one] at hb2
    linarith [hb2]

theorem inner_averaging_input_from_slice : Formalism.FourierDecayAlt.OrbitalSlices.AvgInputJOfSlice := by
  intro hG hJ
  obtain ⟨C₁, C₂, hR⟩ := hG
  obtain ⟨CV₀, hCV⟩ := hJ C₁ C₂
  refine ⟨CV₀, ?_⟩
  intro CV hCV' k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ h1 h2 h3 h4
  obtain ⟨S, hS⟩ := hCV CV hCV' k r Wp Wq D A ε mm F' γ h1 h2 h3 h4
  exact averaging_datum_of_slice_point hR S hS

theorem top_averaging_input_from_slice : Formalism.FourierDecayAlt.OrbitalSlices.AvgInputTopOfSlice := by
  intro hG hT
  obtain ⟨C₁, C₂, hR⟩ := hG
  obtain ⟨CV₀, hCV⟩ := hT C₁ C₂
  refine ⟨CV₀, ?_⟩
  intro CV hCV' k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ h1 h2 h3 h4
  obtain ⟨S, hS⟩ := hCV CV hCV' k r Wp Wq D A ε mm F' γ h1 h2 h3 h4
  exact averaging_datum_of_slice_point hR S hS

theorem inner_averaging_input_of_slice_data (hJ : Formalism.FourierDecayAlt.OrbitalSlices.SliceInputJ) : Formalism.FourierDecayAlt.DensityAveraging.AvgInputJ :=
  inner_averaging_input_from_slice germ_rate hJ

theorem top_averaging_input_of_slice_data (hT : Formalism.FourierDecayAlt.OrbitalSlices.SliceInputTop) : Formalism.FourierDecayAlt.DensityAveraging.AvgInputTop :=
  top_averaging_input_from_slice germ_rate hT

theorem density_lemma_of_slice_data (hJ : Formalism.FourierDecayAlt.OrbitalSlices.SliceInputJ) (hT : Formalism.FourierDecayAlt.OrbitalSlices.SliceInputTop) :
    Formalism.FourierDecayAlt.C6.LemmaDens :=
  density_lemma_of_reductions
    (big_cell_density_of_parts (relevant_trivial_big_cell_of_parts stabilizer_split stabilizer_pairs))
    (inner_density_of_averaging (inner_averaging_input_of_slice_data hJ) averaging_vanishes)
    (top_density_of_averaging (top_averaging_input_of_slice_data hT) averaging_vanishes)

def slicePointInhabited {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) : Formalism.FourierDecayAlt.OrbitalSlices.SlicePt D F' γ where
  m := 0
  β := 1
  β_ne := one_ne_zero
  Dd := -1
  Dd_ne := by norm_num
  z₀ := 1
  z₀_pow := by norm_num
  Ψ := fun _ => 0
  pt := fun _ _ => γ
  δ := 1
  δ_pos := one_pos

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
section
namespace Formalism.FourierDecayAlt.P

theorem jacquet_derivative_formula : Formalism.FourierDecayAlt.JF.JWords :=
  bessel_words_of_domain bessel_integral_domain

theorem invariant_operator_under_jacquet : Formalism.FourierDecayAlt.JF.JTheta :=
  theta_bessel_commute_of_parts jacquet_derivative_formula rewrite_rho_action

theorem jacquet_invariant_operator_ae : Formalism.FourierDecayAlt.JF.RadialPartIntertwines :=
  radial_part_intertwines_of_parts invariant_operator_under_jacquet big_cell_orbit_set

theorem jacquet_smooth_coordinates : Formalism.FourierDecayAlt.JF.JqSmooth :=
  bessel_smooth_of_parts jacquet_derivative_formula big_cell_domain

theorem casimir_under_jacquet_integral : Formalism.FourierDecayAlt.JF.CVUnderInt :=
  capelli_under_integral_of_parts jacquet_derivative_formula capelli_word_sum rewrite_rho_action

theorem casimir_commutes_bessel : Formalism.FourierDecayAlt.Q.BesselCommutes :=
  bessel_capelli_commute_of_parts jacquet_derivative_formula capelli_rho_commute casimir_under_jacquet_integral big_cell_orbit_set
    conjugation_invariance_every_setting Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Formalism.QuantumDeterminants.bessel_unitary_equiv_holds

theorem casimir_eigenvalue_bessel : Formalism.FourierDecayAlt.Q.EigenBessel :=
  eigen_bessel_from_commuting_operators casimir_commutes_bessel matrix_coefficient_linear

theorem right_transfer_upper_levels : Formalism.FourierDecayAlt.Q.RTTUpper :=
  rtt_upper_relations_from_descent chain_descent_relation resSurj_statement capelli_commutation operator_preserves_fusion_forms
    transfer_triples rtt_sandwich rtt_independence leading_term_alt transfer_linear_local

theorem right_transfer_all_levels : Formalism.FourierDecayAlt.Q.RTTLevel :=
  rtt_level_from_upper right_transfer_upper_levels level_transfer level_group_image flag_frame_transfer
    transfer_linear_local

namespace JacquetIntegral

theorem detCore : Formalism.FourierDecayAlt.Q.DetAt fun P => Fin.last P.r :=
  determinant_capelli_from_descent right_transfer_all_levels quantum_determinant_from_rtt determinant_hat right_type_action
    left_type_action operator_preserves_fusion_forms transfer_linear_local

end JacquetIntegral

theorem determinant_identity_all_levels : Formalism.FourierDecayAlt.Q.DetLevel :=
  determinant_level_from_capelli_identity JacquetIntegral.detCore chain_descent_relation restriction_mem family_operators transfer_triples
    operator_preserves_fusion_forms transfer_linear_local transfer_joint_smooth cell_decomposition cells_dense

theorem actual_operators_exist : Formalism.FourierDecayAlt.Q.ActualOpsExist :=
  actual_operators_from_parts operator_preserves_fusion_forms transfer_linear_local transfer_joint_smooth radial_operators

theorem actual_adjointness : Formalism.FourierDecayAlt.Q.ActualAdjoint :=
  actual_adjointness_from_hermitian hermitian_haar_invariance

theorem actual_start : Formalism.FourierDecayAlt.Q.ActualStart :=
  actual_start_from_level_starts right_transfer_all_levels JacquetIntegral.detCore transfer_linear_local

namespace JacquetIntegral

theorem normalFormActual_of_fromModule (h : Formalism.FourierDecayAlt.Q.NormalFormFromModule) : Formalism.FourierDecayAlt.Q.NormalFormActual :=
  h actual_start zeta_commutes leading_term_alt spectral_two_by_two actual_operators_exist

theorem levelStartActual_of_normalForm (h : Formalism.FourierDecayAlt.Q.NormalFormActual) : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  level_start_from_normal_form h actual_start model_is_normal_form interlace_sign_two

theorem levelStartActual_of_fromModule (h : Formalism.FourierDecayAlt.Q.NormalFormFromModule) : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  levelStartActual_of_normalForm (normalFormActual_of_fromModule h)

theorem radAdj_of_open (hE : Formalism.FourierDecayAlt.P.JFxG.Exhaust) (hA : Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC) (hX : Formalism.FourierDecayAlt.B.XiExists) :
    Formalism.FourierDecayAlt.JF.RadAdj :=
  jf_radAdj_of_parts3 hE bessel_integral_domain hA hX

end JacquetIntegral

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.L1QuotientIntegralBound
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem prod_ae {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  obtain ⟨hWs, -, hWc, -⟩ := hW
  obtain ⟨hNs, -, hNc, -⟩ := hN
  have := hWs; have := hNs
  rw [ae_iff]
  have hsub : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r |
      ¬ (Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r)} ⊆
      ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) ∪
        (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) := by
    intro p hp
    by_cases h1 : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z
    · exact Or.inr ⟨Set.mem_univ _, fun h2 => hp ⟨h1, h2⟩⟩
    · exact Or.inl ⟨h1, Set.mem_univ _⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hWc, zero_mul]
  · rw [Measure.prod_prod, hNc, mul_zero]

theorem beInt_norm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r) :
    ‖beInt z c π σ (σ g x) v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ := by
  have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hσ : σ (Matrix.of p.1 * Matrix.of p.2 * g) x = σ (Matrix.of p.1 * Matrix.of p.2) (σ g x) := by
    rw [sigma_mul' hds hhn hg]; rfl
  have hi := (MatrixMultiplicationContinuity.uw_inv hp.1).1
  have hπn : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun w => by rw [MatrixMultiplicationContinuity.piW_unitary hT hπ _ hi w, one_mul])
  have hψ : ‖star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))‖ = 1 := by
    rw [norm_star]; unfold Formalism.QuantumDeterminants.psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  unfold beInt
  rw [norm_smul, norm_mul, hψ, mul_one, hσ]
  exact mul_le_of_le_one_right (norm_nonneg _) hπn

theorem be_enorm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖be z c π σ μW μN (σ g x) v‖ₑ ≤
      ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
  unfold be
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [prod_ae hW hN] with p hp
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (beInt_norm_le hds hT hπ hg hp)

theorem l1_quotient_integral_bound {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hGm : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {x v : H} {C a : ℝ}
    (hC : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪v, σ y x⟫_ℂ‖ ≤ C * B.gN y ^ (-a))
    (hI : Integrable (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y) ^ (-a)) μG) :
    ∫⁻ g, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) ∂νq < ⊤ := by
  obtain ⟨e, he, hee⟩ := coef_ext hds v x
  set U : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
  set f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := U.indicator (fun y => ‖e (Matrix.of y)‖ₑ) with hf
  have hfm : Measurable f := by
    have hc : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of y)) :=
      he.comp (show Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) from continuous_id)
    have : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r => ‖e (Matrix.of y)‖ₑ) := hc.measurable.enorm
    exact this.indicator uh_mem_measurableSet
  have hφ : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
    exact h1.matrix_mul h2
  have hmul : ∀ g : Formalism.QuantumDeterminants.Mt k r, Measurable (fun s : Formalism.QuantumDeterminants.Mt k r =>
      f (fun i j => (Matrix.of s * Matrix.of g) i j)) := by
    intro g
    have : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of s * Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r)) := by
      have h1 : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (Matrix.of s : Mx k r)) := continuous_id
      exact h1.matrix_mul continuous_const
    exact hfm.comp this.measurable
  have hfacts := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hfacts.1 hfacts.2 hq

  have step1 : ∀ᵐ g ∂νq, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) =
      ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of g) i j) ∂(muSof μW μN) := by
    filter_upwards [hae] with g hg
    unfold muSof
    rw [lintegral_map (hmul g) hφ.measurable]
    apply lintegral_congr_ae
    filter_upwards [prod_ae hW hN] with p hp
    have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hin : Matrix.of p.1 * Matrix.of p.2 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      DDSmoothness.uh_mul hhn hg
    have key : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) *
        Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r) ∈ U := hin
    show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ =
      f (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of g) i j)
    rw [hf, Set.indicator_of_mem key]
    show _ = ‖e (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g)‖ₑ
    rw [hee _ hin]
  rw [lintegral_congr_ae step1, ← hq f hfm]

  have hb : ∀ᵐ y ∂μG, f y ≤ ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ := by
    have hGc : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
      rw [ae_iff]; simpa using hGm.2.2.1
    filter_upwards [hGc] with y hy
    simp only [hf]
    rw [Set.indicator_of_mem (show y ∈ U from hy), hee _ hy, ← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hC _ hy).trans (le_abs_self _) |>.trans (le_of_eq (Real.norm_eq_abs _).symm))
  calc ∫⁻ y, f y ∂μG ≤ ∫⁻ y, ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ ∂μG := lintegral_mono_ae hb
    _ < ⊤ := (hI.const_mul C).hasFiniteIntegral

end Formalism.FourierDecayAlt.P.S3dx4
end
end

