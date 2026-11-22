import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0062
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172
import Formalism.HermitianCurvature.StatementJCT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
import Formalism.HermitianCurvature.StatementPN
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.FlagUnipotentLattices.Bundle0004
import Formalism.FlagUnipotentLattices.Bundle0006
import Formalism.HermitianCurvature.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0143

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselFunctionalOfSigmaContinuity
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.ThreeDimData

theorem shape_true : Shape :=
  DDSmoothness.shape_of psi_constant schur_hermitian bessel_convergence norm_identity_smooth bessel_function_bound

theorem k_finite_form : KFinForm :=
  DDSmoothness.kFinForm_of psi_constant bessel_convergence bessel_function_bound

theorem zeroCase_true : ZeroCase :=
  UnipotentHaarMeasurability.zeroCase_of bessel_convergence norm_identity_smooth schur_hermitian

theorem zero_case_discrete_series : ZeroCaseDD :=
  UnipotentHaarMeasurability.zeroCaseDD_of bessel_convergence norm_identity_smooth schur_hermitian

theorem discrete_series_form_one : DDFormOne :=
  discrete_series_form_one_reduction psi_constant schur_hermitian norm_inverse_bound growth_spherical_bound
    growth_group_bound double_coset_decomposition bessel_convergence norm_identity_smooth bessel_function_bound shape_true

theorem admissible_atomic_form_one : AtFormAdmOne :=
  admissible_atomic_form_one_reduction schur_hermitian bessel_convergence norm_identity_smooth bessel_function_bound
    shape_true k_finite_form zeroCase_true zero_case_discrete_series

theorem orbit_convergence_discrete_series : OrbConvDD :=
  S3dx4.orbConvDD_of_decDD double_coset_decomposition

theorem bessel_nonzero_l2 : BesselNonvanishingL2 :=
  MatrixMultiplicationContinuity.bessel_nonzero_l2_reduction schur_hermitian norm_inverse_bound growth_spherical_bound growth_group_bound
    double_coset_decomposition bessel_convergence

theorem regularity_and_convergence_bundle : More.PhiReg ∧ More.OOConv ∧ More.QuadConv :=
  regularity_bundle_from_hypotheses schur_hermitian norm_identity_smooth norm_inverse_bound growth_spherical_bound growth_group_bound
    double_coset_decomposition bessel_convergence orbit_convergence_discrete_series

theorem orbit_integral_convergence : More.OOConv := regularity_and_convergence_bundle.2.1

theorem quadratic_convergence : More.QuadConv := regularity_and_convergence_bundle.2.2

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section beta

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem JF_cutF (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (g : Mat k r) :
    JF D (Formalism.FourierDecayAlt.D.cutF D χ F ε) g = ((χ (Gf k r D.z D.z' g / ε) : ℝ) : ℂ) • JF D F g := by
  unfold JF besselJ
  rw [← integral_smul]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p := Formalism.FourierDecayAlt.P.B5.ae_inSS D
  filter_upwards [hae] with p hp
  have e := Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs D hp g
  simp only [sgs] at e
  simp only [Formalism.FourierDecayAlt.D.cutF, e]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem hsVec_smul' [FiniteDimensional ℂ Wq] (a : ℂ) (A : Wq →L[ℂ] Wp) : hsVec (a • A) = a • hsVec A := by
  unfold hsVec; ext i; simp

theorem hsVec_cont' [FiniteDimensional ℂ Wq] : Continuous (hsVec : (Wq →L[ℂ] Wp) → _) := by
  unfold hsVec
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous)

theorem inner_self_real {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem bcWeight_nonneg' (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => pow_nonneg (norm_nonneg _) _)
      (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

theorem beta_cutF [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ) :
    beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε) =
      ∫ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q * χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 *
        ‖hsVec (JF D F (gq D q))‖ ^ 2 : ℝ) : ℂ) := by
  unfold beta betaBig
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [gq]
  rw [JF_cutF, hsVec_smul', inner_smul_left, inner_smul_right, inner_self_real, Complex.conj_ofReal]
  push_cast
  ring

theorem cut_bound {χ : ℝ → ℝ} (hχ : Formalism.FourierDecayAlt.C6.IsCut0 χ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |χ x| ≤ M := by
  obtain ⟨hs, ⟨δ, _, h0⟩, h1⟩ := hχ
  have hc : Continuous χ := hs.continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := δ) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 1, le_trans zero_le_one (le_max_right _ _), fun x => ?_⟩
  by_cases hx : x < δ
  · rw [h0 x hx, abs_zero]; exact le_trans zero_le_one (le_max_right _ _)
  by_cases hx1 : 1 ≤ x
  · rw [h1 x hx1, abs_one]; exact le_max_right _ _
  · have := hM x ⟨not_lt.1 hx, le_of_not_ge hx1⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

end beta

section core

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_cut_limit (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (hχ : Formalism.FourierDecayAlt.C6.IsCut0 χ)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (hA : AB k r ≤ A) (hF : ∀ m : ℕ, InCC A m F) :
    normSq D F ≠ ⊤ ∧
      Tendsto (fun ε => beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (((normSq D F).toReal : ℝ) : ℂ)) := by

  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D A hA
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨c4, hc4⟩ := hF 4
  have hfin : normSq D F ≠ ⊤ := (hC0 F F c4 c4 (hF 5) (hF 5) hc4 hc4).1
  refine ⟨hfin, ?_⟩
  set w : (Fin r → ℂ) × ℂ → ℝ := bcWeight k r (Tz k r D.z) (Tz k r D.z') with hw
  set J : (Fin r → ℂ) × ℂ → _ := fun q => hsVec (JF D F (gq D q)) with hJ
  set h : (Fin r → ℂ) × ℂ → ℝ := fun q => w q * ‖J q‖ ^ 2 with hh
  set μQ : Measure ((Fin r → ℂ) × ℂ) := volume.restrict (Qset D) with hμQ
  have hw0 : ∀ q, 0 ≤ w q := fun q => bcWeight_nonneg' _ _ q
  have hh0 : ∀ q, 0 ≤ h q := fun q => mul_nonneg (hw0 q) (sq_nonneg _)
  have hwQ : ∀ q, q ∉ Qset D → w q = 0 := by
    intro q hq
    have : ¬ 0 < w q := hq
    exact le_antisymm (not_lt.1 this) (hw0 q)

  have hcont : ContinuousOn F (GV k r) := Formalism.FourierDecayAlt.P.B7.jc_cont (hF 4)
  have hJm : AEStronglyMeasurable J μQ := by
    have h1 := Formalism.FourierDecayAlt.P.B7.jc_aesm_J D hcont (1, 1)
    have e : (fun q => Jtau D (1, 1) F (gq D q)) = fun q => JF D F (gq D q) :=
      funext fun q => Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq D F (gq D q)
    rw [e] at h1
    exact hsVec_cont'.comp_aestronglyMeasurable h1
  have hwm : Measurable w := Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _
  have hhm : AEStronglyMeasurable h μQ := hwm.aestronglyMeasurable.mul (hJm.norm.pow 2)

  have hlin : normSq D F = ∫⁻ q, ENNReal.ofReal (h q) ∂μQ := by
    show (∫⁻ q, ENNReal.ofReal (h q)) = _
    rw [hμQ, setLIntegral_eq_of_support_subset]
    intro q hq
    by_contra hn
    apply hq
    simp only [hh, hwQ q hn, zero_mul, ENNReal.ofReal_zero]
  have hhi : Integrable h μQ := by
    refine ⟨hhm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hh0), ← hlin]
    exact lt_top_iff_ne_top.2 hfin
  have hlim : ∫ q, ((h q : ℝ) : ℂ) ∂μQ = (((normSq D F).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hh0) hhm, ← hlin]

  obtain ⟨M, hM0, hM⟩ := cut_bound hχ
  have hχc : Continuous χ := hχ.1.continuous
  have hGc : Continuous fun x : Mt k r => Gf k r D.z D.z' (Matrix.of x) :=
    (Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r D.z D.z').comp continuous_id
  set Fe : ℝ → (Fin r → ℂ) × ℂ → ℂ := fun ε q =>
    ((w q * χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 * ‖J q‖ ^ 2 : ℝ) : ℂ) with hFe
  have hbeta : ∀ ε, beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε) = ∫ q, Fe ε q ∂μQ := by
    intro ε
    rw [beta_cutF, hμQ, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro q hq
    simp only [hFe, hwQ q hq, zero_mul, Complex.ofReal_zero]
  simp_rw [hbeta]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun q => M ^ 2 * h q) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun ε => ?_
    have hχm : AEStronglyMeasurable (fun q => χ (Gf k r D.z D.z' (gq D q) / ε)) μQ := by
      refine (((hχc.comp (hGc.div_const ε)).measurable.comp
        (Formalism.FourierDecayAlt.P.B7.measurable_gqM D)).aestronglyMeasurable).congr ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict D] with q hq
      simp only [Function.comp_apply]
      rw [Formalism.FourierDecayAlt.P.B7.gqM_eq D hq]
      rfl
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((hwm.aestronglyMeasurable.mul (hχm.pow 2)).mul (hJm.norm.pow 2))
  · refine Eventually.of_forall fun ε => ae_of_all _ fun q => ?_
    simp only [hFe, Complex.norm_real, Real.norm_eq_abs]
    have h2 : χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM _) 2
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hw0 q) (sq_nonneg _)) (sq_nonneg _))]
    simp only [hh]
    nlinarith [hw0 q, sq_nonneg ‖J q‖, mul_nonneg (hw0 q) (sq_nonneg ‖J q‖)]
  · exact hhi.const_mul _
  · filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict D] with q hq
    have hG : 0 < Gf k r D.z D.z' (gq D q) := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq).2.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds hG)] with ε hε hle
    simp only [hFe, hh]
    rw [hχ.2.2 _ ((one_le_div (Set.mem_Ioi.mp hε)).mpr hle)]
    push_cast
    ring

end core

theorem AB_le_of_thr (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k)
    (h : 1 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    AB k r ≤ A₀ := by
  unfold AB
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  set x : ℝ := (r : ℝ) + 1 with hx
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (k : ℝ) + r ≤ n := by rw [hn]; linarith
  have h2 : 1 ≤ x := by rw [hx]; linarith
  have h3 : 3 ≤ n := by rw [hn]; linarith
  have h4 : x ≤ x ^ 4 := by
    have : 1 ≤ x ^ 3 := one_le_pow₀ h2
    nlinarith
  have h5 : 2 * n + 1 ≤ n ^ 3 := by nlinarith
  have h6 : 0 ≤ (N : ℝ) * n ^ 2 := mul_nonneg hN (sq_nonneg _)
  calc 2 * ((k : ℝ) + r) * x + 1 ≤ 2 * n * x + 1 := by nlinarith
    _ ≤ x * (2 * n + 1) := by nlinarith
    _ ≤ x * n ^ 3 := by nlinarith
    _ ≤ x ^ 4 * n ^ 3 := by nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 3]
    _ ≤ 1 * x ^ 4 * ((N : ℝ) * n ^ 2 + n ^ 3) := by nlinarith [pow_pos (show (0 : ℝ) < x by linarith) 4]
    _ ≤ A₀ := h

end Formalism.FourierDecayAlt.P.JCTx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem beta_cutoff_limit : Formalism.FourierDecayAlt.JCT.BetaCutLimit := by
  refine ⟨1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hP v
  obtain ⟨_, _, _, hB, _, _, _, _, _, _, hk, hA, _⟩ := hP
  exact Formalism.FourierDecayAlt.P.JCTx2.beta_cut_limit (T v).base χ hB.1 (f v) A₀
    (Formalism.FourierDecayAlt.P.JCTx2.AB_le_of_thr S.G.k S.G.r S.Ntop A₀ hk hA) (fun m => (hB.2 v).2.2.2.2.1 m)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
section
namespace Formalism.FourierDecayAlt.P.NormChainLemmas

open Formalism.FourierDecayAlt.PN Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem exactCores : Formalism.FourierDecayAlt.PN.ExactCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.S4.step4, Formalism.HermitianLatticeCounting.Final.S4.omCount, Formalism.HermitianLatticeCounting.Final.S4.weightedCS,
   Formalism.HermitianLatticeCounting.Final.ExpansionTerms.component_total_sixty_four⟩

theorem loopCores : Formalism.FourierDecayAlt.PN.LoopCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.nonDegSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.single_row_lattice_sum_bound,
   Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gainSqrt, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.lattice_exp_sum_upper_bound, Formalism.FourierDecayAlt.Final.pb_loopsJoint,
   Formalism.FourierDecayAlt.Final.pb_loopsGiveRows⟩

theorem nGChain : Formalism.FourierDecayAlt.PN.NGChain :=
  ⟨exactCores, Formalism.FourierDecayAlt.Final.pn_classSquaresSum, Formalism.FourierDecayAlt.Final.pn_rowFromClasses,
   Formalism.FourierDecayAlt.Final.pn_classCS, Formalism.FourierDecayAlt.Final.pn_firstBracket, Formalism.FourierDecayAlt.Final.pn_secondBracket,
   Formalism.FourierDecayAlt.Final.pn_meanAmpJoint, Formalism.FourierDecayAlt.Final.pn_rowNGAbstract, Formalism.FourierDecayAlt.Final.pn_normBound,
   Formalism.FourierDecayAlt.Final.pn_framePassage, Formalism.FourierDecayAlt.Final.pn_normRe, Formalism.FourierDecayAlt.Final.pn_exponentSum,
   Formalism.FourierDecayAlt.Final.pn_nGNumbers⟩

end Formalism.FourierDecayAlt.P.NormChainLemmas

namespace Formalism.FourierDecayAlt.P

theorem loop_kernels : Formalism.FourierDecayAlt.PN.LoopCores := NormChainLemmas.loopCores

theorem norm_chain : Formalism.FourierDecayAlt.PN.NGChain := NormChainLemmas.nGChain

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizePtG
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt

noncomputable section

def ptG (h' : C.LPt) (m : ℕ) : (ℂ × ℂ) ⊕ ℂ → C.LPt
  | Sum.inl q => h' ++ [(m + 1, q.1), (1, q.2)]
  | Sum.inr z => h' ++ [(m + 2, z)]

def yG {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (Φ : G.Mat (m + 2) → V) :
    (ℂ × ℂ) ⊕ ℂ → V
  | Sum.inl q => ((kapB m : ℝ) : ℂ) • G.OmBlock β (m + 1) Φ q.1 q.2
  | Sum.inr z => ((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong β (m + 1) Φ z

def okG (m : ℕ) (Kc : Set ℂ) : (ℂ × ℂ) ⊕ ℂ → Prop
  | Sum.inl q => q.1 ≠ 0 ∧ q.2 * q.1 ^ (m + 1) ∈ Kc
  | Sum.inr z => ∃ D ∈ Kc, z ^ (m + 2) = (-1) ^ (m + 3) * D

theorem ptSize_ptG (h' : C.LPt) (m : ℕ) (q : (ℂ × ℂ) ⊕ ℂ) : D.ptSize (ptG h' m q) = D.ptSize h' + (m + 2) := by
  cases q <;> simp [ptG, D.ptSize, List.map_append, List.sum_append] <;> omega

def GermPlace : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (sg : ℂ) (w : List C.Letter) (f : B.Mat P0.k P0.r → (Wq →L[ℂ] Wp))
    (χ : ℝ → ℝ) (ε : ℝ) (h' : C.LPt) (m i : ℕ) (hi : i ≤ P0.r) (hsz : D.ptSize h' + (m + 2) = i),
    B.CkOn ⊤ (B.GV P0.k P0.r) f → (∃ R : ℝ, ∀ g ∈ B.GV P0.k P0.r, f g ≠ 0 → B.gN g ≤ R) → C6.IsCut0 χ →
    0 < ε → 2 ≤ P0.k → D.IsLocPt h' (D.ptSize h') →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℂ V) (_ : CompleteSpace V)
      (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : G.Mat (m + 2) → V) (Cp Cst : ℝ),
      0 ≤ Cp ∧ (∀ u, (Bf u u).re ≤ (Cp * ‖u‖) ^ 2) ∧
      (∀ q1 q2, okG m Kc q1 → okG m Kc q2 →
        D.formLev T sg ⟨i, by omega⟩ w
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q1) (by rw [ptSize_ptG, hsz]))
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q2) (by rw [ptSize_ptG, hsz])) =
        Bf (yG U.betaU m Φ q1) (yG U.betaU m Φ q2)) ∧
      ∀ t D : ℂ, t ≠ 0 → D ∈ Kc →
        ‖U.uD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D - U.aD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D‖ ≤
          Cst * ‖t‖

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StepFormCptAllOfStepFormAll
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

theorem herGenC_herGen {i : Fin (P.r + 1)} {Φ : RadSp P.k P.r z z' π π'}
    (h : HerGenC S P z z' π π' L st l0 D i Φ) : HerGen S P z z' π π' L st l0 D i Φ := by
  induction h with
  | jf F Φ hF hΦ => exact HerGen.jf F Φ hF.1 hΦ
  | slice l w a b Φ hw _ ih => exact HerGen.slice l w a b Φ hw ih
  | waveC l w s Wv Wv' a b Φ hw h1 h2 _ ih => exact HerGen.waveC l w s Wv Wv' a b Φ hw h1 h2 ih
  | waveZ w s Wv Wv' a b Φ hw h1 h2 _ ih => exact HerGen.waveZ w s Wv Wv' a b Φ hw h1 h2 ih

theorem herKc_le_herK (i : Fin (P.r + 1)) : herKc S P z z' π π' L st l0 D i ≤ herK S P z z' π π' L st l0 D i :=
  Submodule.span_le.mpr fun _ hΦ => Submodule.subset_span (herGenC_herGen hΦ)

theorem herKc_sliceIn : SliceIn (S := S) P z z' π π' L st (herKc S P z z' π π' L st l0 D) l0 := by
  intro w hw l x hx
  exact inK_act_span (bTl L l w) (fun a b Φ hΦ => Submodule.subset_span (HerGenC.slice l w a b Φ hw hΦ)) x hx

theorem herKc_waveK : WaveK (S := S) P z z' π π' st (herKc S P z z' π π' L st l0 D) l0 := by
  intro w hw l s Wv Wv' hW hW' x hx
  exact inK_act_span (Vw (mkP Wv Wv') s w)
    (fun a b Φ hΦ => Submodule.subset_span (HerGenC.waveC l w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herKc_waveZ (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')) (hW : multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g))) (x : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herKc S P z z' π π' L st l0 D (Fin.last P.r)) x) :
    InK (herKc S P z z' π π' L st l0 D (Fin.last P.r)) (act (Vw (mkP Wv Wv') s w) x) :=
  inK_act_span (Vw (mkP Wv Wv') s w)
    (fun a b Φ hΦ => Submodule.subset_span (HerGenC.waveZ w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herKc_jf (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π')
    (hΦ : IsRadJF P z z' π π' D F Φ) : Φ ∈ herKc S P z z' π π' L st l0 D 0 :=
  Submodule.subset_span (HerGenC.jf F Φ hF hΦ)

end Classes

def HerCptTopAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    herKc S P z z' π π' L st l0 D (Fin.last P.r) ≤ cptSub P.k P.r z z' π π'

def StepFormCptAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herKc S P z z' π π' L st l0 D) l0 ∧
      FormInt S P z z' π π' μ L st l0 (herKc S P z z' π π' L st l0 D)

theorem stepFormCptAll_of_stepFormAll (h : StepFormAll) : StepFormCptAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  obtain ⟨hSD, hFI⟩ := h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  have hle : ∀ i (x : Ix S → RadSp P.k P.r z z' π π'), InK (herKc S P z z' π π' L st l0 D i) x →
      InK (herK S P z z' π π' L st l0 D i) x := fun i x hx a => herKc_le_herK i (hx a)
  exact ⟨fun w hw l x y hx hy c hc => hSD w hw l x y (hle _ x hx) (hle _ y hy) c hc,
    fun w hw i c hc x y hx hy => hFI w hw i c hc x y (hle _ x hx) (hle _ y hy)⟩

theorem thmPActualCpt_of_herClassesCpt (hHer : HerClassesCpt) (hWC : WaveCommQQAll) : ThmPActualCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  obtain ⟨K, hAdj, hTD, hTT, hSl, hSD, hWK, hFS, hCor, hJ⟩ :=
    hHer Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  refine ⟨K, ?_, hSl, hCor, hJ⟩
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hST := stepTwistFromParts (S := S) P z z' π π' X μ L st K l0 hD Formalism.FourierDecayAlt.P.plane_wave_vector_identity
    (waveSiteAll Wp Wq P z z' π π' X L) (hWC Wp Wq P z z' π π' X μ L st l0 hD) hWK
  exact thmPFromStepsAll Wp Wq S P z z' π π' μ L st K l0 hTI hTD hTT hSl hSD hST hFS

theorem herClassesCpt_of_parts (hT : HerCptTopAll) (hSF : StepFormCptAll) : HerClassesCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' _ _
  obtain ⟨hSD, hFI⟩ := hSF Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  set K := herKc S P z z' π π' L st l0 D with hKdef
  haveI : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hAdj : AdjTop (S := S) P z z' π π' μ L st K l0 :=
    adjTop_cpt P z z' π π' X μ L st K l0 hD (hT Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ')
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD
    Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hXK := xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hTD := topDensNonnegOfKappa Wp Wq S P z z' π π' X μ L st l0 K hD hl1 hl2 hXK
  have hCor := integral_formula_of_steps Wp Wq S P z z' π π' μ L st l0 K hTI hTD herKc_sliceIn hSD
    (topDensMeasAll Wp Wq S P z z' π π' μ L st K)
  have hTT := topTwistDensOfZeta Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt Wp Wq S P z z' π π' X μ L st l0 K hD
  have hFS := formSesqOfInt Wp Wq S P z z' π π' μ L st l0 _ hFI
  refine ⟨K, hAdj, hTD, ?_, herKc_sliceIn, hSD, herKc_waveK, hFS, hCor, ?_⟩
  · intro w hw s Wv Wv' hW hW' x y hx hy c hc
    exact ⟨herKc_waveZ w hw s Wv Wv' hW hW' x hx, hTT w hw s Wv Wv' hW hW' x y hx hy c hc⟩
  · intro F ε hε hF hC hG
    obtain ⟨Φ, hΦ⟩ := radJFExists Wp Wq P z z' π π' D F hD.1 hz hz' hπ hπ' ⟨hF, ε, hε, hG⟩
    exact ⟨Φ, herKc_jf F ⟨⟨hF, ε, hε, hG⟩, hC⟩ Φ hΦ, hΦ⟩

theorem thmPActualCpt_of_parts (hT : HerCptTopAll) (hSF : StepFormCptAll) : ThmPActualCpt :=
  thmPActualCpt_of_herClassesCpt (herClassesCpt_of_parts hT hSF) waveCommQQAll

theorem thmPActualCpt_of_top (hT : HerCptTopAll) (hSF : StepFormAll) : ThmPActualCpt :=
  thmPActualCpt_of_parts hT (stepFormCptAll_of_stepFormAll hSF)

theorem thmPActualCpt_of_thmPActual (h : ThmPActual) : ThmPActualCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  obtain ⟨K, h1, h2, h3, h4⟩ := h Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  exact ⟨K, h1, h2, h3, fun F ε hε hF _ hG => h4 F ε hε hF hG⟩

end Formalism.FourierDecayAlt.P5.HerC
end
end

