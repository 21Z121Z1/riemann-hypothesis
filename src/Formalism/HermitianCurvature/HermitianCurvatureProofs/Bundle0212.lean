import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0153
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0204
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0202
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0118

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACAsm
section
open MeasureTheory Topology Filter
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gv_isClosed (k r : ℕ) : IsClosed (B.GV k r) := by
  show IsClosed {g : B.Mat k r | Matrix.conjTranspose g * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem sgs_continuousAt_oneP {k r : ℕ} (g : B.Mat k r) :
    ContinuousAt (fun p : B.SS k r => B.sgs p g) oneP := by
  have hinv : ContinuousAt (fun A : B.Mat k r => A⁻¹) 1 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Matrix.det_one]
    exact NormedRing.inverse_continuousAt (1 : ℂˣ)
  have c11 : Continuous fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r) := continuous_fst.comp continuous_fst
  have c12 : Continuous fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r) := continuous_snd.comp continuous_fst
  have c21 : Continuous fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r) := continuous_fst.comp continuous_snd
  have c22 : Continuous fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r) := continuous_snd.comp continuous_snd
  have i1 : ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) oneP :=
    ContinuousAt.comp_of_eq hinv c11.continuousAt rfl
  have i2 : ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) oneP :=
    ContinuousAt.comp_of_eq hinv c12.continuousAt rfl
  show ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * g *
    (Matrix.of p.2.2 : B.Mat k r) * (Matrix.of p.2.1 : B.Mat k r)) oneP
  exact (((i1.mul i2).mul continuousAt_const).mul c22.continuousAt).mul c21.continuousAt

theorem avgCutoff_of_parts (hB : ACBump) (hI : ACInv) (hN : ACInt) (hP : ACHaarPos) (hS : ACSmooth) :
    Formalism.FourierDecayAlt.P.JFxI.AvgCutoff := by
  intro k r Wp Wq _ _ _ _ D K hK hKQ
  obtain ⟨φ₀, hφ₀s, hφ₀n, hφ₀c, hφ₀O, hφ₀K⟩ := hB k r Wp Wq D K hK hKQ
  have hφ₀cont : Continuous φ₀ := hφ₀s.continuous
  set I : B.Mat k r → ℝ := fun g => ∫ p, φ₀ (B.sgs p g) ∂D.μSS with hIdef
  have hgqOm : ∀ q ∈ JF.QDom k r D.z D.z', B.gq D q ∈ JF.Om k r D.z D.z' := fun q hq =>
    Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q hq

  have hposI : ∀ g ∈ JF.Om k r D.z D.z', 0 < φ₀ g → 0 < I g := by
    intro g hg hφg
    have hint := hN k r Wp Wq D φ₀ hφ₀cont hφ₀c g hg
    rw [hIdef]
    refine (integral_pos_iff_support_of_nonneg (fun p => hφ₀n _) hint).2 ?_
    have hca : ContinuousAt (fun p : B.SS k r => φ₀ (B.sgs p g)) oneP :=
      hφ₀cont.continuousAt.comp (sgs_continuousAt_oneP g)
    have hev : ∀ᶠ p in 𝓝 (oneP : B.SS k r), 0 < φ₀ (B.sgs p g) := by
      refine hca.eventually (lt_mem_nhds ?_)
      show 0 < φ₀ (B.sgs oneP g)
      rw [sgs_oneP]; exact hφg
    obtain ⟨O, hOsub, hOo, hO1⟩ := mem_nhds_iff.1 hev
    exact lt_of_lt_of_le (hP k r Wp Wq D O hOo hO1)
      (measure_mono fun p hp => (ne_of_gt (hOsub hp)))

  have hcont : ContinuousOn (fun q => I (B.gq D q)) K := by
    intro q₀ hq₀
    have hq₀D := hKQ hq₀
    obtain ⟨U, I', hUo, hgU, hI'U, hII'⟩ := hS k r Wp Wq D φ₀ hφ₀s hφ₀c hφ₀O _ (hgqOm q₀ hq₀D)
    have hgqc : ContinuousAt (fun q => B.gq D q) q₀ :=
      ((Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn).continuousAt
        ((Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z').mem_nhds hq₀D)
    have hev : (fun q => I (B.gq D q)) =ᶠ[𝓝 q₀] fun q => I' (B.gq D q) := by
      have h1 : ∀ᶠ q in 𝓝 q₀, B.gq D q ∈ U := hgqc.preimage_mem_nhds (hUo.mem_nhds hgU)
      have h2 : ∀ᶠ q in 𝓝 q₀, q ∈ JF.QDom k r D.z D.z' := (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z').mem_nhds hq₀D
      filter_upwards [h1, h2] with q hq1 hq2
      exact hII' _ hq1 (hgqOm q hq2).1
    have hI'c : ContinuousAt I' (B.gq D q₀) := (hI'U.continuousOn).continuousAt (hUo.mem_nhds hgU)
    exact ((ContinuousAt.comp_of_eq hI'c hgqc rfl).congr hev.symm).continuousWithinAt

  obtain ⟨c₀, hc₀, hc₀K⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ q ∈ K, c₀ ≤ I (B.gq D q) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun q hq => by simp [hKe] at hq⟩
    · obtain ⟨q₁, hq₁, hmin⟩ := hK.exists_isMinOn hKne hcont
      exact ⟨I (B.gq D q₁), hposI _ (hgqOm q₁ (hKQ hq₁)) (hφ₀K q₁ hq₁), fun q hq => hmin hq⟩

  set s : ℝ → ℝ := fun t => Real.smoothTransition ((t - c₀ / 2) / (c₀ / 2)) with hsdef
  set σ : ℝ → ℝ := fun t => s t * t + (1 - s t) * (c₀ / 2) with hσdef
  have hc2 : 0 < c₀ / 2 := by linarith
  have hσlb : ∀ t, c₀ / 2 ≤ σ t := by
    intro t
    have h0 : 0 ≤ s t := Real.smoothTransition.nonneg _
    by_cases ht : c₀ / 2 ≤ t
    · show c₀ / 2 ≤ s t * t + (1 - s t) * (c₀ / 2)
      nlinarith
    · have hz : s t = 0 := Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hc2.le)
      show c₀ / 2 ≤ s t * t + (1 - s t) * (c₀ / 2)
      rw [hz]; simp
  have hσpos : ∀ t, σ t ≠ 0 := fun t => (lt_of_lt_of_le hc2 (hσlb t)).ne'
  have hσid : ∀ t, c₀ ≤ t → σ t = t := by
    intro t ht
    have h1 : s t = 1 := Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hc2]; linarith)
    show s t * t + (1 - s t) * (c₀ / 2) = t
    rw [h1]; ring
  have hσs : ContDiff ℝ ∞ σ := by
    have hs : ContDiff ℝ ∞ s :=
      Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    exact (hs.mul contDiff_id).add ((contDiff_const.sub hs).mul contDiff_const)

  classical
  let φ : B.Mat k r → ℂ := fun g => if g ∈ B.GV k r then ((φ₀ g * (σ (I g))⁻¹ : ℝ) : ℂ) else 0
  have hφ0 : ∀ g, g ∉ tsupport φ₀ → φ g = 0 := by
    intro g hg
    have : φ₀ g = 0 := image_eq_zero_of_notMem_tsupport hg
    simp [φ, this]
  refine ⟨φ, ?_, ⟨tsupport φ₀ ∩ B.GV k r, hφ₀c.isCompact.inter_right (gv_isClosed k r),
    fun g hg => ⟨hg.2, hφ₀O hg.1⟩, fun g hg => ?_⟩, ?_⟩
  ·
    intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus k r D.z D.z'
    · obtain ⟨U, I', hUo, hgU, hI'U, hII'⟩ := hS k r Wp Wq D φ₀ hφ₀s hφ₀c hφ₀O g₀ ⟨hg₀, hO⟩
      refine ⟨U, fun g => ((φ₀ g * (σ (I' g))⁻¹ : ℝ) : ℂ), hUo, hgU, ?_, ?_⟩
      · have h1 : ContDiffOn ℝ ∞ (fun g => φ₀ g * (σ (I' g))⁻¹) U :=
          hφ₀s.contDiffOn.mul ((hσs.comp_contDiffOn hI'U).inv fun g _ => hσpos _)
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1
      · intro g hg hgG
        show (if g ∈ B.GV k r then ((φ₀ g * (σ (∫ p, φ₀ (B.sgs p g) ∂D.μSS))⁻¹ : ℝ) : ℂ) else 0) = _
        rw [if_pos hgG, hII' g hg hgG]
    · refine ⟨(tsupport φ₀)ᶜ, fun _ => 0, (isClosed_tsupport _).isOpen_compl, fun h => hO (hφ₀O h),
        contDiffOn_const, fun g hg _ => hφ0 g hg⟩
  ·
    by_cases hgG : g ∈ B.GV k r
    · exact hφ0 g fun h => hg ⟨h, hgG⟩
    · simp [φ, hgG]
  ·
    intro p₀ hp₀ q hq
    have hgq := hgqOm q (hKQ hq)
    have hg := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D hp₀ hgq
    have hIg : I (B.sgs p₀ (B.gq D q)) = I (B.gq D q) := hI k r Wp Wq D φ₀ hφ₀cont p₀ hp₀ _
    have hIpos : 0 < I (B.gq D q) := lt_of_lt_of_le hc₀ (hc₀K q hq)
    have hae : ∀ᵐ p ∂D.μSS, φ (B.sgs p (B.sgs p₀ (B.gq D q))) =
        ((φ₀ (B.sgs p (B.sgs p₀ (B.gq D q))) * (I (B.gq D q))⁻¹ : ℝ) : ℂ) := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
      have hG : B.sgs p (B.sgs p₀ (B.gq D q)) ∈ B.GV k r := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV D hp hg.1
      have hIp : I (B.sgs p (B.sgs p₀ (B.gq D q))) = I (B.gq D q) := by
        rw [← hIg]; exact hI k r Wp Wq D φ₀ hφ₀cont p hp _
      simp only [φ, if_pos hG, hIp, hσid _ (hc₀K q hq)]
    rw [integral_congr_ae hae, integral_complex_ofReal, integral_mul_const]
    change (((I (B.sgs p₀ (B.gq D q))) * (I (B.gq D q))⁻¹ : ℝ) : ℂ) = 1
    rw [hIg, mul_inv_cancel₀ hIpos.ne', Complex.ofReal_one]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACInv
section
open MeasureTheory
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

theorem averaging_invariance_holds : ACInv := by
  intro k r Wp Wq _ _ _ _ D φ₀ _hφ p₀ hp₀ g
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  obtain ⟨h1, h2, h3, h4⟩ := hp₀
  let F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun x => ((φ₀ x : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)
  let π1 : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun _ => 1
  have hpsi : ∀ (w : Fin (2 * r + k + 1) → ℂ) (y : B.Mat k r), psi k r w 0 y = 1 := by
    intro w y; simp [psi]
  have hJ : ∀ x : B.Mat k r, besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F x =
      ((∫ p, φ₀ (B.sgs p x) ∂D.μSS : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
    intro x
    unfold besselJ
    simp only [hpsi, star_one, mul_one, one_smul, π1, F]
    rw [← integral_complex_ofReal, ← integral_smul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ext
    simp [B.sgs]
  have hrep : ∀ U : Set (B.Mat k r), IsCRepOn U π1 := fun U => ⟨rfl, fun _ _ _ _ => by ext; simp [π1]⟩
  have hN := bessel_unipotent_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    (fun n₀ h => D.haarN.left n₀ h)
  have hU := bessel_unitary_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
    (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) (hrep _) (hrep _)
  have hs : B.sgs p₀ g = (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ *
      ((Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r)) * (Matrix.of p₀.2.1 : B.Mat k r) := by
    show (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ * (Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r) *
      (Matrix.of p₀.2.1 : B.Mat k r) = _
    simp only [Matrix.mul_assoc]
  have key : besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F (B.sgs p₀ g) =
      besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F g := by
    rw [hs, hU _ _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1) _ h3, hN _ _ (WeylGroupFacts.mem_n_inv h2) _ h4]
    ext
    simp [π1, hpsi]
  rw [hJ, hJ] at key
  have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) key
  simp at this
  exact_mod_cast this

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACProper
section
open Matrix MeasureTheory Topology
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem averaging_properness_holds : ACProper := by
  intro k r Wp Wq _ _ _ _ D C C' hC hC' hC'O
  have hW : IsCompact (UWset k r D.z) := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos
  have hW' : IsCompact (UWset k r D.z') := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos
  have hgc : Continuous (B.gN : B.Mat k r → ℝ) := Formalism.FourierDecayAlt.P.B6.gN_continuous
  obtain ⟨MW, hMW⟩ := hW.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MW', hMW'⟩ := hW'.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MC, hMC⟩ := hC.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨Co, hCo0, hCo⟩ := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.orbit D.z D.z' C' hC' hC'O
  have gN_nn : ∀ M : B.Mat k r, 0 ≤ B.gN M := fun M => Real.sqrt_nonneg _
  have bnd : ∀ {s : Set (B.Mat k r)} {M : ℝ}, (∀ x ∈ s, ‖B.gN x‖ ≤ M) → ∀ x ∈ s, B.gN x ≤ M :=
    fun h x hx => (le_abs_self _).trans (h x hx)
  set Bd : ℝ := max MW 0 * max MC 0 * max MW' 0 with hBd
  set R : ℝ := max (max MW MW') (Co * Bd ^ (2 * r + 1)) with hR
  refine ⟨Metric.closedBall 0 (max R 0), isCompact_closedBall _ _, ?_⟩
  intro p hp g hg hsg
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  set h : B.Mat k r := Matrix.of p.1.1
  set n : B.Mat k r := Matrix.of p.1.2
  set h' : B.Mat k r := Matrix.of p.2.1
  set n' : B.Mat k r := Matrix.of p.2.2
  have hdet : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hdet' : IsUnit h'.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1
  have hx : n⁻¹ * g * n' = h * B.sgs p g * h'⁻¹ := by
    have e1 : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e2 : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet'
    calc n⁻¹ * g * n' = (h * h⁻¹) * (n⁻¹ * g * n') * (h' * h'⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = h * (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹ := by simp only [Matrix.mul_assoc]
  have hb : B.gN (n⁻¹ * g * n') ≤ Bd := by
    rw [hx]
    have h1 := bnd hMW h hh
    have h2 := bnd hMC _ hsg
    have h3 := bnd hMW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')
    calc B.gN (h * B.sgs p g * h'⁻¹) ≤ B.gN (h * B.sgs p g) * B.gN h'⁻¹ := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ B.gN h * B.gN (B.sgs p g) * B.gN h'⁻¹ :=
        mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) (gN_nn _)
      _ ≤ max MW 0 * max MC 0 * max MW' 0 :=
        mul_le_mul (mul_le_mul (h1.trans (le_max_left _ _)) (h2.trans (le_max_left _ _)) (gN_nn _) (le_max_right _ _))
          (h3.trans (le_max_left _ _)) (gN_nn _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  have hBd0 : 0 ≤ Bd := by positivity
  have hpow : B.gN (n⁻¹ * g * n') ^ (2 * r + 1) ≤ Bd ^ (2 * r + 1) := pow_le_pow_left₀ (gN_nn _) hb _
  obtain ⟨hon, hon'⟩ := hCo g hg n hn n' hn'
  have hnR : B.gN n ≤ max R 0 :=
    (hon.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hn'R : B.gN n' ≤ max R 0 :=
    (hon'.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hhR : B.gN h ≤ max R 0 :=
    (bnd hMW h hh).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hh'R : B.gN h' ≤ max R 0 :=
    (bnd hMW' h' hh').trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have sup : ∀ x : Mt k r, ‖x‖ ≤ B.gN (Matrix.of x) := fun x => Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN (Matrix.of x)
  rw [mem_closedBall_zero_iff]
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact (sup _).trans hhR
  · exact (sup _).trans hnR
  · exact (sup _).trans hh'R
  · exact (sup _).trans hn'R

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAGrp
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def capA (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X := C3.AAop k r r le_rfl (Q.uC k r 0 y) F

def capAv (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  C3.AAvop k r r le_rfl (y - ((2 * r + k : ℕ) : ℂ) / 2) F

def capBeta (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a))))

def capAlphaV (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l))

end defs

def JDACapRep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (y : ℂ),
    ∃ Θ Θv : B.DiffOp k r Wp Wq,
      PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θ ∧ PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θv ∧
      B.opOrder Θ = r ∧ B.opOrder Θv = r ∧
      (∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θ : ℕ∞) {g} F →
        B.opApply Θ F g = capA k r y F g) ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θv : ℕ∞) {g} F →
        B.opApply Θv F g = capAv k r y F g

def JDACapInv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ (y : ℂ) (Θ : B.DiffOp P.k P.r Wp Wq), P.r ≤ B.opOrder Θ →
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capA P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ) ∧
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capAv P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ)

def JDACapToda : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capA P.k P.r y J) c g =
          dMul (drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

def JDACapTodaV : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
          dMul (drbF P.r) (Q.crd (Q.cmp (vABm P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

section assembly

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem capa_J_ck (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r)
    {g : Q.Mx P.k P.r} (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) (m : ℕ∞) :
    Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r ∧ B.CkOn m {Q.wCell P.k P.r (Fin.last P.r) c * g} J := by
  have hGV : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV hc hg
  refine ⟨hGV, fun g₀ hg₀ => ?_⟩
  rw [Set.mem_singleton_iff] at hg₀
  subst hg₀
  have hG0 : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
    ⟨hGV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  obtain ⟨U, F, hU, hmem, hF, hJF⟩ := hJ.1 _ ⟨hG0, hcg⟩
  refine ⟨U, F, hU, hmem, hF.of_le ?_, fun x hx hxG => hJF x hx ⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩
  exact_mod_cast le_top

end assembly

theorem jDAGrp_of_parts (hR : JDACapRep) (hI : JDACapInv) (hT : JDACapToda) (hTv : JDACapTodaV) : JDAGrp := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  obtain ⟨Θ, Θv, hP, hPv, hO, hOv, hA, hAv⟩ := hR S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) y
  refine ⟨Θ, Θv, hP, hPv, (hI _ _ (D.parOf S v) (T v).base hpl hk y Θ hO.ge).1 hA,
    (hI _ _ (D.parOf S v) (T v).base hpl hk y Θv hOv.ge).2 hAv, fun J hJ c hc g hg hcg => ⟨?_, ?_⟩⟩
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θ)
    rw [← hT _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hA J _ hGV hCk]
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θv)
    rw [← hTv _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hAv J _ hGV hCk]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQHatQQ
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

theorem jDHatOpQQ_of_opA_opR_residue_splitting (hA : JDOpA) (hR : JDOpR) (h1 : ResidueSplittingModelAlgebra) (h2 : MirrorResidueSplittingModelAlgebra)
    (h3 : JDHatLagrange) (h4 : JDHatNodes) : JDHatOpQQ := by
  obtain ⟨KA, hKA, hA⟩ := hA
  obtain ⟨KR, hKR, hR⟩ := hR
  refine ⟨max KA KR, le_max_of_le_left hKA, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hGQ hML X hX
  have hAat := hA (max KA KR) (le_max_left _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hML
  have hRat := hR (max KA KR) (le_max_right _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGQ hML
  have hAh : ∀ y, HReal (max KA KR) S T v e L (L.Ahat y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hAat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hAhv : ∀ y, HReal (max KA KR) S T v e L (L.Ahatv y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hAat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hRh : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhM (D.parOf S v) L y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hRat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hRhv : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhvM (D.parOf S v) L y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hRat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hx : ∀ y, xInvM (D.parOf S v) y ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) :=
    fun y => jdh_kap_mem _ L _
  obtain ⟨ν, hνi, hνr⟩ := h4 (D.parOf S v)
  have hR0n : ∀ j, HReal (max KA KR) S T v e L (L.R0 (ν j)) := fun j => by
    rw [h1 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRh _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_SSn_mem _ L l hl))
      (jdh_kap_mem _ L _)) (hAh _)
  have hR0vn : ∀ j, HReal (max KA KR) S T v e L (L.R0v (ν j)) := fun j => by
    rw [h2 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRhv _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_kap_mem _ L _))
      (jdh_SSns_mem _ L l hl)) (hAhv _)
  have key : HReal (max KA KR) S T v e L X := by
    simp only [MA.hatSet, Set.mem_union, Set.mem_range] at hX
    rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
    · exact hAh y
    · rw [(h3 _ L ν hνi y).1]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0n j)
    · exact hAhv y
    · rw [(h3 _ L ν hνi y).2]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0vn j)
  exact key

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGGfStep
section
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

theorem gf_castPt {k a b : ℕ} (h : a = b) (z z' : Fin (2 * a + k + 1) → ℂ) (A M C : B.Mat k a) :
    Gf k b (D.castV h z) (D.castV h z') ((D.castM h A)⁻¹ * D.castM h M * D.castM h C) =
      Gf k a z z' (A⁻¹ * M * C) := by
  subst h
  have h1 : ∀ v : Fin (2 * a + k + 1) → ℂ, D.castV rfl v = v := fun v => by
    funext i
    simp [D.castV]
  have h2 : ∀ X : B.Mat k a, D.castM rfl X = X := fun X => by
    ext i j
    simp [D.castM]
  rw [h1, h1, h2, h2, h2]

theorem gram_function_induction : GfStep := by
  intro k ρ m e z z' hz hz' t _ γ xx
  have h1 : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ
  show Gf k m (D.castV e (D.castV h1 (liftVec k 1 ρ z))) (D.castV e (D.castV h1 (liftVec k 1 ρ z')))
      ((D.castM e (D.castM h1 (U.Rn k 1 ρ xx.1)))⁻¹ *
        D.castM e (D.castM h1 (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ)) *
        D.castM e (D.castM h1 (U.Rn k 1 ρ xx.2))) = _
  rw [gf_castPt e, gf_castPt h1,
    level_function_slice k 1 ρ _ _ (Qx4.lift_inWb hz) (Qx4.lift_inWb hz'), lowV_lift, lowV_lift]
  simp [Matrix.det_unique, Complex.normSq_eq_norm_sq]

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceInductionLevel
section
namespace Formalism.FourierDecayAlt.P

theorem slice_induction_level : Formalism.FourierDecayAlt.KB.SliceStep :=
  Formalism.FourierDecayAlt.P.PBH.sliceStep_of Formalism.FourierDecayAlt.P.PBH.jfStep (Formalism.FourierDecayAlt.P.PBH.asm_pointStepT Formalism.FourierDecayAlt.P.PBH.pointStep)

end Formalism.FourierDecayAlt.P
end

