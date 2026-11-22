import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0062
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOfR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0045
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0099
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0076
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0042
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0037
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0013
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.SettingExistsOfGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MuNEqHaarLie
section
noncomputable section

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

theorem torS_eq (δ : ℝ) :
    Formalism.L2.SG.LocWSOf.torS (-Complex.I * (δ : ℂ)) k r = (Complex.I ^ r)⁻¹ • (tT k r * dM k r δ 1) := by
  unfold Formalism.L2.SG.LocWSOf.torS tT dM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  by_cases h1 : i.val < r
  · simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, if_true, one_mul]
    obtain ⟨n, hn⟩ : ∃ n, r = i.val + n := ⟨r - i.val, by omega⟩
    have hn' : r - i.val = n := by omega
    have hIr : Complex.I ^ r = Complex.I ^ i.val * Complex.I ^ n := by rw [← pow_add, ← hn]
    rw [hn', hIr, ← Complex.inv_I]
    push_cast
    field_simp
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hI0)]
  · by_cases h2 : r + k < i.val
    · have h2' : ¬ (i.val ≤ r + k) := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, h2, h2', if_true, if_false, one_mul]
      obtain ⟨n, hn⟩ : ∃ n, r = (2 * r + k - i.val) + n := ⟨r - (2 * r + k - i.val), by omega⟩
      have hn' : r - (2 * r + k - i.val) = n := by omega
      have hIr : Complex.I ^ r = Complex.I ^ (2 * r + k - i.val) * Complex.I ^ n := by rw [← pow_add, ← hn]
      rw [hn', hIr]
      simp only [star_pow, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, neg_neg]
      push_cast
      rw [mul_pow]
      field_simp
    · have h2' : i.val ≤ r + k := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, h1, h2, h2', if_true, if_false]
      push_cast
      rw [mul_one, inv_mul_cancel₀ (pow_ne_zero _ hI0)]

theorem torS_inv_eq (δ : ℝ) (hδ : 0 < δ) :
    Formalism.L2.SG.LocWSOf.torS (-Complex.I * (δ : ℂ))⁻¹ k r = (Complex.I ^ r) • (dMi k r δ 1 * tTi k r) := by
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  unfold Formalism.L2.SG.LocWSOf.torS tTi dMi
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h1 : i.val < r
  · simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, if_true, one_mul]
    obtain ⟨n, hn⟩ : ∃ n, r = i.val + n := ⟨r - i.val, by omega⟩
    have hn' : r - i.val = n := by omega
    have hIr : Complex.I ^ r = Complex.I ^ i.val * Complex.I ^ n := by rw [← pow_add, ← hn]
    rw [hn', hIr, star_pow, Complex.star_def, Complex.conj_I, ← Complex.inv_I]
    push_cast
    field_simp
    rw [div_pow, div_pow, one_pow]
    field_simp
  · by_cases h2 : r + k < i.val
    · have h2' : ¬ (i.val ≤ r + k) := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, h2, h2', if_true, if_false, one_mul]
      obtain ⟨n, hn⟩ : ∃ n, r = (2 * r + k - i.val) + n := ⟨r - (2 * r + k - i.val), by omega⟩
      have hn' : r - (2 * r + k - i.val) = n := by omega
      have hIr : Complex.I ^ r = Complex.I ^ (2 * r + k - i.val) * Complex.I ^ n := by rw [← pow_add, ← hn]
      rw [hn', hIr]
      simp only [star_pow, star_inv₀, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
        neg_neg, inv_inv]
      rw [← Complex.inv_I]
      push_cast
      rw [inv_pow]
      field_simp
      rw [div_pow, one_pow, mul_pow]
      field_simp
    · have h2' : i.val ≤ r + k := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, h1, h2, h2', if_true, if_false]
      push_cast
      rw [star_pow, Complex.star_def, Complex.conj_I, ← Complex.inv_I]
      field_simp
      rw [div_pow, one_pow]
      field_simp

theorem nLeft_holds : Formalism.MainNotions.MeasFS.NLeft := fun k r κ h0 h1 a ha =>
  (Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0 h1).2.2.2 a ha

theorem muN_eq_haarLie (k r : ℕ) :
    ∃ κ₀ : ENNReal, κ₀ ≠ 0 ∧ κ₀ ≠ ⊤ ∧ Formalism.FourierDecayAlt.D.muN k r = haarLie (Nset k r) κ₀ := by
  have hH := Formalism.MainNotions.MeasFS.haar_lie_measure_on_nilpotent (k := k) (r := r) nLeft_holds 1 one_ne_zero ENNReal.one_ne_top
  have hM := Formalism.FourierDecayAlt.Final.d_muNHaar k r
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (Nset k r) _ _ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hH
    hM.conc hM.left hM.finite_compact
  refine ⟨(c : ENNReal), fun h => hM.ne_zero ?_, ENNReal.coe_ne_top, ?_⟩
  · rw [hc, ENNReal.coe_eq_zero.mp h, zero_smul]
  · rw [hc, show ((c : ENNReal)) = (c : ENNReal) * 1 from (mul_one _).symm, haarLie_smul, ENNReal.smul_def]

def kaB (D : Formalism.BasicNotions.D7) : ℝ := D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))

theorem kaB_pos (D : Formalism.BasicNotions.D7) : 0 < kaB D := by
  have hka : 0 < D.host.ka := by
    have hrd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  exact div_pos hka (mul_pos hg0 hg1)

theorem muT_eq (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.LocWSOf.muT D = -Complex.I * (((kaB D)⁻¹ : ℝ) : ℂ) := by
  have hka : 0 < D.host.ka := by
    have hrd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hkac : (D.host.ka : ℂ) ≠ 0 := by exact_mod_cast hka.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  unfold Formalism.L2.SG.LocWSOf.muT Formalism.L2.SG.LocWSOf.cfS Formalism.L2.SG.LocWSOf.frS kaB
  push_cast
  field_simp

theorem torS_muT (D : Formalism.BasicNotions.D7) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r = (Complex.I ^ r)⁻¹ • (tT k r * dM k r (kaB D)⁻¹ 1) := by
  rw [muT_eq, torS_eq]

theorem torS_muT_inv (D : Formalism.BasicNotions.D7) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r = (Complex.I ^ r) • (dMi k r (kaB D)⁻¹ 1 * tTi k r) := by
  rw [muT_eq, torS_inv_eq _ (inv_pos.mpr (kaB_pos D))]

theorem torS_conj (D : Formalism.BasicNotions.D7) (k r : ℕ) (M : Mx k r) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r * M * Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r =
      gStd (kaB D) M := by
  rw [torS_muT, torS_muT_inv, gStd]
  have hI : (Complex.I ^ r) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hI, mul_inv_cancel₀ hI, one_smul]
  simp only [cj, Matrix.mul_assoc]

theorem torS_conjI (D : Formalism.BasicNotions.D7) (k r : ℕ) (M : Mx k r) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r * M * Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r =
      tT k r * cjI k r (kaB D)⁻¹ 1 M * tTi k r := by
  rw [torS_muT, torS_muT_inv]
  have hI : (Complex.I ^ r) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hI, mul_inv_cancel₀ hI, one_smul]
  simp only [cjI, Matrix.mul_assoc]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NGLeaves
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.NGLeaves

open Formalism.BasicNotions Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

theorem ranks_of_dictionary (hD : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (D : D7) :
    Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun hk =>
  Formalism.L2.SG.NGDict.local_counting_bound_thirty_nine _ _ hk (Formalism.L2.SG.Pf.glue_constant_thirty_nine _ _) (hD _ _ hk)

theorem nondegenerate_gram_tuple : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    rw [X.n_eq]
    have h1 := D.R.rS_two
    have h2 := D.R.r_eq
    have h3 := D.R.k_ge
    omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  obtain ⟨X0, hX⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0 = PI.NormGramAtOrigin.gram (starRingEnd _) X.B.I.J X0 := by
    ext a b; rfl
  rw [e]; exact hX

theorem rowNGC_of_leaves
    (hOV : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hNml : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv) (hNC : Formalism.L2.SG.NGCut.NormalInvariants.NormCount)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hAmp : Formalism.L2.SG.Pf.BDat.AmpUnif) (hPt : Formalism.L2.SG.Pf.BDat.PtUnif)
    (hRB : Formalism.L2.SG.Pf.BDatR.RowBDataUnifR)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r)
    (hX : NondegenerateGramTuple) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC)
    (hFam : Formalism.L2.SG.NGLocModel.StepFamC) : Formalism.L2.SG.RowsConc.RowNGC :=
  Formalism.L2.SG.NGLocModel.rowNGC_of_fam Formalism.FourierDecayAlt.Final.pn_rowNGJoint Formalism.FourierDecayAlt.P.norm_chain (ranks_of_dictionary hDict) hX
    hB hE (Formalism.L2.SG.NGVanish.stepTermVanish_of_form hF) hFam
    (Formalism.L2.SG.Pf.BDatR.stepThmBPinnedC_ofR hB3 hAmp hPt hRB) Formalism.L2.SG.NGCut.CorankRelation.corankOne_equivalence_holds
    (Formalism.L2.SG.NGCut.NormalInvariants.stepNormals_of hNml hNC (Formalism.L2.SG.NGCut.VanishingOrbitalPoints.stepNormOne_of_ooVanish hOV))
    (Formalism.L2.SG.NGCut.VanishingOrbitalPoints.stepPoints_of_ooVanish hOV) (Formalism.L2.SG.NGCut.VanishingOrbitalPoints.stepNormOne_of_ooVanish hOV)

theorem rowNGC_of_leaves'
    (hOV : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hNml : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv) (hNC : Formalism.L2.SG.NGCut.NormalInvariants.NormCount)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hAmp : Formalism.L2.SG.Pf.BDat.AmpUnif) (hPt : Formalism.L2.SG.Pf.BDat.PtUnif)
    (hRB : Formalism.L2.SG.Pf.BDatR.RowBDataUnifR)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r)
    (hB : StepChoiceConstantsC) (hE : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC)
    (hFam : Formalism.L2.SG.NGLocModel.StepFamC) : Formalism.L2.SG.RowsConc.RowNGC :=
  rowNGC_of_leaves hOV hNml hNC hB3 hAmp hPt hRB hDict nondegenerate_gram_tuple hB hE hF hFam

theorem rowNGC_of_leaves2
    (hOV : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hNml : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv) (hNC : Formalism.L2.SG.NGCut.NormalInvariants.NormCount)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hAmp : Formalism.L2.SG.Pf.BDat.AmpUnif) (hPt : Formalism.L2.SG.Pf.BDat.PtUnif)
    (hRB : Formalism.L2.SG.Pf.BDatR.RowBDataUnifR)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r)
    (hB : StepChoiceConstantsC) (hPl : Formalism.L2.SG.NGPin.PlaceHaar) (hF : Formalism.L2.SG.NGVanish.FormRelC)
    (hG6 : ∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) (hH : Formalism.L2.SG.FamDefs.HTie)
    (hG5 : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) (hW : Formalism.L2.SG.FamDefs.WeightsNG) (hG4 : Formalism.L2.SG.FamDefs.ProductStructureNonGeneric)
    (hE : Formalism.L2.SG.FamDefs.ExistNG) : Formalism.L2.SG.RowsConc.RowNGC :=
  rowNGC_of_leaves' hOV hNml hNC hB3 hAmp hPt hRB hDict hB (Formalism.L2.SG.NGPin.stepPinExists_of_place hPl)
    (Formalism.L2.SG.NGVanish.formNGC_of_rel hF) (Formalism.L2.SG.FamDefs.stepFamC_of hG6 hH hG5 hW hG4 hE)

theorem rowNGC_of_leaves3
    (hOV : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hAmp : Formalism.L2.SG.Pf.BDat.AmpUnif) (hRB : Formalism.L2.SG.Pf.BDatR.RowBDataUnifR)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hB : StepChoiceConstantsC)
    (hG6 : ∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9)
    (hHP : Formalism.L2.SG.NGHTie.HTPlace) (hHD : Formalism.L2.SG.NGHTie.HTDelta) (hHT : Formalism.L2.SG.NGHTie.HTTheta)
    (hG5 : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) (hW : Formalism.L2.SG.FamDefs.WeightsNG) (hG4 : Formalism.L2.SG.FamDefs.ProductStructureNonGeneric)
    (hE : Formalism.L2.SG.FamDefs.ExistNG) : Formalism.L2.SG.RowsConc.RowNGC :=
  rowNGC_of_leaves' hOV Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInv_holds Formalism.L2.SG.NGCut.NormalCount.NormCount_holds hB3 hAmp Formalism.L2.SG.PointUniformity.ptUnif' hRB hDict hB
    Formalism.L2.SG.NGPin.stepPinExists Formalism.L2.SG.Pf.formNGC_holds
    (Formalism.L2.SG.FamDefs.stepFamC_of hG6 (Formalism.L2.SG.NGHTie.hTie_of hHP hHD hHT) hG5 hW hG4 hE)

end Formalism.L2.SG.NGLeaves
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayClosed
section
noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.Pf.WuDec

theorem besselMultOne_of_uniq (h : PI.BesselMapUniq.BesselMapUniq) : Formalism.L2.SG.LitS.BesselMultOne := by
  intro k r ε lam H _ _ σ z c u Wp _ _ π hl hds hz hT hc hπ B1 B2 h1 h2
  have h1' := (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B1).1 h1
  have h2' := (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B2).1 h2
  obtain ⟨a, b, hab, hlin⟩ := h k r ε lam H σ z c u Wp π hl hds hz hT hc hπ B1 B2 h1' h2'
  exact ⟨a, b, hab, fun v hv => hlin v hv⟩

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem wuDecay_of_gap_closed (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hMU : PI.BesselMapUniq.BesselMapUniq)
    (hQK : Formalism.L2.SG.Pf.WFL.QuotProdK) (hHN : Formalism.L2.SG.Pf.WFL.LocHNProps) (hNU : Formalism.L2.SG.Pf.WFL.NUnimodLoc)
    (hS : LocScalarStep) (hU : LocUniqStep) : WuDecayOfGap :=
  wuDecay_of_gap Formalism.L2.SG.Closed.BesselNVGap_holds Formalism.L2.SG.Closed.CoefWeightedLoc_holds
    Formalism.L2.SG.Closed.WlocExists_holds (Formalism.MainNotions.BridgeCS3dBOW.besselOfW_of_local_decomposition hDI hMU) (besselMultOne_of_uniq hMU)
    hQK hHN hNU hS hU

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem bessel_decay_of_gap (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hMU : PI.BesselMapUniq.BesselMapUniq)
    (hS : LocScalarStep) (hU : LocUniqStep) : WuDecayOfGap :=
  wuDecay_of_gap_closed hDI hMU Formalism.L2.SG.Closed.QuotProdK_holds Formalism.L2.SG.Pf.WFL.locHNProps_holds
    Formalism.L2.SG.Closed.NUnimodLoc_holds hS hU

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem wuDecay_of_gap_scalar (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hMU : PI.BesselMapUniq.BesselMapUniq)
    (hS : LocScalarStep) : WuDecayOfGap :=
  bessel_decay_of_gap hDI hMU hS local_uniqueness_reduction

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem wuDecay_of_gap_jsz (hMU : PI.BesselMapUniq.BesselMapUniq) (hS : LocScalarStep) : WuDecayOfGap :=
  wuDecay_of_gap_scalar Formalism.L2.SG.BesselDiscreteSeries.decInf hMU hS

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem wuDecayOfGap_of_jsz (hMU : PI.BesselMapUniq.BesselMapUniq) : WuDecayOfGap :=
  wuDecay_of_gap_jsz hMU local_scalar_reduction

end Formalism.L2.SG.Pf
end
end

