import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0069
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0068
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0066
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0067

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinRX
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.AmpWinRX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (u u' : D.what₂.Word)

theorem goodW_all (τ : D.what₂.Tau) : GoodW D τ u u' θ (locW C u u' τ) :=
  goodW_of C u u' τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u' τ) (Formalism.L2.SG.Pf.zTr C u τ)
    (Formalism.L2.SG.Pf.zTr C u' τ) (Formalism.L2.SG.Pf.haarTr C τ)

end Formalism.L2.SG.Pf.AmpWinRX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCut
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.Pf.Carrier.CarPinCut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cut_of_haar (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 F) (hGV : γ ∈ Formalism.FourierDecayAlt.B.GV k r) (hRel : Formalism.FourierDecayAlt.C6.IsRelevant B γ)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (hd : ∀ a, d a ≠ 0)
    (hZ : Formalism.QuantumDeterminants.Zhat k r B.z B.z' γ = Formalism.FourierDecayAlt.C2.monoP w d) (hGf : 0 < Formalism.QuantumDeterminants.Gf k r B.z B.z' γ)
    (hH : μ (Formalism.FourierDecayAlt.C6.Rset γ)ᶜ = 0 ∧ (∀ a ∈ Formalism.FourierDecayAlt.C6.Rset γ, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) ∧
      (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μ K < ⊤) ∧ μ ≠ 0) :
    ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut B γ μ θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B γ F p) B.μSS := by
  obtain ⟨θ, hθ, hint⟩ := Formalism.FourierDecayAlt.P.orbital_integral_converges.choose_spec k r Wp Wq B γ w d A₀ F hGV hRel hd hZ hGf hA hCC
  have hMu := Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq B γ w d hGV hd hZ
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (Formalism.FourierDecayAlt.C6.Rset γ) (Formalism.FourierDecayAlt.D.muR B γ w) μ
    (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hGV)) hMu hH.1 hH.2.1 hH.2.2.1
  have hc0 : c ≠ 0 := by
    intro h0
    apply hH.2.2.2
    rw [hc, h0, zero_smul]
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    have := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0)
    exact this
  have hμ : μ = ENNReal.ofReal (c : ℝ) • Formalism.FourierDecayAlt.D.muR B γ w := by
    rw [hc, ENNReal.ofReal_coe_nnreal]
    rfl
  refine ⟨fun p => θ p / (c : ℝ), ?_, ?_⟩
  · rw [hμ, Formalism.L2.SG.Pf.Bridge.isNormCut_smul B γ _ hcpos]
    have e : (fun p => (c : ℝ) * (θ p / (c : ℝ))) = θ := by
      funext p; field_simp
    rw [e]
    exact hθ
  · have e : (fun p => (θ p / (c : ℝ)) • Formalism.FourierDecayAlt.D.orbIntegrand B γ F p) =
        fun p => ((c : ℝ)⁻¹ : ℝ) • (θ p • Formalism.FourierDecayAlt.D.orbIntegrand B γ F p) := by
      funext p
      rw [smul_smul, div_eq_inv_mul]
    rw [e]
    exact hint.smul ((c : ℝ)⁻¹ : ℝ)

end Formalism.L2.SG.Pf.Carrier.CarPinCut

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.LocWSOf Formalism.BasicNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

def HaarFields {k r : ℕ} (U : Set (Formalism.FourierDecayAlt.B.Mat k r)) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  μ Uᶜ = 0 ∧ (∀ a ∈ U, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) ∧ (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μ K < ⊤) ∧ μ ≠ 0

def FrameAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ ∈ Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS ∧
    (∃ (w : Equiv.Perm (Fin (D.R.rS + 1))) (d : Fin (D.R.rS + 1) → ℂ), (∀ a, d a ≠ 0) ∧
      Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z
        (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z'
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) =
        Formalism.FourierDecayAlt.C2.monoP w d) ∧
    0 < Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z
      (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z'
      (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) ∧
    HaarFields (Formalism.FourierDecayAlt.C6.Rset
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ))
      (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
        (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x)))

theorem cutAt_of (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (hF : FrameAt C u u' τ) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 (fcAt C u u' τ a b ξ ξ' c)) : CutAt C u u' τ a b ξ ξ' c := by
  intro γ μRv ν hP
  obtain ⟨hGV, ⟨w, d, hd, hZ⟩, hGf, hH⟩ := hF γ μRv ν hP
  exact Formalism.L2.SG.Pf.Carrier.CarPinCut.cut_of_haar _ _ _ _ A₀ hA hCC hGV hP.2.2.1 w d hd hZ hGf hH

theorem trHyp_Qc (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u (vOf X τ))
      (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ))
      (fun a : Fin D.R.rS => Formalism.L2.SG.LocWSOf.cfS D ^ (D.R.rS - (a : ℕ))) :=
  ⟨(Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).1, (Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.1,
    (Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.2.1,
    fun a => ((Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.2.2 a a rfl).1,
    fun a => ((Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.2.2 a a rfl).2⟩

def HaarAtC (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    HaarFields (Formalism.FourierDecayAlt.C6.Rset
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ))
      (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
        (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x)))

set_option maxHeartbeats 2000000 in

theorem frameAt_of (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hH : HaarAtC C u u' τ) : FrameAt C u u' τ := by
  intro γ μRv ν hP
  obtain ⟨hG, hM, -, -, -⟩ := id hP
  refine ⟨Formalism.L2.SG.Pf.Bridge.delta_GV (trHyp_Qc C u τ) (Formalism.L2.SG.Pf.Carrier.uMat_unitary γ), ?_,
    gf_pos_tr (trHyp_Qc C u τ) (trHyp_Qc C u' τ) (uMat γ) hG, hH γ μRv ν hP⟩
  have hz : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z
      (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z'
      (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) =
      Matrix.diagonal (fun a => star (Formalism.L2.SG.Pf.Bridge.lam
        (fun a : Fin D.R.rS => Formalism.L2.SG.LocWSOf.cfS D ^ (D.R.rS - (a : ℕ))) 1 a)) *
        Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ) *
        Matrix.diagonal (Formalism.L2.SG.Pf.Bridge.lam
          (fun a : Fin D.R.rS => Formalism.L2.SG.LocWSOf.cfS D ^ (D.R.rS - (a : ℕ))) 1) :=
    Formalism.L2.SG.Pf.Bridge.zhat_cs (trHyp_Qc C u τ) (trHyp_Qc C u' τ) one_ne_zero (uMat γ)
  have hm := mono_scale hM (fun i => star_ne_zero.mpr (Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_Qc C u τ) one_ne_zero i))
    (fun i => Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_Qc C u τ) one_ne_zero i)
  rw [← hz] at hm
  obtain ⟨w, d, hd, hwd⟩ := hm
  exact ⟨w, d, hd, hwd⟩

theorem cutAt_of_haar (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (hH : HaarAtC C u u' τ) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 (fcAt C u u' τ a b ξ ξ' c)) : CutAt C u u' τ a b ξ ξ' c :=
  cutAt_of C u u' τ a b ξ ξ' c (frameAt_of C u u' τ hH) A₀ hA hCC

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HaarTrHolds
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem trHyp_C (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (PtRepPf.frU X u (vOf X τ)) (C.Q τ) (C.Qi τ)
      (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) := by
  obtain ⟨h1, h2, hH, hef⟩ := C.isT τ
  exact ⟨h1, h2, hH, fun a => (hef a a rfl).1, fun a => (hef a a rfl).2⟩

theorem n_eq : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have h := (PtRepPf.frU X (Classical.arbitrary D.what₂.Word) v).card
  omega

theorem trG_mul_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹ = 1 := by
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  unfold trG
  calc C.Qi τ * uMat γ * C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ)
      = C.Qi τ * uMat γ * (C.Q τ * C.Qi τ) * uMat γ⁻¹ * C.Q τ := by simp only [Matrix.mul_assoc]
    _ = C.Qi τ * (uMat γ * uMat γ⁻¹) * C.Q τ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul_inv, Matrix.mul_one, h1]

theorem trG_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (trG (C.Q τ) (C.Qi τ) γ)⁻¹ = trG (C.Q τ) (C.Qi τ) γ⁻¹ :=
  Matrix.inv_eq_right_inv (trG_mul_inv C τ γ)

theorem trG_mul (τ : D.what₂.Tau) (a b : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) (a * b) = trG (C.Q τ) (C.Qi τ) a * trG (C.Q τ) (C.Qi τ) b := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  unfold trG
  rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
  calc C.Qi τ * (uMat a * uMat b) * C.Q τ = C.Qi τ * uMat a * (C.Q τ * C.Qi τ) * uMat b * C.Q τ := by
        rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem haarTr_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : HaarTr C u u' τ := by
  intro γ μRv hH
  obtain ⟨hσ, hne, hconc, hinv⟩ := hH
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hT := trHyp_C C u τ
  have hT' := trHyp_C C u' τ
  set f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x) with hf
  have hemb : Topology.IsClosedEmbedding f := Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ h2
  have hme : MeasurableEmbedding f := hemb.measurableEmbedding
  have hU : ∀ y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := fun y => y.2

  have hfwd : ∀ y ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
      (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ, trG (C.Q τ) (C.Qi τ) y ∈ RStab D.R.k D.R.rS (gB C τ γ) := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨Formalism.L2.SG.Pf.Bridge.fwd_N hT (hU y) hy1, ?_⟩
    show (trG (C.Q τ) (C.Qi τ) γ)⁻¹ * trG (C.Q τ) (C.Qi τ) y * trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS
    rw [trG_inv, ← trG_mul, ← trG_mul]
    exact Formalism.L2.SG.Pf.Bridge.fwd_N hT' (hU _) hy2
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI := hσ; exact hme.sigmaFinite_map
  · intro h0
    apply hne
    have h := congrArg (fun m : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) => m Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    rw [hme.map_apply, Set.preimage_univ] at h
    exact Measure.measure_univ_eq_zero.1 h
  · rw [hme.map_apply]
    refine measure_mono_null (fun y hy => ?_) hconc
    intro hyS
    exact hy (hfwd y hyS)
  · intro s hs
    obtain ⟨hsN, hsN'⟩ := hs
    have hmem := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hsN.1
    set y0 := Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * s * C.Qi τ) hmem with hy0
    have hy0S : y0 ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
        (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ := by
      refine ⟨Formalism.L2.SG.Pf.Bridge.inN_Q hT hsN, ?_⟩
      show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (γ⁻¹ * y0 * γ))
      have e : uMat (γ⁻¹ * y0 * γ) = C.Q τ * ((gB C τ γ)⁻¹ * s * gB C τ γ) * C.Qi τ := by
        rw [trG_inv]
        show uMat (γ⁻¹ * y0 * γ) = C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ * s * (C.Qi τ * uMat γ * C.Q τ)) * C.Qi τ
        rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul, Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
        show uMat γ⁻¹ * (C.Q τ * s * C.Qi τ) * uMat γ = _
        simp only [← Matrix.mul_assoc]
        rw [h2, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one]
      rw [e]
      exact Formalism.L2.SG.Pf.Bridge.inN_Q hT' hsN'
    have hcomp : (Formalism.QuantumDeterminants.lmulM s) ∘ f = f ∘ (fun x => y0 * x) := by
      funext x
      simp only [Function.comp, hf, Formalism.QuantumDeterminants.lmulM, Matrix.of_symm_apply]
      rw [trG_mul]
      congr 1
      show s = C.Qi τ * (C.Q τ * s * C.Qi τ) * C.Q τ
      simp only [← Matrix.mul_assoc]
      rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcont_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    rw [Measure.map_map hcont_l hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_mul_left y0).measurable, hinv y0 hy0S]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PinCovCarrierInTc
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem pinCov_carrierInTc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀)))
    (Hj : ∀ j : Fin (nfE D),
      ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (tauE X e j))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (tauE X e j)))),
        Formalism.L2.SG.Pf.Carrier.JointPin.PinHyp
          (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo)
          (tauE X e j) γ μRv ν →
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
          Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
          Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (tauE X e j)) (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
            (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
            (Formalism.L2.SG.Pf.Carrier.CarPinTor.fcAt C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) (cc j))) :
    Formalism.L2.SG.Pf.Carrier.JointPin.PinCov
      (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo) := by
  intro v γ μRv ν hH
  obtain ⟨j, rfl⟩ := (tauE X e).surjective v
  have key : ∀ (j' : Fin (nfE D)) (h' : X.pl.symm (e (plE D j')) = tauE X e j),
      (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
        Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
        ((castLoc X u h').toContinuousLinearEquiv.toContinuousLinearMap :
            X.Vloc u (tauE X e j') →L[ℂ] X.Vloc u (tauE X e j)).comp
          ((Formalism.FourierDecayAlt.D.orbJ (towersOf X C u u' e j').base (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
              (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
              (fcT X C e u u' a b ξ ξ' cc j')).comp
            ((castLoc X u' h').symm.toContinuousLinearEquiv.toContinuousLinearMap :
              X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u' (tauE X e j'))) := by
    intro j' h'
    have hj : j' = j := (tauE X e).injective h'
    subst hj
    rw [towersOf_base, Hj j' γ μRv ν hH]
    ext x
    rfl
  exact key _ (tauE_symm X e (tauE X e j))

end Formalism.L2.SG.Pf.CarrierT
end
end

