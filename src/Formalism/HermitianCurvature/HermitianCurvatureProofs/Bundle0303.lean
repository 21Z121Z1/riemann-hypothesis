import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0298
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0301
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGerm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0299
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0302
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEDecayAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0283
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0280
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0284

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAll
section
namespace Formalism.FourierDecayAlt.P.CutBP

theorem germ_data_low_levels : GermDataLowAll :=
  germDataLowAll_of_parts low_level_gram low_level_fibre low_level_continuity low_level_germ

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopAll
section
namespace Formalism.FourierDecayAlt.P.CutBP

theorem germ_data_top_level : GermDataTopAll :=
  GT.germDataTopAll_of_parts GT.top_level_gram GT.top_level_germ_leading GT.top_level_fibre GT.top_level_Y_continuity
    GT.field_mem_unitary GT.field_supremum GT.field_measurability GT.field_locality

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimEvT
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def levelZeroRadialIntegral (p : KB.Pl P Wp Wq) (w : List C.Letter) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (q : (Fin P.r → ℂ) × ℂ) : ℂ :=
  (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
    inner ℂ (B.hsVec (B.JF p.T.base H (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))
      (B.hsVec (B.JF p.T.base (w.foldr (fun a G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) H)
        (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))

theorem residual_pairing_eq_integral (p : KB.Pl P Wp Wq) {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hH : B.CkOn ⊤ (B.GV P.k P.r) H)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) : p.RR H 0 w [] [] = ∫ q, levelZeroRadialIntegral p w H q := by
  unfold KB.Pl.RR
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hH (good_positioned_of_cut hw)]
  rfl

def PtwCut (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ᵐ q : (Fin P.r → ℂ) × ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε) q = levelZeroRadialIntegral p w F q

def DomCut (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε)) volume) ∧
  ∃ h : (Fin P.r → ℂ) × ℂ → ℝ, Integrable h ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ q : (Fin P.r → ℂ) × ℂ, ‖levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε) q‖ ≤ h q

theorem limEvT_of_cut (p : KB.Pl P Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (Y : Finset ℝ) (N : ℕ)
    (hP : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → PtwCut p χ F w)
    (hD : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → DomCut p χ F w) : LimEvT p χ F Y N := by
  intro w hw hN
  have e : (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) =
      fun ε => (∫ q, levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε) q).re :=
    funext fun ε => by rw [residual_pairing_eq_integral p (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε) hw.1]
  rw [e, residual_pairing_eq_integral p hF hw.1]
  obtain ⟨hmeas, h, hint, hb⟩ := hD w hw hN
  have hlim : ∀ᵐ q : (Fin P.r → ℂ) × ℂ, Tendsto (fun ε : ℝ => levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε) q) (𝓝[>] 0)
      (𝓝 (levelZeroRadialIntegral p w F q)) := by
    filter_upwards [hP w hw hN] with q hq
    exact tendsto_const_nhds.congr' (hq.mono fun ε h => h.symm)
  exact (Complex.continuous_re.tendsto _).comp
    (tendsto_integral_filter_of_dominated_convergence h hmeas hb hint hlim)

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopHer
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem stepExp0_of_leaves (hO : OneLetterDens) (hS : DensSmoothCls) (hR : RadDecay) : Formalism.FourierDecayAlt.P5.HerD.StepExp0 :=
  stepExp0_of_open hO hS (decayPair2_of_smooth hS) (decayPair3_of wave_outgoing_orbital (clsDecayJ_of hR))
    (decayPair4_of wave_outgoing_orbital (clsDecayJ_of hR) site_multiplication_orbital)

theorem thmPActualCpt_of_leaves (hO : OneLetterDens) (hS : DensSmoothCls) (hR : RadDecay) :
    Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  Formalism.FourierDecayAlt.P5.HerD.thmPActualCpt_of_stepExp0 (stepExp0_of_leaves hO hS hR)

end Formalism.FourierDecayAlt.P.CutSE
end

