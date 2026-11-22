import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.Bundle0002
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0065

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComponentParametersContainString
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.LiftParams

theorem param_of_sysParam : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s y, IsEigV R i t h s y → ∀ l : (R.cV i).W →ₗ[ℂ] ℂ, (fun g => l (R.extV i t y g)) ≠ 0 → ∀ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B → GlobalTheory.LFun.IsParamFunV (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (fun g => l (R.extV i t y g)) B := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _hF i t h hh s y hy l hl B hB
  have hC := hG.core
  have h1 := hC.lev.βV i
  unfold IsSDFrame at h1
  obtain ⟨n, hBase⟩ := h1
  have hBase1 : IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1 := by
    simpa only [one_pow] using hBase
  have hfm := Eq.le (hC.models.HV i t).right.left (LinearMap.mem_range_self (R.HV i t).e y)
  have hc := hC.models.cV i
  have hS : ∀ PP : Pl D.host.E, PP ∈ (flag1L (R.datVt i t)).Pg ∨ PP ∈ (flag1L (R.datVt i t)).Q →
      HeightOneSpectrum.under (𝓞 ↥D.host.F) PP ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t :=
    fun _ hPP => GlobalTheory.DownLift.Params.under_mem_badPl R t hPP
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D (Vc D i) (R.βV i) (R.ΛV i) (flag1L (R.datVt i t))
    (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) hBase1 hS).1

  have hfix : ∀ P : Pl D.host.E, GlobalTheory.Hk3.Good R t P → ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ g,
      l ((R.extV i t) y (g * k)) = l ((R.extV i t) y g) := by
    intro P hP k hk g
    have hlo := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) 1 (flag1L (R.datVt i t)) hBase1 P
      (GlobalTheory.DefLiftHecke.one_pow_notMem P 0) (fun PP hPP => hP PP hPP)).1 k hk
    exact congrArg l (GlobalTheory.DefLiftHecke.ext_level (R.cV i) hc hfm hlo.1 hlo.2 g)
  refine ((GlobalTheory.LFun.param_iff_sysParam D (Vc D i) (↑(levG (Vc D i) (R.βV i) (flag1L (R.datVt i t))))
    (levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t))) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) s B hsph).1
    (fun g => l ((R.extV i t) y g)) hl ?_ ?_).2 hB
  · intro v hv k hk g
    have hw0 : ∃ w : HeightOneSpectrum (𝓞 D.host.E), HeightOneSpectrum.under (𝓞 ↥D.host.F) w = v := GlobalTheory.ChainOnto.VacOffS.exists_under v
    obtain ⟨w, hw⟩ := hw0
    have hgood : GlobalTheory.Hk3.Good R t w := (GlobalTheory.DownLift.Params.good_iff R t w).2 (by rw [hw]; exact hv)
    have hm : (GlobalTheory.AdelicU.emb _ (HSpace.gram (Vc D i)) v) k ∈ GlobalTheory.Hk3.hyp (Vc D i) w := (GlobalTheory.HypDict.mem_hyp_iff_embV D v w hw (Vc D i) _).2 ⟨k, hk, rfl⟩
    exact hfix w hgood _ hm g
  · intro P d Rr hR
    have hoff : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) P := by
      obtain ⟨_, _, _, _, hoff, _⟩ := hR
      exact hoff
    have hgood : GlobalTheory.Hk3.Good R t P := (GlobalTheory.Hk3.OpsRowsTuple.offS_badPl_iff R t P).1 hoff
    have hsp : GlobalTheory.Hk3.SphOp (Vc D i) P d Rr :=
      (((GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) 1 (flag1L (R.datVt i t)) hBase1 P
        (GlobalTheory.DefLiftHecke.one_pow_notMem P 0) (fun PP hPP => hgood PP hPP)).2.1 _ d Rr).1 hR).2
    have hlab : GlobalTheory.Hk3.IsLab (Vc D i) P d := ⟨Rr, hsp⟩
    have hK0 := GlobalTheory.SphLabelOps.exists_hyp (Vc D i) P
    obtain ⟨K, hK⟩ := hK0
    have hsp' := hsp
    unfold GlobalTheory.Hk3.SphOp Hecke₂ at hsp'
    obtain ⟨e, f, ϖ, α, _, hpi, hϖ, hϖ2, _, _, _, hα, hdα, _, _⟩ := hsp'
    have r1 := GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi hϖ hϖ2 hα hdα hsp
    have r2 := GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi hϖ hϖ2 hα hdα (GlobalTheory.Hk3.LabDet.sphOp_rep hlab)
    funext g
    have hsum : ∑ γ ∈ Rr, l ((R.extV i t) y (g * γ)) =
        ∑ γ ∈ GlobalTheory.Hk3.rep (Vc D i) P d, l ((R.extV i t) y (g * γ)) := by
      have h0 := r1.sum_eq r2 K.one_mem (fun γ => l ((R.extV i t) y (g * γ)))
        (fun x k hk => by
          simpa only [mul_assoc] using hfix P hgood k (by rw [hK]; exact hk) (g * x))
      simpa only [one_mul] using h0
    have hop : GlobalTheory.Hk3.hkF (Vc D i) P (fun₀ | d => 1) ((R.HV i t).e y) = s P d • (R.HV i t).e y :=
      Eq.trans (Eq.symm (hh P hgood (fun₀ | d => 1) y))
        (Eq.trans (congrArg (⇑(R.HV i t).e) (hy P d hgood hlab)) (map_smul (R.HV i t).e (s P d) y))
    have hext := GlobalTheory.DefLiftHecke.ext_hkF (R.cV i) hc P (fun₀ | d => 1) ((R.HV i t).e y) g
    have hext2 : s P d • (R.cV i).ext ((R.HV i t).e y) g =
        ∑ a ∈ GlobalTheory.Hk3.rep (Vc D i) P d, (R.cV i).ext ((R.HV i t).e y) (g * a) := by
      have h0 := (congrArg (fun z => (R.cV i).ext z g) hop).symm.trans hext
      simpa only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
        one_smul, map_smul, Pi.smul_apply, LinearMap.smul_apply] using h0
    show ∑ γ ∈ Rr, l ((R.extV i t) y (g * γ)) = s P d • l ((R.extV i t) y g)
    refine hsum.trans ?_
    show ∑ γ ∈ GlobalTheory.Hk3.rep (Vc D i) P d, l ((R.cV i).ext ((R.HV i t).e y) (g * γ)) =
      s P d • l ((R.cV i).ext ((R.HV i t).e y) g)
    exact (map_sum l (fun γ => (R.cV i).ext ((R.HV i t).e y) (g * γ)) (GlobalTheory.Hk3.rep (Vc D i) P d)).symm.trans
      ((congrArg l hext2.symm).trans (map_smul l (s P d) _))

end GlobalTheory.LiftParams
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerDualHalfDerivativeLinearForm
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

theorem gramAt_conjTranspose {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, HSpace.gram]
  rw [← h1]
  exact (NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem conj_complexPlace_traceZero_element (D : D7) (τ : D.what₂.Tau) : conj (tauE D τ D.host.xi0) = -tauE D τ D.host.xi0 := by
  have hcm := D.host.isCMField_hostE
  rw [← NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _]
  have h := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  change tauE D τ (star D.host.xi0) = _
  rw [h, map_neg]

theorem re_trace_swap {n m : ℕ} (c : ℂ) (hc : conj c = -c) (G : Matrix (Fin n) (Fin n) ℂ) (hG : Gᴴ = G)
    (X Y : Matrix (Fin n) (Fin m) ℂ) :
    (c * Matrix.trace (Xᴴ * G * Y)).re = -(c * Matrix.trace (Yᴴ * G * X)).re := by
  have ht : Matrix.trace (Xᴴ * G * Y) = conj (Matrix.trace (Yᴴ * G * X)) := by
    have h := Matrix.trace_conjTranspose (Yᴴ * G * X)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      ← Matrix.mul_assoc] at h
    exact h
  rw [ht]
  have hre : c.re = 0 := by
    have := congrArg Complex.re hc
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hre]
  ring

end GlobalTheory.StdUnn

open GlobalTheory.Unf in

theorem GlobalTheory.StdUnn.sch_dRho_dualHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (Y * (dblDec A).qY.map (tauE D τ)) f) x = -(2 * Real.pi * Complex.I) * ((2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re : ℝ) : ℂ) * sch ψ A B ν 𝓨 f x := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν f hf τ Y x
  let d := dblDec A
  let v : VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt (m := B.rank) (n := A.rank) hθ τ Y
  have hq : compAt θ τ d.pY = d.qY.map (tauE D τ) := by
    ext i j
    exact (hθ τ).1 _
  have hL' : IsLineAt θ τ (Y * compAt θ τ d.pY) ((d.extY B).comp (lineAt θ τ Y)) := by
    refine ⟨?_, fun t => ?_, fun t τ' => ?_⟩
    · exact hL.1.matrix_mul continuous_const
    · show ((lineAt θ τ Y t) * d.pY).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
    · show compAt θ τ' ((lineAt θ τ Y t) * d.pY) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2 t τ']
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  have hline := GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL' (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _)
  have hline' : ∀ t, d.extY B (lineAt θ τ Y t) = lineAt θ τ (Y * compAt θ τ d.pY) t := fun t => by
    rw [← hline]; rfl
  have hder := GlobalTheory.Unf.hasDerivAt_mixS_extY D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank d v f hf
    (lineAt θ τ Y) hL.1 hL.2.1 x 0
  have hfun : (fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (d.extY B (lineAt θ τ Y t)) f p) 0) =
      dRho (heisO ψ (dblSp A) B) θ τ (Y * compAt θ τ d.pY) f := by
    funext p
    simp only [hline']
    rfl
  rw [hfun] at hder
  have hphase : ∀ t : ℝ, ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) =
      Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℂ)) * t) := by
    intro t
    have e := GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ (GlobalTheory.Size.posSp D A.rank) B x τ Y t
    have e2 : symplOH (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t)) =
        symplOH (GlobalTheory.Size.posSp D A.rank) B x (lineAt θ τ Y t) := by
      rw [d.symplOH_extX_extY]
      exact (congrArg (trHalf D) (hO_posSp D B A.rank x _)).symm
    have e3 : ψ (symplOH (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) =
        Complex.exp ((Real.pi * Complex.I) *
          ((t * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℝ) : ℂ)) := by
      rw [e2]; exact e
    rw [symplO_eq_two_half, AddChar.map_add_eq_mul, e3, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfun2 : (fun t : ℝ => ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) *
      d.mixS B ψ v.μ v.𝓕 f x 0) =
      fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℂ)) * t) *
          d.mixS B ψ v.μ v.𝓕 f x 0 :=
    funext fun t => by rw [hphase]
  rw [hfun2] at hder
  set a : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) with ha_def
  set M := d.mixS B ψ v.μ v.𝓕 f x 0 with hM
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * t) * M)
      ((2 * Real.pi * Complex.I * (a : ℂ)) * M) 0 := by
    have h2 : HasDerivAt (fun u : ℂ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * u) * M)
        (Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * ((0:ℝ):ℂ)) * ((2 * Real.pi * Complex.I * (a : ℂ)) * 1) * M)
        ((0:ℝ):ℂ) :=
      (((hasDerivAt_id _).const_mul (2 * Real.pi * Complex.I * (a : ℂ))).cexp).mul_const M
    have h3 := h2.comp_ofReal
    refine h3.congr_deriv ?_
    simp
  have heq := hder.unique hexp
  have ha : a = -(2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re) := by
    rw [ha_def]
    refine (GlobalTheory.Unf.symplAt_posSp D B A.rank τ Y (compAt θ τ x)).trans ?_
    rw [GlobalTheory.StdUnn.re_trace_swap _ (GlobalTheory.StdUnn.conj_complexPlace_traceZero_element D τ) _ (GlobalTheory.StdUnn.gramAt_conjTranspose B τ)]
    ring
  show d.mixS B ψ ν 𝓨 _ x 0 = _ * d.mixS B ψ ν 𝓨 f x 0
  rw [← hq]
  change d.mixS B ψ v.μ v.𝓕 _ x 0 = _ * M
  rw [heq, ha]
  push_cast
  ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelCut

variable {D : D7}

theorem tensor_prod_zero {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z = 0)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z = 0) : z = 0 := by
  have key : ∀ z : (A × B) ⊗[F] E, z =
      (LinearMap.inl F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      (LinearMap.inr F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [key z, h1, h2]; simp

theorem adele_zero (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 :=
  tensor_prod_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) (E := D.host.E) z h1 h2

theorem mem_GfC_of (V : HSp D) (y : GA D V) (hy : ∀ i j, infPart D ((mt V y - 1) i j) = 0) : y ∈ GfC V := by
  show infHom V y = 1
  apply Units.ext
  change (mt V y).map (infPart D) = 1
  ext i j
  have := hy i j
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem eq_one_of_parts (V : HSp D) (y : GA D V) (h1 : y ∈ GfC V) (h2 : y ∈ GinfC V) : y = 1 := by
  have k1 : (mt V y).map (infPart D) = 1 := by
    have := congrArg Units.val (show infHom V y = 1 from h1)
    exact this
  have k2 : (mt V y).map (finPart D) = 1 := by
    have := congrArg Units.val (show finHom V y = 1 from h2)
    exact this
  apply GlobalTheory.SplitCut.mt_injective
  rw [GlobalTheory.SplitCut.mt_one]
  ext i j
  apply sub_eq_zero.mp
  apply adele_zero
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k1.trans (Matrix.map_one (infPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k2.trans (Matrix.map_one (finPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j

theorem mem_GfC_of_grpAt (V : HSp D) (P : Pl D → Prop) (x : GA D V) (hx : x ∈ grpAt V P) : x ∈ GfC V := by
  refine mem_GfC_of V x fun i j => ?_
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ idAt D P) => y.1 i j) (show _ = (1 : GL _ _) from hx)
  change Ideal.Quotient.mk (idAt D P) (mt V x i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V x i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h4 : (mt V x - 1) i j ∈ idAt D P := by
    rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2
  exact (RingHom.mem_ker).mp (Ideal.mem_inf.mp h4).1

theorem mem_GfC_of_supp (V : HSp D) {w : Pl D} (e : AE D) (he : ∃ ε, IsPlaceIdem D w ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (y : GA D V) (hy : SuppAt e V y) : y ∈ GfC V := by
  obtain ⟨ε, ⟨α, rfl, -⟩, hε⟩ := he
  have h0 : infPart D (e + cA D e) = 0 := by
    rw [hε]
    exact TensorProduct.zero_tmul _ _
  refine mem_GfC_of V y fun i j => ?_
  rw [← hy i j, RingHom.map_mul, h0, zero_mul]

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

variable {D : D7}

theorem entry_mem_of (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : g ∈ congGrp V I) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ I := by
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ I) => y.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk I (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2

theorem mem_of_entry (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  show (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)) (matHom V g) = 1
  apply Units.ext
  ext i j
  change Ideal.Quotient.mk I (mt V g i j) = (1 : GL (Fin V.rank) (AE D ⧸ I)).1 i j
  rw [Units.val_one]
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
    Ideal.Quotient.eq.mpr (by rw [← Matrix.sub_apply]; exact hg i j)
  rw [h2]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem congGrp_le (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J :=
  fun g hg => mem_of_entry V J g fun i j => h (entry_mem_of V I g hg i j)

theorem idAt_le_idOff_compl (P Q : Pl D → Prop) (hPQ : ∀ w, Q w → ¬ P w) : idAt D P ≤ idOff D Q := by
  intro a ha
  unfold idAt at ha
  unfold idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  exact ha.2 ⟨u.1, hPQ u.1 u.2⟩

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

theorem grpAt_eq_prod_local : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G →
    ∀ (j' : ℕ), ∀ x ∈ grpAt (c.V j') (· ∈ v.gP), ∃ xs : Fin n → GA D (c.V j'),
      (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) ∧ x = (List.ofFn xs).prod := by
  intro D c v n _ _ G hG j' x hx
  have hoff : x ∈ grpOff (c.V j') (fun w => w ∉ Set.range fun i => (G i).q.v) := by
    refine congGrp_le (c.V j') (idAt_le_idOff_compl _ _ fun w hw hP => hw ?_) hx
    obtain ⟨i, hi⟩ := (hG.places w).mp hP
    exact ⟨i, hi.symm⟩
  obtain ⟨a, ha, h, hsupp, hcomm, -, hxa, -⟩ := GlobalTheory.SplitCut.prod_of_trivOff D (c.V j') (Fin n) (fun i => (G i).q.v)
    (fun i => (G i).q.e) hG.inj (fun i => ⟨(G i).q.split, (G i).q.above⟩) x hoff
  have hperm : (Finset.univ.toList.map h).prod = (List.ofFn h).prod := by
    rw [List.ofFn_eq_map]
    refine List.Perm.prod_eq' ((List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) (List.nodup_finRange n)
      (by ext i; simp)).map h) ?_
    exact List.Pairwise.map _ (fun i i' hii => hcomm i i' hii) (Finset.nodup_toList _)
  refine ⟨h, hsupp, ?_⟩
  have hP : (List.ofFn h).prod ∈ GfC (c.V j') := by
    refine (GfC (c.V j')).list_prod_mem fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact mem_GfC_of_supp (c.V j') _ (G i).q.above (h i) (hsupp i)
  have hxf : x ∈ GfC (c.V j') := mem_GfC_of_grpAt _ _ x hx
  rw [hperm] at hxa
  have haf : a ∈ GfC (c.V j') := by
    have : a = x * ((List.ofFn h).prod)⁻¹ := by rw [hxa, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hxf (inv_mem hP)
  rw [hxa, eq_one_of_parts _ a haf ha, one_mul]

end GlobalTheory.LevelCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitModelToPlaceModel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.LocFlat.CFac
open GlobalTheory.FinPl (SplitPt)
open GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier (atW beta nrm OppLines IsLineFrame ofCol ofRow LineFourier SeeSawFourier)
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastCompare

theorem map_mem_integer {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (φ : k →* k') (hφ : Continuous φ)
    {a : k} (ha : a ∈ 𝒪[k]) : φ a ∈ 𝒪[k'] := by
  by_contra h
  rw [Valuation.mem_integer_iff, not_le] at h
  have hK : IsCompact (φ '' (𝒪[k] : Set k)) := (isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[k])).image hφ
  haveI : MulArchimedean (ValueGroupWithZero k') := ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h0 : valuation k' (φ a) ≠ 0 := (zero_lt_one.trans h).ne'
  have hU : ∀ n : ℕ, IsOpen {y : k' | valuation k' y < valuation k' (φ a) ^ n} := fun n => by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset ((IsValuativeTopology.hasBasis_nhds y).mem_of_mem (i := Units.mk0 _ (pow_ne_zero n h0)) trivial) ?_
    intro z hz
    have := (valuation k').map_add_lt hz hy
    simpa using this
  obtain ⟨n, hn⟩ := hK.elim_directed_cover _ hU (fun y _ => by
      obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k' y) h
      exact Set.mem_iUnion.2 ⟨n + 1, hn.trans_lt (pow_lt_pow_right₀ h n.lt_succ_self)⟩)
    (directed_of_isDirected_le fun m n hmn y hy => lt_of_lt_of_le hy (pow_le_pow_right₀ h.le hmn))
  have := hn ⟨a ^ n, pow_mem ha n, rfl⟩
  simp at this

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iota_mul (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]

def pass {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (p : Place D k)
    (p' : Place D k') (h : p'.e = p.e) : k →* k' where
  toFun a := p'.π (p.ι a)
  map_one' := by rw [← p.π.map_one, p.ι_π, ← h, ← p'.ι_π, p'.π_ι, map_one]
  map_mul' a b := by rw [iota_mul, map_mul]

variable {Y Y' n n' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n']

def Scaled {q : SplitPt D k} {S : HSp D} (s : k) (σ : Y ≃ n) (F : Frame k S.rank Y) (α : GlobalTheory.FinPl.Frame q S n) : Prop :=
  ∀ r z, F.β r z = s * α.b r (σ z)

def ren (σ' : Y ≃ n) (σ : Y' ≃ n') : Matrix n n' k ≃ₜ Matrix Y Y' k where
  toFun x := x.submatrix σ' σ
  invFun x := x.submatrix σ'.symm σ.symm
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_id.matrix_submatrix _ _
  continuous_invFun := continuous_id.matrix_submatrix _ _

variable {q : SplitPt D k} {S T : HSp D} {s : k} {σ : Y' ≃ n'} {σ' : Y ≃ n} {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y}
  {α : GlobalTheory.FinPl.Frame q S n'} {β : GlobalTheory.FinPl.Frame q T n}

section Lines

variable {L L'' : HSp D} {ζ₁ : Fin L.rank → D.host.E} {ζ : Fin L''.rank → D.host.E}

end Lines

def colH (n U : Type) [Unique U] : (n → k) ≃ₜ Matrix n U k where
  toFun y := Matrix.of fun r _ => y r
  invFun x r := x r default
  left_inv _ := rfl
  right_inv x := by ext r j; rw [Subsingleton.elim j default]; rfl
  continuous_toFun := continuous_matrix fun r _ => continuous_apply r
  continuous_invFun := continuous_pi fun r => continuous_id.matrix_elem r default

def rowH (n U : Type) [Unique U] : (n → k) ≃ₜ Matrix U n k where
  toFun y := Matrix.of fun _ r => y r
  invFun x := x default
  left_inv _ := rfl
  right_inv x := by ext j r; rw [Subsingleton.elim j default]; rfl
  continuous_toFun := continuous_matrix fun _ r => continuous_apply r
  continuous_invFun := continuous_pi fun r => continuous_id.matrix_elem default r

end GlobalTheory.LastCompare

end
end

