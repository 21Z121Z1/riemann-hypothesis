import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0024
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.SeeHH

theorem inner_antiunitary_swap {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) : ⟪U x, U y⟫_ℂ = ⟪y, x⟫_ℂ := by
  have hI : ∀ z : E, U (Complex.I • z) = (-Complex.I) • U z := by
    intro z; rw [map_smulₛₗ]; simp
  have h1 : ‖U x + U y‖ = ‖y + x‖ := by rw [← map_add, U.norm_map, add_comm]
  have h2 : ‖U x - U y‖ = ‖y - x‖ := by rw [← map_sub, U.norm_map, norm_sub_rev]
  have h3 : ‖U x - Complex.I • U y‖ = ‖y - Complex.I • x‖ := by
    have e1 : U x - Complex.I • U y = U (x + Complex.I • y) := by
      rw [map_add, hI, neg_smul, sub_eq_add_neg]
    have e2 : y - Complex.I • x = (-Complex.I) • (x + Complex.I • y) := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]; abel
    rw [e1, U.norm_map, e2, norm_smul]; simp
  have h4 : ‖U x + Complex.I • U y‖ = ‖y + Complex.I • x‖ := by
    have e1 : U x + Complex.I • U y = U (x - Complex.I • y) := by
      rw [map_sub, hI, neg_smul, sub_neg_eq_add]
    have e2 : y + Complex.I • x = Complex.I • (x - Complex.I • y) := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]; abel
    rw [e1, U.norm_map, e2, norm_smul]; simp
  rw [inner_eq_sum_norm_sq_div_four (U x) (U y), inner_eq_sum_norm_sq_div_four y x]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, h3, h4]

end GlobalTheory.Core.Mi.SeeHH

namespace GlobalTheory.Core.Mi.SeeHH

theorem star_toLp_eq {D : D7} (X : HidaSetting D) {f : X.B.I.GA → ℂ} (hm : MemLp f 2 (muX X))
    (hs : MemLp (fun x => star (f x)) 2 (muX X)) :
    star (hm.toLp f) = hs.toLp (fun x => star (f x)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (hm.toLp f), hm.coeFn_toLp, hs.coeFn_toLp] with x a1 a2 a3
  rw [a1, a3, Pi.star_apply, a2]

theorem re_fix_of_row {D : D7} (X : HidaSetting D) {f : X.B.I.GA → ℂ} (hf : RowFun X f) (hm : MemLp f 2 (muX X)) :
    X.B.Re (star (hm.toLp f)) = star (hm.toLp f) := by
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hm.star
  rw [star_toLp_eq X hm hs]
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hKM : MeasurableSet X.K2 := (Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL).isOpen.measurableSet
  have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
  refine Formalism.L2.SG.Pf.idempotent_fixes_invariant_L2 X (fun x => star (f x)) ?_ ?_ hs ?_
  · exact (continuous_star.comp hf.cont).measurable
  · intro γ hγ y
    rw [hf.left γ hγ y]
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfun : (fun g => X.B.e g * star (f (y * (1, g)))) =
        X.K2.indicator (fun _ => star (f y) / ((X.B.μf X.K2).toReal : ℂ)) := by
      funext g
      rw [X.e_eq g]
      by_cases hg : g ∈ X.K2
      · have hg' : g ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
        rw [if_pos hg', Set.indicator_of_mem hg, hf.right g hg y]
        have hn : ‖X.chi2 g‖ = 1 := hK.2.2.2.2 g hg
        have hc : star (X.chi2 g) * X.chi2 g = 1 := by
          rw [← starRingEnd_apply, Complex.conj_mul', hn]; simp
        have e2 : chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd g = X.chi2 g := rfl
        have ev : X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw) = X.B.μf X.K2 := rfl
        rw [e2, ev, star_mul', star_star, div_eq_mul_inv, div_eq_mul_inv]
        linear_combination (star (f y) * (((X.B.μf X.K2).toReal : ℂ))⁻¹) * hc
      · have hg' : g ∉ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
        rw [if_neg hg', Set.indicator_of_notMem hg, zero_mul]
    rw [hfun, integral_indicator hKM, setIntegral_const]
    simp only [Measure.real]
    rw [Complex.real_smul]
    have hvc : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by exact_mod_cast hvol
    rw [mul_comm, div_mul_cancel₀ _ hvc]

end GlobalTheory.Core.Mi.SeeHH

namespace GlobalTheory.Core.Mi.SeeHH

theorem real_shift {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ)
    (t : GA D (D.sp.Y 0)) (ht : t ∈ GfC (D.sp.Y 0)) (hR : RealSplit X h θ) (v₀ : M.Vec) (g : X.B.I.Ginf) :
    ∃ a : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ,
      (∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ)) ∧
      (∀ τ, (iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))).1 (X.pl.symm τ) = g (X.pl.symm τ)) ∧
      ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (a τ) (v₀ τ : M.H τ)) ∧
        ∀ U ∈ Mult θ M J χ, ∀ x, U v₀ ((iotaX X h).symm (x * (g, 1)) * t) = U w ((iotaX X h).symm x * t) := by
  classical
  choose a ha hb using fun τ => hR.2.2.2 τ (g (X.pl.symm τ))
  have hsm : ∀ τ, M.rep τ (a τ) (v₀ τ : M.H τ) ∈ M.sm τ := fun τ =>
    GlobalTheory.SmoothStable.rep_mem_sm D (D.sp.Y 0) S M τ (a τ) (ha τ) _ (v₀ τ).2
  let gs : Finset D.what₂.Tau → X.B.I.GA := fun s => ((fun v => if X.pl v ∈ s then g v else 1), 1)
  let ws : Finset D.what₂.Tau → M.Vec := fun s τ => if τ ∈ s then ⟨_, hsm τ⟩ else v₀ τ
  have key : ∀ s : Finset D.what₂.Tau, ∀ U ∈ Mult θ M J χ, ∀ x,
      U v₀ ((iotaX X h).symm (x * gs s) * t) = U (ws s) ((iotaX X h).symm x * t) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro U _ x
      have e1 : gs ∅ = 1 := Prod.ext (funext fun v => by simp [gs]) rfl
      have e2 : ws ∅ = v₀ := funext fun τ => by simp [ws]
      rw [e1, e2, mul_one]
    | insert τ s hτ ih =>
      intro U hU x
      obtain ⟨he2, hoth, -⟩ := hR.2.2.1 τ (a τ) (ha τ)
      have hws : ws s τ = v₀ τ := by simp [ws, hτ]
      have hupd : ws (insert τ s) = Function.update (ws s) τ ⟨_, hsm τ⟩ := by
        funext σ
        by_cases hσ : σ = τ
        · subst hσ; simp [ws]
        · simp [ws, hσ, Function.update_of_ne hσ]
      have hE := Formalism.IndefR.Eqv.KerDiag.mult_equiv θ M J χ hU τ (ha τ) (ws s) ⟨_, hsm τ⟩
        (by simp only [hws])
      have hmul : iotaX X h (atTau θ (D.sp.Y 0) τ (a τ)) * gs s = gs (insert τ s) := by
        refine Prod.ext (funext fun v => ?_) ?_
        · simp only [gs, Prod.fst_mul, Pi.mul_apply]
          by_cases hv : v = X.pl.symm τ
          · subst hv
            have hm : X.pl (X.pl.symm τ) ∈ insert τ s := by simp
            have hn : X.pl (X.pl.symm τ) ∉ s := by simpa using hτ
            rw [if_pos hm, if_neg hn, hb τ, mul_one]
          · have hpv : X.pl v ≠ τ := fun e => hv (by rw [← e, Equiv.symm_apply_apply])
            rw [hoth v hv, one_mul]
            simp [Finset.mem_insert, hpv]
        · simp only [gs, Prod.snd_mul, he2, mul_one]
      rw [hupd, hE]
      show U v₀ ((iotaX X h).symm (x * gs (insert τ s)) * t) =
        U (ws s) ((iotaX X h).symm x * t * atTau θ (D.sp.Y 0) τ (a τ))
      rw [mul_assoc, ← GlobalTheory.HeckeParts.comm_atTau ht τ (a τ), ← mul_assoc]
      have hι : (iotaX X h).symm x * atTau θ (D.sp.Y 0) τ (a τ) =
          (iotaX X h).symm (x * iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))) := by
        rw [map_mul, ContinuousMulEquiv.symm_apply_apply]
      rw [hι, ← ih U hU, mul_assoc, hmul]
  have eu : gs Finset.univ = (g, 1) := Prod.ext (funext fun v => by simp [gs]) rfl
  refine ⟨a, ha, hb, ws Finset.univ, fun τ => by simp [ws], fun U hU x => ?_⟩
  rw [← key Finset.univ U hU x, eu]

theorem coef_eq {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (v₀ : M.Vec) (hCV : ConjVec X h θ M v₀) (g : X.B.I.Ginf)
    (a : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ)
    (ha : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ))
    (hb : ∀ τ, (iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))).1 (X.pl.symm τ) = g (X.pl.symm τ))
    (w : M.Vec) (hw : ∀ τ, (w τ : M.H τ) = M.rep τ (a τ) (v₀ τ : M.H τ)) :
    ∏ τ, ⟪(w τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = Formalism.L2.SG.ProjRows.mInf X.B.I X.B.σ X.B.w g := by
  obtain ⟨c, hc1, hc2⟩ := hCV
  have e : ∀ τ, ⟪(w τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ =
      ⟪X.B.w (X.pl.symm τ), X.B.σ (X.pl.symm τ) (uMat (g (X.pl.symm τ))) (X.B.w (X.pl.symm τ))⟫_ℂ := by
    intro τ
    rw [← inner_antiunitary_swap (c τ) (v₀ τ : M.H τ) (w τ : M.H τ), hw τ,
      hc1 τ (a τ) (ha τ), hb τ, hc2 τ]
  simp_rw [e]
  exact Fintype.prod_equiv X.pl.symm _ _ (fun _ => rfl)

end GlobalTheory.Core.Mi.SeeHH

open GlobalTheory.Core.Mi.SeeHH in

theorem GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ T ∈ MultT θ M J χ, ∀ φ : L2X X, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX X := by
  intro hP D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hCV T hT φ hφ
  obtain ⟨-, -, -, -, -, hL⟩ := GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps D X hGap
  have hR := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hIdE
  have hTm : PiTensorProduct.lift.symm T ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  obtain ⟨hRow, hMem⟩ := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hP D X h θ S M J χ t hθ hMat T hT (PiTensorProduct.tprod ℂ v₀)
  have hfx : ∀ x, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) x =
      (PiTensorProduct.lift.symm T) v₀ ((iotaX X h).symm x * t) := fun x => rfl
  generalize PiTensorProduct.lift.symm T = U at hTm hfx
  generalize evS X h t (T (PiTensorProduct.tprod ℂ v₀)) = f at hRow hMem hφ hfx
  have hφ' : φ = hMem.toLp f := Lp.ext (hφ.trans hMem.coeFn_toLp.symm)
  have hRe := re_fix_of_row X hRow hMem
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact GlobalTheory.Mem.SJ.SchurMove.castGA_mem_GFset _ _
  obtain ⟨κ, hκ⟩ := GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge M θ J χ (fun μ 𝓕 => GlobalTheory.MultFinite.schurMult hP μ 𝓕) hθ
    X.B.I X.B.μf X.B.fund X.B.fund_spec (iotaX X h) hι t U hTm U hTm
  have hv₀ : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    obtain ⟨c, -, hc2⟩ := hCV
    refine Finset.prod_eq_one fun τ _ => ?_
    have hn : ‖(v₀ τ : M.H τ)‖ = 1 := by
      rw [← (c τ).norm_map, hc2 τ]
      exact (X.low _).1
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hMem.star
  have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, star (f (γ * y)) = star (f y) := fun γ hγ y => by
    rw [hRow.left γ hγ y]
  have hnorm : (((‖hs.toLp (fun x => star (f x))‖ ^ 2 : ℝ)) : ℂ) = κ := by
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hs, ← integral_complex_ofReal]
    have e := hκ v₀ v₀
    rw [hv₀, mul_one] at e
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [norm_star, hfx x, ← starRingEnd_apply, Complex.conj_mul']
    push_cast
    ring
  have hRph : X.Rph (star (hMem.toLp f)) = star (hMem.toLp f) := by
    rw [star_toLp_eq X hMem hs]
    refine Formalism.L2.SG.EvalTRph.rph_fix_of_coef X hL _ (fun g => ?_)
    obtain ⟨a, ha, hb, w, hw, hsh⟩ := real_shift X h θ M J χ t hMat.1 hR v₀ g
    have hco := coef_eq X h θ M v₀ hCV g a ha hb w hw
    have hRg := Formalism.L2.SG.EvalTReg.reg_toLp_X X (fun x => star (f x)) hinv hs (g, 1)
    have hpair : ⟪hs.toLp (fun x => star (f x)), X.B.R (g, 1) (hs.toLp (fun x => star (f x)))⟫_ℂ =
        ∫ x, star (U w ((iotaX X h).symm x * t)) * U v₀ ((iotaX X h).symm x * t) ∂(muX X) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs.coeFn_toLp, hRg] with x a1 a2
      rw [a1, a2]
      simp only [RCLike.inner_apply, hfx]
      rw [hsh U hTm x, starRingEnd_apply, star_star, mul_comm]
    rw [hpair, hκ w v₀, hco, hnorm]
  rw [hφ']
  refine ⟨star (hMem.toLp f), ?_⟩
  show X.B.Re (X.Rph _) = _
  rw [hRph, hRe]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapHasLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowLev

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem e_left (k : X.B.I.Gf) (hk : k ∈ X.K2) (y : X.B.I.Gf) : X.B.e y = X.chi2 k * X.B.e (k * y) := by
  obtain ⟨-, hKm, hKi, hχm, hχn⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hK : ∀ z, z ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw ↔ z ∈ X.K2 := fun z => Iff.rfl
  rw [X.e_eq y, X.e_eq (k * y)]
  by_cases hy : y ∈ X.K2
  · have hky : k * y ∈ X.K2 := hKm k hk y hy
    rw [if_pos ((hK y).2 hy), if_pos ((hK _).2 hky)]
    change star (X.chi2 y) / _ = X.chi2 k * (star (X.chi2 (k * y)) / _)
    rw [hχm k hk y hy, star_mul', ← mul_div_assoc, ← mul_assoc]
    have h1 : X.chi2 k * star (X.chi2 k) = 1 := by
      rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχn k hk]; simp
    rw [h1, one_mul]
  · have hky : k * y ∉ X.K2 := fun h' => hy (by simpa using hKm _ (hKi k hk) _ h')
    rw [if_neg (fun h' => hy ((hK y).1 h')), if_neg (fun h' => hky ((hK _).1 h')), mul_zero]

theorem R_comp_Re (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous X.B
  obtain ⟨-, hT⟩ := X.B.Re_spec
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  refine ContinuousLinearMap.ext fun y => ?_
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, hT, hT, ← integral_const_mul,
    ← integral_mul_left_eq_self (fun h => X.chi2 k * (X.B.e h * ⟪x, X.B.R (1, h) y⟫_ℂ)) k]
  congr 1
  funext h
  have e1 : ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = ⟪x, X.B.R (1, k * h) y⟫_ℂ := by
    rw [← GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, pm]
    rfl
  show X.B.e h * ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = X.chi2 k * (X.B.e (k * h) * ⟪x, X.B.R (1, k * h) y⟫_ℂ)
  rw [e1, e_left X k hk h, mul_assoc]

end GlobalTheory.ConjRowLev

namespace GlobalTheory.ConjRowMult

open GlobalTheory.ConjRowLev in

theorem conjMap_lev : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, ∀ k ∈ J, ∀ g : GA D (D.sp.Y 0), GlobalTheory.ConjRowMult.conjMap X M c Φ h t u (g * k) = χ k * GlobalTheory.ConjRowMult.conjMap X M c Φ h t u g := by
  intro _ D X h θ S M J χ t c _ _ _ _ hM _ Φ hΦ hrep u k hk g
  obtain ⟨-, hCL⟩ := hM
  obtain ⟨hJ, hχ⟩ := hCL k
  have hk0 := hJ.1 hk
  obtain ⟨h1, h2⟩ : (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧ (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hk0
  set k' := (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 with hk'
  have hsplit : g * k * t⁻¹ = (g * t⁻¹) * (t⁻¹⁻¹ * k * t⁻¹) := by group
  have hι : iotaX X h (g * k * t⁻¹) = iotaX X h (g * t⁻¹) * ((1, k') : X.B.I.GA) := by
    rw [hsplit, map_mul]
    congr 1
    exact Prod.ext h1 rfl
  obtain ⟨ψ, hψ⟩ := hrep u
  have hR : X.B.R (1, k') (Φ (X.B.tens (vecC X M c u))) = X.chi2 k' • Φ (X.B.tens (vecC X M c u)) := by
    obtain ⟨T0, -, rfl⟩ := hΦ
    have := congrArg (fun L => L (T0 (X.B.tens (vecC X M c u)))) (R_comp_Re X k' h2)
    simpa using this
  have a := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1, k') : X.B.I.GA)
  rw [hR] at a
  have key := congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X a (Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 k') hψ))
  rw [conjMap_apply, conjMap_apply, contRepL_spec X hψ, hι, key, Pi.smul_apply, smul_eq_mul, star_mul', ← hχ hk]
  rfl

end GlobalTheory.ConjRowMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesIsCuspFunStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateIntertwiner_values_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  first | exact @GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun | exact GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun | (intros; apply GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClassStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_of_heisenbergDerivativeClosedClass : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (V : Set (WO S T → ℂ)), (∀ f ∈ V, Continuous f) → (∀ f ∈ V, ∀ M : ℝ →+ WO S T, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ f' ∈ V, ∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (M t) f w) (f' w) 0) → ∀ f ∈ V, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t) := by
  first | exact @GlobalTheory.HeisSmooth.contDiff_of_heis_closed | exact GlobalTheory.HeisSmooth.contDiff_of_heis_closed | (intros; apply GlobalTheory.HeisSmooth.contDiff_of_heis_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
section
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem continuous_mat_pt (D : D7) (n : ℕ) : Continuous (mat : G D n → _) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mat_pt_inv (D : D7) (n : ℕ) : Continuous (fun g : G D n => mat g⁻¹) :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_of_mat_pt {D : D7} {n : ℕ} {X : Type} [TopologicalSpace X] {φ : X → G D n}
    (h : Continuous fun x => mat (φ x)) (h' : Continuous fun x => mat (φ x)⁻¹) : Continuous φ :=
  Continuous.subtype_mk (f := fun x => AdelicU.matHom _ D.sp.cm.sig (Jst D n) (φ x))
    (Units.continuous_iff.2 ⟨h, h'⟩) _

theorem chart_continuous : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → Continuous κ ∧ Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hT := (Tm_gram_inv D A μ hμ).2.1
  have h₁ : (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hT, rat_one]
  have h₂ : (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hT, rat_one]
  have e₁ : ∀ g, mat (κ g) = (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) *
      (Formalism.L2.Theta.mt (dblSp A) g * rat (Tm A μ)) := fun g => by
    rw [← hκ g, ← Matrix.mul_assoc, h₁, Matrix.one_mul]
  have e₂ : ∀ x, Formalism.L2.Theta.mt (dblSp A) (κ.symm x) =
      (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * mat x * rat (Tm A μ)⁻¹ := fun x => by
    have := hκ (κ.symm x)
    rw [κ.apply_symm_apply] at this
    rw [this]
    exact ((Matrix.mul_assoc _ _ _).trans ((congrArg _ h₂).trans (Matrix.mul_one _))).symm
  have c₁ : Continuous fun g => mat (κ g) := by
    simp only [e₁]
    exact continuous_const.matrix_mul ((continuous_mt (dblSp A)).matrix_mul continuous_const)
  refine ⟨continuous_of_mat_pt c₁ ?_, continuous_of_mt (dblSp A) ?_⟩
  · simp only [← map_inv]
    exact c₁.comp continuous_inv
  · simp only [e₂]
    exact (continuous_const.matrix_mul (continuous_mat_pt D A.rank)).matrix_mul continuous_const

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroupsStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSum_along_mulEquiv_subgroups : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (κ : G₁ ≃* G₂) (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂), (∀ g, g ∈ P₁ ↔ κ g ∈ P₂) → (∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) → ∀ (Φ₂ : G₂ → ℂ) (x : G₁) (c : ℂ) (Φ₁ : G₁ → ℂ), (∀ g, Φ₁ g = c * Φ₂ (κ (g * x))) → LeftInv (P₂ ⊓ Γ₂) Φ₂ → LeftInv (P₁ ⊓ Γ₁) Φ₁ ∧ ∀ g, (GlobalTheory.Eis.CosetConv P₂ Γ₂ Φ₂ (κ (g * x)) → GlobalTheory.Eis.CosetConv P₁ Γ₁ Φ₁ g) ∧ GlobalTheory.Eis.cosetSum P₁ Γ₁ Φ₁ g = c * GlobalTheory.Eis.cosetSum P₂ Γ₂ Φ₂ (κ (g * x)) := by
  first | exact @GlobalTheory.StdUnn.cosetSum_along_mulEquiv | exact GlobalTheory.StdUnn.cosetSum_along_mulEquiv | (intros; apply GlobalTheory.StdUnn.cosetSum_along_mulEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapEqZeroOfTranslatedEvalAeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormMap_eq_zero_of_translatedEval_ae_zero : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), IsInfFam θ → (∀ τ, (v₀ τ : M.H τ) ≠ 0) → ∀ T ∈ MultT θ M J χ, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 → T = 0 := by
  first | exact @GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae | exact GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae | (intros; apply GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_forms_rapid_decay : GlobalTheory.Published.CuspRapidDecay := by
  first | exact @GlobalTheory.RapidDecay.cuspRapidDecay | exact GlobalTheory.RapidDecay.cuspRapidDecay | (intros; apply GlobalTheory.RapidDecay.cuspRapidDecay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DerivativeClosedFunctionClassSmoothAndSchwartzStatement
section
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivativeClosedFunctionClass_smooth_and_schwartz : ∀ (k : ℕ) (V : Set ((Fin k → ℝ) → ℂ)), (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ x : Fin k → ℝ, HasDerivAt (fun t : ℝ => φ (x + t • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' x) 0) → (∀ φ ∈ V, ContDiff ℝ ∞ φ) ∧ ((∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖φ x‖ ≤ C) → ∀ φ ∈ V, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ x, g x = φ x) := by
  first | exact @GlobalTheory.Unf.PartialClass.smooth_schwartz | exact GlobalTheory.Unf.PartialClass.smooth_schwartz | (intros; apply GlobalTheory.Unf.PartialClass.smooth_schwartz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverseStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank ∧ IsUnit (Tm A μ).det ∧ (Tm A μ)⁻¹ = (Matrix.fromRows (dblDec A).qX (μ⁻¹ • (dblDec A).qY)).submatrix finSumFinEquiv.symm id := by
  first | exact @GlobalTheory.StdUnn.Tm_gram_inv | exact GlobalTheory.StdUnn.Tm_gram_inv | (intros; apply GlobalTheory.StdUnn.Tm_gram_inv <;> assumption)
end

