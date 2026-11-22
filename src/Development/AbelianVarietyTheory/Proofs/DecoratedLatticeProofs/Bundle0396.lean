import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0366
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedPeriodEqIntegralBesselPeriods
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Core.MiFold

open scoped ENNReal

variable {D : D7}

theorem mul_mem_sfin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) {n : X.B.I.Gf} (hn : n ∈ X.NfinU u)
    {g : X.B.I.Gf} (hg : g ∈ Hfin X u) : n * g ∈ SfinU X u := by
  have hfix : ∀ y ∈ fixSet X u, X.B.I.fmat g *ᵥ incl X.B.I y = incl X.B.I y := hg
  have hm : X.B.I.fmat (n * g) = X.B.I.fmat n * X.B.I.fmat g := by simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : ∀ y ∈ fixSet X u,
      (X.B.I.fmat (n * g) - 1) *ᵥ incl X.B.I y = (X.B.I.fmat n - 1) *ᵥ incl X.B.I y := by
    intro y hy
    rw [hm, Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hfix y hy]
  refine ⟨fun a => ?_, ?_⟩
  · rw [key _ (Or.inl (Or.inl ⟨a, rfl⟩))]; exact hn.1 a
  · rw [key _ (Or.inr rfl)]; exact hn.2.1

theorem ph_supp (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (x : X.B.I.GA)
    (hx : Ph X u hK T x ≠ 0) : ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k := by
  unfold Ph at hx
  split_ifs at hx with hd
  · obtain ⟨n, g, k, hdec⟩ := hd
    obtain ⟨hn, hk, he⟩ := hdec
    exact ⟨n * (g : X.B.I.Gf), mul_mem_sfin X u hn g.2, k, hk, he⟩
  · exact absurd rfl hx

end GlobalTheory.Core.MiFold

namespace GlobalTheory.Core.MiFold

open scoped ENNReal

variable {D : D7}

theorem norm_psiBes {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (n : GA D S) : ‖psiBes ψ d θ z n‖ = 1 := by
  simp only [psiBes, psiE]; exact hψ.2.1 _

theorem iota_mul_assoc (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ s : GA D (D.sp.Y 0)) (y : X.B.I.Ginf) (x : X.B.I.Gf) :
    iotaX X h (γ * s) * (y, x) = iotaX X h γ * (iotaX X h s * (y, x)) := by
  rw [map_mul]
  exact mul_assoc _ _ _

end GlobalTheory.Core.MiFold

set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.MiFold in

theorem GlobalTheory.Core.Mi.unfoldedPer : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter), IsStdChar D ψ (-1) → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℂ, ∀ (T : Cu X u hK), IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) ∧ ∀ f : X.B.I.GA → ℂ, RowFun X f → ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) = c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u) := by
  intro D X h u ψ A B hK hψ Fs hFs
  obtain ⟨-, -, -, 𝓢, h𝓢, h𝓢fin, hI⟩ := GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D D.R.rS B.lev
  obtain ⟨c, hc, hQ⟩ := GlobalTheory.T.fold_integral_besselQuotient_supportedFunctions D X h u ψ A B 𝓢 h𝓢 Fs hFs
  refine ⟨(c : ℂ), fun T => ?_⟩
  have hPh := Formalism.L2.SG.PoincareInHH.Cut.phProps_closed X u hK (Formalism.L2.SG.Pf.ksetSplit_holds X u)
    (Formalism.L2.SG.Pf.unipotent_in_level X u) (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u) T
  have hgrp := GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B
  have hph := GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T

  set Φ : X.B.I.Ginf → besGrp B.d B.o → X.B.I.GA := fun y s => iotaX X h s.1 * (y, X.xu u) with hΦdef
  have hι : Continuous fun s : besGrp B.d B.o => iotaX X h s.1 := (iotaX X h).continuous.comp continuous_subtype_val
  have hΦ : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun p : X.B.I.Ginf × besGrp B.d B.o => (iotaX X h p.2.1).1 * p.1 :=
      ((continuous_fst.comp hι).measurable.comp measurable_snd).mul measurable_fst
    have h2 : Measurable fun p : X.B.I.Ginf × besGrp B.d B.o => (iotaX X h p.2.1).2 * X.xu u :=
      ((continuous_snd.comp hι).measurable.comp measurable_snd).mul_const _
    exact h1.prodMk h2

  obtain ⟨C, hC⟩ := GlobalTheory.T.bessel_column_scalar_form_norm_bound D X h u ψ A B hK T
  have hbd : ∀ y (s : besGrp B.d B.o), ‖Ph X u hK T (Φ y s)‖ ≤ C * ‖X.Wu u y‖ := by
    intro y s
    obtain ⟨n, hn, a, ha⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o s.1).1 s.2
    simp only [hΦdef, ha, hph.2 n hn a y, norm_mul, norm_star, norm_psiBes hψ.1, one_mul]
    exact hC _ _
  have hWu : ∫⁻ y, ‖X.Wu u y‖ₑ ∂(X.nuQ u) < ⊤ := (X.Wu_spec u).2.2.2.1
  have hfin : ∀ K : ℝ, 0 ≤ K → ∀ G : X.B.I.GA → ℂ, (∀ x, ‖G x‖ ≤ K * ‖Ph X u hK T x‖) →
      ∫⁻ y, ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ∂(X.nuQ u) < ⊤ := by
    intro K hK0 G hG
    have hpt : ∀ y (s : besGrp B.d B.o), ‖G (Φ y s)‖ₑ ≤ ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ := by
      intro y s
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ((hG _).trans ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ((hbd y s).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))) hK0
    calc ∫⁻ y, ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ∂(X.nuQ u)
        ≤ ∫⁻ y, B.lev.μR 𝓢 * (ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ) ∂(X.nuQ u) := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ≤ ∫⁻ s in 𝓢, ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ ∂B.lev.μR :=
                lintegral_mono fun s => hpt y s
            _ = _ := by rw [setLIntegral_const, mul_comm]
      _ = B.lev.μR 𝓢 * ENNReal.ofReal (K * |C|) * ∫⁻ y, ‖X.Wu u y‖ₑ ∂(X.nuQ u) := by
          rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top h𝓢fin.ne ENNReal.ofReal_ne_top)]
          simp only [mul_assoc]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top h𝓢fin ENNReal.ofReal_lt_top) hWu

  set P : (X.B.I.GA → ENNReal) → Prop := fun F => (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) ∧
    (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) ∧
    (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) with hPdef
  have hQ' : ∀ F : X.B.I.GA → ENNReal, Measurable F → P F →
      ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (Φ y s) ∂B.lev.μR ∂(X.nuQ u) :=
    fun F hF hP => hQ F hF hP.1 hP.2.1 hP.2.2
  have hsupp : ∀ G : X.B.I.GA → ℂ, (∀ x, G x ≠ 0 → Ph X u hK T x ≠ 0) → ∀ φ : ℂ → ENNReal, φ 0 = 0 →
      ∀ x, φ (G x) ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k := by
    intro G hG φ hφ x hx
    refine ph_supp X u hK T x (hG x ?_)
    intro h0; rw [h0, hφ] at hx; exact hx rfl
  have hchi : ∀ k ∈ X.K2, ‖X.chi2 k‖ = 1 := hK.2.2.2.2

  have hint : IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) := by
    refine ⟨hPh.1.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hQ' (fun x => ‖Ph X u hK T x‖ₑ) hPh.1.enorm ⟨fun γ hγ x => by dsimp only; rw [hPh.2.1 γ hγ x],
      fun k hk x => by dsimp only; rw [hPh.2.2.1 x k hk, enorm_mul, ← ofReal_norm_eq_enorm (X.chi2 k), hchi k hk,
        ENNReal.ofReal_one, one_mul],
      hsupp (Ph X u hK T) (fun x hx => hx) (fun z => ‖z‖ₑ) enorm_zero⟩]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin 1 zero_le_one _ fun x => by rw [one_mul])
  refine ⟨hint, fun f hf => ?_⟩
  obtain ⟨Cf, hCf⟩ := hf.bdd
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 1)
  have hfm : Measurable f := hf.cont.measurable

  obtain ⟨G, hGdef⟩ : ∃ G : X.B.I.GA → ℂ, G = fun x => f x * Ph X u hK T x := ⟨_, rfl⟩
  have hGl : ∀ γ ∈ Srat X u, ∀ x, G (γ * x) = G x := by
    intro γ hγ x
    simp only [hGdef, hPh.2.1 γ hγ x, hf.left γ (Subgroup.mem_inf.1 hγ).1 x]
  have hGr : ∀ k ∈ X.K2, ∀ x, G (x * (1, k)) = G x := by
    intro k hk x
    have h1 : star (X.chi2 k) * X.chi2 k = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hchi k hk]; norm_num
    simp only [hGdef, hPh.2.2.1 x k hk, hf.right k hk x]
    calc star (X.chi2 k) * f x * (X.chi2 k * Ph X u hK T x) = (star (X.chi2 k) * X.chi2 k) * (f x * Ph X u hK T x) := by ring
      _ = _ := by rw [h1, one_mul]
  have hGs : ∀ x, G x ≠ 0 → Ph X u hK T x ≠ 0 := fun x hx h0 => hx (by simp only [hGdef, h0, mul_zero])
  have hGm : Measurable G := by rw [hGdef]; exact hfm.mul hPh.1
  have hGb : ∀ x, ‖G x‖ ≤ Cf * ‖Ph X u hK T x‖ := fun x => by
    rw [hGdef, norm_mul]; exact mul_le_mul_of_nonneg_right (hCf x) (norm_nonneg _)
  obtain ⟨-, hfold⟩ := GlobalTheory.T.integral_fold_via_lintegral_formula (X.B.I.muA X.B.μf) Fs (X.nuQ u) B.lev.μR 𝓢 h𝓢fin Φ hΦ c hc.le P hQ' G hGm
    (fun φ hφ => ⟨fun γ hγ x => by simp only [hGl γ hγ x], fun k hk x => by simp only [hGr k hk x],
      hsupp G hGs φ hφ⟩) (hfin Cf hCf0 G hGb)
  rw [show (∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf)) = ∫ x in Fs, G x ∂(X.B.I.muA X.B.μf) by rw [hGdef], hfold]
  subst hGdef
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)

  have hcont : ContinuousOn (fun g => f (iotaX X h g * (y, X.xu u)) * Ph X u hK T (iotaX X h g * (y, X.xu u)))
      (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := by
    refine ContinuousOn.mul ?_ (GlobalTheory.T.bessel_column_function_continuousOn_bessel_group D X h u ψ A B hK T y hψ.1)
    exact (hf.cont.comp ((iotaX X h).continuous.mul continuous_const)).continuousOn
  have hinv : ∀ γ ∈ GQ (D.sp.Y 0) ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o,
      f (iotaX X h (γ * s) * (y, X.xu u)) * Ph X u hK T (iotaX X h (γ * s) * (y, X.xu u)) =
        f (iotaX X h s * (y, X.xu u)) * Ph X u hK T (iotaX X h s * (y, X.xu u)) := by
    intro γ hγ s _
    have hγ' := (hgrp.2 γ).1 hγ
    have := hGl _ hγ' (iotaX X h s * (y, X.xu u))
    dsimp only at this
    exact (congrArg (fun z => f z * Ph X u hK T z) (iota_mul_assoc X h γ s y (X.xu u))).trans this
  have hIy := (hI _ hcont hinv).2
  refine hIy.trans ?_
  simp only [BesLev.per, besPer, besFun]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [hph.2 n.1 n.2 a y]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeyl
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Gen
open GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : ∃ a b c d, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [blk4, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem rel {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) :
    -(adj c * a) + adj a * c = 0 ∧ -(adj c * b) + adj a * d = 1 ∧ -(adj d * b) + adj b * d = 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [JR_Jst, hg] at h
  simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h
  exact ⟨(blockMatrixTwoByTwoFin_injective h).1, (blockMatrixTwoByTwoFin_injective h).2.1, (blockMatrixTwoByTwoFin_injective h).2.2.2⟩

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Mx D n n), mat g = blk4 1 b 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Mx D n n} (hg : mat g = blk4 a b 0 d) (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) u⁻¹
  have h1 : (adj u.1 : Mx D n n) * d = 1 := by simpa using (rel hg).2.1
  rw [← S.mul_mem_cancel_left (hm m _ hmm)]
  refine hn _ ((u⁻¹).1 * b) ?_
  rw [mat_mul, hmm, hg, submatrix_fromBlocks_mul]
  simp only [inv_inv, Units.inv_mul, mul_zero, zero_mul, add_zero, zero_add, h1]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Mx D n n} (hg : mat g = blk4 a 0 c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have h1 : (adj u.1 : Mx D n n) * b = adj b * u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h2 : (adj (u⁻¹).1 : Mx D n n) * adj u.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
  have h3 : (adj (-(b * (u⁻¹).1)) : Mx D n n) = -(b * (u⁻¹).1) := by
    rw [adj_neg, adj_mul]
    congr 1
    calc (adj (u⁻¹).1 : Mx D n n) * adj b = adj (u⁻¹).1 * (adj b * u.1) * (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      _ = b * (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  rw [← S.mul_mem_cancel_left (hn x _ hx)]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]

end GlobalTheory.StdUnn.Gen

namespace GlobalTheory.StdUnn

theorem eq_top_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (GlobalTheory.StdUnn.G D n)), (∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 a.1 0 0 (GlobalTheory.MixModel.adj (a⁻¹).1) → g ∈ S) → (∀ (g : GlobalTheory.StdUnn.G D n) (b : Mx D n n), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b 0 1 → g ∈ S) → (∀ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 → g ∈ S) → S = ⊤ := by
  intro D n S hm hn hw
  rw [eq_top_iff]
  intro g _
  obtain ⟨a, b, c, d, hg⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g)
  obtain ⟨p', p, q', q, hi⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g⁻¹)
  have h1 : mat g * mat g⁻¹ = 1 := by rw [← Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hg, hi, Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_isUnit D n c d p q (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  obtain ⟨y, hy⟩ := (Model.exists_unip x).2 hx
  rw [← S.mul_mem_cancel_right (hn y _ hy)]
  refine Gen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [Gen.mat_mul, hg, hy, Model.submatrix_fromBlocks_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.StdUnn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeCharAtUniformizerIdeleEqValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocUnifVal

theorem valued_eq_of_unif {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (ϖ : (Fv D.host.F v)ˣ)
    (hϖ : ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) = ValuativeRel.uniformizer (Fv D.host.F v)) :
    Valued.v (ϖ : Fv D.host.F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have key : ∀ a b : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) a ≤ ValuativeRel.valuation (Fv D.host.F v) b ↔
      Valued.v a ≤ Valued.v b := fun a b =>
    (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (Fv D.host.F v)) a b).symm.trans
      (Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)))) a b)
  have hlt : Valued.v (ϖ : Fv D.host.F v) < 1 := by
    have h1 : ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) < ValuativeRel.valuation (Fv D.host.F v) 1 := by
      rw [map_one, hϖ]; exact ValuativeRel.uniformizer_lt_one
    rw [← map_one (Valued.v : Valuation (Fv D.host.F v) _)]
    exact lt_of_not_ge fun h => (not_le.2 h1) ((key _ _).2 h)
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer D.host.F
  have hx : Valued.v (algebraMap D.host.F (Fv D.host.F v) π) = WithZero.exp (-1 : ℤ) := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, hπ]
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : Fv D.host.F v) := by
    rw [← hx]
    refine (key _ _).1 ?_
    rw [hϖ, ValuativeRel.le_uniformizer_iff, ← map_one (ValuativeRel.valuation (Fv D.host.F v))]
    refine lt_of_not_ge fun h => ?_
    have := (key _ _).1 h
    rw [map_one, hx] at this
    exact absurd this (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  have h0 : Valued.v (ϖ : Fv D.host.F v) ≠ 0 := (map_ne_zero _).2 ϖ.ne_zero
  rw [← WithZero.exp_log h0] at hlt hle ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hle
  congr 1
  omega

theorem value_eq_val : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ χ : (AE D)ˣ →* Circle, GlobalTheory.LFun.UnrAt (F := D.host.F) χ PP → Circle.toUnits (χ x) = GlobalTheory.LFun.val (F := D.host.F) χ PP := by
  intro D v φ PP hφ x ϖ hloc χ hχ
  obtain ⟨e, he, hx1, hx2, hx3⟩ := hloc
  have h : PP.under (𝓞 D.host.F) = v := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1.symm
  have hAt : Formalism.L2.NTheta.IsIdemAt e PP := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  have hP : IsPrimeIdem PP e (e + cA D e) := Or.inl ⟨hAt, rfl⟩
  have hxe : e * ((x : AE D) - 1) = (x : AE D) - 1 := by linear_combination -hx1
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) x hxe
  have hτ : GlobalTheory.AdelicU.splitPrime (GlobalTheory.SplitProjChart.emb φ) = PP := (GlobalTheory.ResLift.eq_splitPrime hφ).symm
  have hc : (y : PP.adicCompletion D.host.E) = GlobalTheory.LFun.complMap h (ϖ : Fv D.host.F v) := by
    have e1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D (x : AE D)) =
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (x : AE D) := by
      rw [GlobalTheory.FinPl.LatMem.compFin_eq_compAt]; rfl
    rw [hy, GlobalTheory.LFun.compAt_apply, GlobalTheory.LFun.finAdEquiv_apply h, e1,
      GlobalTheory.LFun.ConjPlace.toCompl_eq (GlobalTheory.AdelicU.isCMExt_host D) h hτ, GlobalTheory.SplitProjChart.splitProj_emb, ← hx2]
    rfl
  have hu : Formalism.L2.Host.IsUnifAt PP y := by
    unfold Formalism.L2.Host.IsUnifAt
    rw [hc, GlobalTheory.LFun.ConjPlace.valued_complMap (GlobalTheory.AdelicU.isCMExt_host D) h hτ]
    exact GlobalTheory.LocUnifVal.valued_eq_of_unif ϖ hx3
  have := hχ.locChar_eq_val hu
  rw [← this, hxy]
  rfl

end GlobalTheory.LocUnifVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientPureTensorEqSmulInner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.WeilCoefScalar

theorem integrableOn_mul_conj {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) {ν : Measure (WO S T)}
    {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕) :
    IntegrableOn (fun w => f w * conj (g w)) 𝓕 ν := by
  refine GlobalTheory.MixModel.covolOne_integrableOn hν _
    (hf.cont.mul (Complex.continuous_conj.comp hg.cont)) ?_
  rintro _ ⟨γ, rfl⟩ a
  have e1 := hf.quasi γ a
  have e2 := hg.quasi γ a
  have hn : ∀ x, conj (ψ x) * ψ x = 1 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1 x]; norm_num
  change f (ratW T S γ + a) * conj (g (ratW T S γ + a)) = f a * conj (g a)
  rw [e1, e2, map_mul]
  linear_combination (f a * conj (g a)) * hn (-symplOH S T (ratW T S γ) a)

end GlobalTheory.WeilCoefScalar

namespace GlobalTheory.WeilCoefScalar

theorem wcoef_pure_eq_smul_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z * ⟪w, (R.cV i).ρ b w⟫_ℂ) ∧ ∀ w : (R.cV i).W, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 → z ≠ 0 := by

  intro D G _ _ Pl0 T A Ks _ _ _ R F hC _hF i t v ν 𝓕 hν
  have hc : (R.cV i).Is := hC.models.cV i
  have hW := hC.thP.ωP i t
  have hio := (hC.thP.ioP i t).1
  let J : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
      (onb (R.MW i (sg0 D A))) (R.vP i t)).comp (R.ioP i (PiTensorProduct.tprod ℂ v))
  have hJ : ∀ x, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) x) = J x := fun x => rfl
  have hth : ∀ x, IsThetaFunO R.ψ (Vc D i) (Wc D i) (J x) := fun x => hC.thP.pt_theta i t _
  have hint : ∀ x y, IntegrableOn (fun w => J y w * conj (J x w)) 𝓕 ν := fun x y =>
    integrableOn_mul_conj hW.std (hth y) (hth x) hν
  let B : (R.cV i).W →ₗ⋆[ℂ] (R.cV i).W →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ w in 𝓕, J y w * conj (J x w) ∂ν)
      (fun x x' y => by
        simp only [map_add, Pi.add_apply, mul_add]
        exact integral_add (hint x y) (hint x' y))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
      (fun x y y' => by
        simp only [map_add, Pi.add_apply, add_mul]
        exact integral_add (hint x y) (hint x y'))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
  have hB : ∀ x y, B x y = ∫ w in 𝓕, J y w * conj (J x w) ∂ν := fun x y => rfl
  have hom : ∀ u ∈ GinfC (Vc D i), ∀ x, R.ωP i t (u, 1) (J x) = J ((R.cV i).ρ u x) := fun u hu x => by
    rw [← hJ, ← hJ]; exact hio u hu _ x
  have hinv : ∀ u ∈ GinfC (Vc D i), ∀ x y, B ((R.cV i).ρ u x) ((R.cV i).ρ u y) = B x y := by
    intro u hu x y
    rw [hB, hB, ← hom u hu x, ← hom u hu y]
    exact GlobalTheory.Mem.LiftPolar.scalar_eq D R.ψ hW.std _ _ ν 𝓕 hν.1 hν.2.1 (R.ωP i t (u, 1))
      (fun f hf => hW.om_pres _ f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 _ f hf) (J y) (J x) (hth y) (hth x)
  obtain ⟨z, hz⟩ := GlobalTheory.T.real_invariant_sesquilinear_form_eq_smul_inner D (Vc D i) (R.cV i) hc B hinv
  refine ⟨z, fun w b hb => ?_, fun w hw hz0 => ?_⟩
  · rw [hJ, ← hz, hB, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hom b hb w]
  · rw [hJ] at hw
    have h1 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std (hth w) hw hν
    apply h1
    have h2 := hz w w
    rw [hz0, zero_mul, hB] at h2
    rw [GlobalTheory.RawLift.thetaIP, ← h2]
    congr 1; funext x
    rw [Complex.star_def, mul_comm]

end GlobalTheory.WeilCoefScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WordElementConjOrthProjHyperbolicNegativeSpanEqStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordElement_conj_orthProjHyperbolicNegativeSpan_eq : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : VA X.B.I), X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y) = ∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a + ∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) := by
  first | exact @GlobalTheory.ScalW.Conj.prj_conj | exact GlobalTheory.ScalW.Conj.prj_conj | (intros; apply GlobalTheory.ScalW.Conj.prj_conj <;> assumption)
end

