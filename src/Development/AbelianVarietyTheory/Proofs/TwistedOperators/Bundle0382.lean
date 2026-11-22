import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightLeOfNoShortVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0366
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothly
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsNeZeroOfIsMatch
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylConjugateParabolicLogModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerSurj

open GlobalTheory.MixModel (rat sandwich HypDec)
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition (isoPart midPart res IsIsoSplit)

variable {D : D7}

section Emb

variable {V V' H Z : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r)

def embMat : Matrix (Fin V.rank) (Fin H.rank) D.host.E := d.e * dH.qX + d.e' * dH.qY

theorem ee_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.e) = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.ee

theorem e'e'_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.e'ᴴ * (S.gram * d.e') = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.e'e'

theorem e'e_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.e'ᴴ * (S.gram * d.e) = 1 := by
  rw [← Matrix.mul_assoc]
  exact d.e'e

theorem ee'_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.e') = 1 := by
  have h := congrArg Matrix.conjTranspose d.e'e
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_one] at h
  exact h

theorem i₀e_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.i₀ᴴ * (S.gram * d.e) = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.i₀e

theorem i₀e'_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.i₀ᴴ * (S.gram * d.e') = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.i₀e'

theorem ei₀_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.i₀) = 0 := by
  have h := congrArg Matrix.conjTranspose d.i₀e
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_zero] at h
  exact h

theorem embMat_e : embMat d dH * dH.e = d.e := by
  have h1 := e'e_assoc dH
  have h0 := ee_assoc dH
  simp only [embMat, GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, Matrix.add_mul, Matrix.mul_assoc, h1, h0,
    Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem embMat_e' : embMat d dH * dH.e' = d.e' := by
  have h1 := ee'_assoc dH
  have h0 := e'e'_assoc dH
  simp only [embMat, GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, Matrix.add_mul, Matrix.mul_assoc, h1, h0,
    Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem iso_embMat : d.eᴴ * V.gram * embMat d dH = dH.eᴴ * H.gram := by
  have h1 : d.eᴴ * V.gram * d.e' = 1 := by
    rw [Matrix.mul_assoc]
    exact ee'_assoc d
  rw [embMat, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.ee, h1, Matrix.zero_mul, Matrix.one_mul,
    zero_add]
  rfl

theorem mid_embMat : d.i₀ᴴ * V.gram * embMat d dH = 0 := by
  rw [embMat, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.i₀e, d.i₀e', Matrix.zero_mul,
    Matrix.zero_mul, add_zero]

end Emb

section Form

variable {V V' H Z : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r) (W : HSp D)

theorem hO_rank_zero (hZ : Z.rank = 0) (x y : WO Z W) : hO Z W x y = 0 := by
  haveI : IsEmpty (Fin Z.rank) := by
    rw [hZ]
    infer_instance
  rw [GlobalTheory.MixModel.hO_eq_trace]
  simp [Matrix.trace]

theorem mul_embMat_jX (x : WO V W) : x * rat (embMat d dH) * dH.jX = x * d.jX := by
  rw [Matrix.mul_assoc]
  congr 1
  show rat (embMat d dH) * rat dH.e = rat d.e
  rw [← GlobalTheory.MixModel.rat_mul, embMat_e]

theorem mul_embMat_jY (x : WO V W) : x * rat (embMat d dH) * dH.jY = x * d.jY := by
  rw [Matrix.mul_assoc]
  congr 1
  show rat (embMat d dH) * rat dH.e' = rat d.e'
  rw [← GlobalTheory.MixModel.rat_mul, embMat_e']

theorem hO_split (hZ : Z.rank = 0) (x y : WO V W) :
    hO V W x y = hO V' W (x * rat d.i₀) (y * rat d.i₀) + hO H W (x * rat (embMat d dH)) (y * rat (embMat d dH)) := by
  rw [GlobalTheory.MixModel.HypDec.hO_coordS d, GlobalTheory.MixModel.HypDec.hO_coordS dH, hO_rank_zero W hZ,
    mul_embMat_jX d dH W x, mul_embMat_jX d dH W y, mul_embMat_jY d dH W x, mul_embMat_jY d dH W y]
  show _ = hO V' W (x * d.j0) (y * d.j0) + _
  abel

theorem symplOH_split (hZ : Z.rank = 0) (x y : WO V W) :
    symplOH V W x y =
      symplOH V' W (sandwich (rat 1) (rat d.i₀) x) (sandwich (rat 1) (rat d.i₀) y) +
        symplOH H W (sandwich (rat 1) (rat (embMat d dH)) x) (sandwich (rat 1) (rat (embMat d dH)) y) := by
  simp only [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul]
  rw [hO_split d dH W hZ, map_add]

end Form

section Res

variable {V V' H Z W : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r)

theorem sand_B (y : Mx D W.rank r) (x : WO V' W) :
    sandwich (rat 1) (rat d.i₀) (isoPart V W d.e y + midPart V V' W d.i₀ x) = x := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram).map (incA D) * rat d.i₀ = 0 := by
    show rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram) * rat d.i₀ = 0
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, ei₀_assoc d, GlobalTheory.MixModel.rat_zero]
  have h2 : (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram).map (incA D) * rat d.i₀ = 1 := by
    show rat (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram) * rat d.i₀ = 1
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.iso,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V'), GlobalTheory.MixModel.rat_one]
  rw [GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul, Matrix.add_mul]
  unfold isoPart midPart
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, Matrix.mul_one, zero_add]

theorem sand_A (y : Mx D W.rank r) (x : WO V' W) :
    sandwich (rat 1) (rat (embMat d dH)) (isoPart V W d.e y + midPart V V' W d.i₀ x) = isoPart H W dH.e y := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram).map (incA D) * rat (embMat d dH) =
      (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D dH.e * H.gram).map (incA D) := by
    show rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram) * rat (embMat d dH) = rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D dH.e * H.gram)
    rw [← GlobalTheory.MixModel.rat_mul, hadj, hadj, iso_embMat]
  have h2 : (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram).map (incA D) * rat (embMat d dH) = 0 := by
    show rat (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram) * rat (embMat d dH) = 0
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, mid_embMat,
      Matrix.mul_zero, GlobalTheory.MixModel.rat_zero]
  rw [GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul, Matrix.add_mul]
  unfold isoPart midPart
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, add_zero]

theorem surj_core (hZ : Z.rank = 0) (hsH : IsIsoSplit H Z dH.e dH.i₀) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsStdChar D ψ (-1)) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (hμ : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) (f' : WO V' W → ℂ) (hf' : IsThetaFunO ψ V' W f') :
    ∃ f, IsThetaFunO ψ V W f ∧ f' = res V V' W d.e d.i₀ μ 𝓨 f := by
  obtain ⟨fH, hfH, hne⟩ := (GlobalTheory.TowerRestrict.res_theta D H Z W r dH.e dH.i₀ hsH ψ hψ μ 𝓨 hμ).2
  generalize hcv : res H Z W dH.e dH.i₀ μ 𝓨 fH 0 = c
  have hc : c ≠ 0 := by
    rintro rfl
    apply hne
    funext z
    have hz : z = 0 := by
      haveI : IsEmpty (Fin Z.rank) := by
        rw [hZ]
        infer_instance
      exact Matrix.ext fun _ j => isEmptyElim j
    subst hz
    exact hcv
  have hint : ∫ y in 𝓨, fH (isoPart H W dH.e y) ∂μ = c := by
    rw [← hcv]
    simp only [res, GlobalTheory.TowerRestrict.midPart_zero, add_zero]
  refine ⟨fun w => f' (sandwich (rat 1) (rat d.i₀) w) * (c⁻¹ • fH) (sandwich (rat 1) (rat (embMat d dH)) w), ?_, ?_⟩
  · exact GlobalTheory.MixModel.isThetaFunO_prod 1 d.i₀ 1 (embMat d dH) (symplOH_split d dH W hZ) hf'
      (GlobalTheory.OrientedHeis.theta_smul c⁻¹ hfH)
  · funext x
    simp only [res, sand_B, sand_A, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, hint, inv_mul_cancel₀ hc, mul_one]

private theorem isIsoSplit_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (hρ : 0 < ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀ := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  refine ⟨⟨hρ, ?_, ?_⟩, ?_, ?_, d.rank_add.symm.trans (Nat.add_comm _ _ ▸ rfl)⟩
  · apply Fintype.linearIndependent_iff.2
    intro g hg
    have h1 : d.e.mulVec g = 0 := by
      funext k
      have hk := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, smul_eq_mul, Pi.zero_apply] at hk
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← hk]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 : (d.e'ᴴ * S.gram * d.e).mulVec g = 0 := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    rw [d.e'e, Matrix.one_mulVec] at h2
    exact fun i => congrFun h2 i
  · rw [GlobalTheory.MixModel.cT_sig]
    exact d.ee
  · rw [hadj]
    exact d.iso
  · rw [hadj, Matrix.mul_assoc]
    exact ei₀_assoc d

end Res

theorem res_surjective : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f', IsThetaFunO ψ V' W f' → ∃ f, IsThetaFunO ψ V W f ∧ f' = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 hμ f' hf'
  obtain ⟨d, hdC, hdB, -⟩ := GlobalTheory.T.exists_wittDecomposition_isotropicSplit_unipotent D V V' r C B hs
  subst hdC hdB
  exact surj_core d (GlobalTheory.Core.Rk.SWLaw.dblDec (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral r)) rfl
    (isIsoSplit_of_hypDec _ hs.frame.1) ψ hψ μ 𝓨 hμ f' hf'

end GlobalTheory.TowerSurj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAutomorphicConvolutionMemCuspidalOfRadica
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.RopCusp

theorem ropG_mem_L2cusp : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f ∈ CcGA V, RadicalIntegralsVanish V f → ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ := by
  intro D V μ _ _ f hf hR F
  obtain ⟨hfc, hfs⟩ := continuous_of_mem_ccAd hf
  obtain ⟨-, hc, hl, he⟩ := GlobalTheory.T.rightRegularOperator_represented_continuous D V μ f hf F
  refine mem_L2cusp_of_ae_eq ⟨hc, hl, (isCuspFun_iff hl).2 fun W hW => funext fun x => ?_⟩ he
  obtain ⟨hw1, hw2, hw3⟩ := GlobalTheory.T.constant_term_locally_integrable D V μ W hW F
  rw [hw3 f hfc hfs x, Pi.zero_apply]
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  have hcl : IsClosed ((NA (.single hW) : Subgroup (GA D V)) : Set (GA D V)) :=
    IsoFlag.isClosed_unip (IsoFlag.single hW) D.sp.cm _
  exact GlobalTheory.T.integral_mul_eq_zero_of_coset_integral_eq_zero_alt (GA D V) (NA (.single hW)) hcl (Measure.haar) μ (fun y => f (x⁻¹ * y)) _
    (hfc.comp (continuous_mul_left x⁻¹)) (hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹)) hw1 hw2
    fun g => by simpa only [mul_assoc] using hR _ (IsoFlag.proper_single hW) Measure.haar inferInstance x⁻¹ g

end GlobalTheory.RopCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFactorKernelStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_factor_kernel : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → (Z : Set I.H) = I.intKer ν) → ∀ h : 0 < I.a, (I.s ⟨0, h⟩).re ≤ (n : ℝ) - 1 := by
  first | exact @GlobalTheory.UnitaryBound.unitary_bound | exact GlobalTheory.UnitaryBound.unitary_bound | (intros; apply GlobalTheory.UnitaryBound.unitary_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissibleStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_irreducible_smooth_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NonarchimedeanGroup G] [LocallyCompactSpace G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : G →* (H →L[ℂ] H)), IsIrrUnitary π → (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional ℂ (fixed (toRep π) K)) → (smRep π).IsIrreducible ∧ IsAdmissible (smRep π) := by
  first | exact @GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep | exact GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep | (intros; apply GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightLeOfNoShortVectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuotientHeight_le_of_no_short_vector : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (b : ℕ), ∀ (g : GA D V) (t : ℝ), 0 < t → t ≤ 1 → (∀ ξ : Fin V.rank → D.host.E, ξ ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ)) → GlobalTheory.Grow.quotHeight V g * t ^ b ≤ C := by
  first | exact @GlobalTheory.HtMahler.quotHeight_le_of_no_short | exact GlobalTheory.HtMahler.quotHeight_le_of_no_short | (intros; apply GlobalTheory.HtMahler.quotHeight_le_of_no_short <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTypeLevelFamilyIsOpenLeLatticeStabilizerStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTypeLevelFamily_isOpen_le_latticeStabilizer : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ v, IsOpen (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) ∧ levelFam T U v ≤ Kv V v := by
  first | exact @GlobalTheory.TrIdem.levelFam_open_le | exact GlobalTheory.TrIdem.levelFam_open_le | (intros; apply GlobalTheory.TrIdem.levelFam_open_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanishStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ v : T.S, (μf v).IsHaarMeasure → ∀ (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), IsRegSS γ.1.1 → ε * ε = ε → γ.1.1 * ε = ε * γ.1.1 → 0 < ε.rank → ε.rank < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank ε.rank) → ∀ b : GLoc D.sp.cm.sig V.gram v → ℂ, Continuous b → LeftInv (cent (proj D.sp.cm.sig V.gram v (rat V γ))) b → (∀ g, ε.map (T.frame v).emb * ((splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1) * (1 - ε.map (T.frame v).emb) = (splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1 → ∀ x, b (g * x) = b x) → ∀ (dt : Measure (cent (proj D.sp.cm.sig V.gram v (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (proj D.sp.cm.sig V.gram v (rat V γ))) dt (μf v) (fun x => b x * ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x)) 0 := by
  first | exact @GlobalTheory.TwistLocal.weighted_orbital_vanish | exact GlobalTheory.TwistLocal.weighted_orbital_vanish | (intros; apply GlobalTheory.TwistLocal.weighted_orbital_vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothlyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOneParam_moves_fockVacuum_smoothly : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ T : ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ, (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ A : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) →
    A 0 = LinearMap.id →
    (∀ (t : ℝ) (p q : V) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β p q ⇑f →
      ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f)) →
    (∀ f x, Continuous fun t => T t f x) →
    ∀ J₀ : (V × V) →ₗ[ℝ] (V × V), (∀ w, J₀ (J₀ w) = -w) →
    ∀ f₀ : SchwartzMap V ℂ, (∀ w x, GlobalTheory.GaussLine.dHeis β (J₀ w) ⇑f₀ x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑f₀ x) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => T p.1 f₀ p.2) ∧
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ) (c : ℂ), ∀ x,
      HasDerivAt (fun t => T t f₀ x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ) * f₀ x + c * f₀ x) 0 := by
  first | exact @GlobalTheory.WeilVacuum.smooth_flow | exact GlobalTheory.WeilVacuum.smooth_flow | (intros; apply GlobalTheory.WeilVacuum.smooth_flow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationsForTriple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SquareComm.WeilOfTriple

theorem exists_weil_pair : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
      ∃ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA ∧ IsWeil ψ false W₁ X α (α / β) ωB := by
  intro hP D ψ hψ W W₁ X α β h
  obtain ⟨⟨ωA, hA⟩, ⟨ωB, hB⟩⟩ :=
    GlobalTheory.SquareSt.Model.exists_weil_of_isTriple hP.weilRepresentationUnitaryPair hψ h
  exact ⟨ωA, ωB, hA, hB⟩

end GlobalTheory.SquareComm.WeilOfTriple

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilThetaLevelPolynomialInHeightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilTheta_level_polynomial_in_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁),
    ∃ K₀ : Set (WO M X), K₀ ∈ nhds (0 : WO M X) ∧ IsCompact K₀ ∧ ∃ (m : ℝ) (e : ℕ), ∀ y ∈ C₁, ∀ h : GA D X,
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ m * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ e ∧
        ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) (ω (y, h) Φ) = ω (y, h) Φ := by
  first | exact @GlobalTheory.LevelGrowth.level_poly | exact GlobalTheory.LevelGrowth.level_poly | (intros; apply GlobalTheory.LevelGrowth.level_poly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylConjugateParabolicLogModulusStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_conjugate_parabolic_log_modulus : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GF V), Φ.IsWeylRep D.sp.cm π ε w → ∀ (j : Fin (wittIndex V)) (m : GA D V), m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) → rat V w * m * (rat V w)⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) ∧ logDelta Φ (stdVec j) (rat V w * m * (rat V w)⁻¹) = logDelta Φ (invSV π ε (stdVec j)) m := by
  first | exact @GlobalTheory.LeviShift.logDelta_conj_weylRep | exact GlobalTheory.LeviShift.logDelta_conj_weylRep | (intros; apply GlobalTheory.LeviShift.logDelta_conj_weylRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElementStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFrame_torus_eq_levi_element : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (M : HSp D) (r : ℕ)
    (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf →
    ∃ (S₀ : HSp D) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r), ∀ t : Fin r → ℝ, (∀ i, 0 < t i) →
      ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
        ∃ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 ∧
          (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) ∧ (ofSgn ε M).symm a = d.levi α := by
  first | exact @GlobalTheory.WittLevi.witt_levi | exact GlobalTheory.WittLevi.witt_levi | (intros; apply GlobalTheory.WittLevi.witt_levi <;> assumption)
end

