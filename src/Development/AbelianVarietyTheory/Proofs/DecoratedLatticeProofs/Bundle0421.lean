import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0400
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.StdUnn.CartanMove

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem compAt_mt_one (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) :
    compAt θ τ (Formalism.L2.Theta.mt V 1) = 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this]
  exact Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem compAt_mt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * h)) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V h) := by
  rw [mt_mul']
  exact GlobalTheory.AdForm.RatMove.compAt_mul θ τ _ _

theorem compAt_isom {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
  GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ

theorem isCartanInv_conj {k : ℕ} {G s P Pi : Matrix (Fin k) (Fin k) ℂ} (hs : IsCartanInv G s)
    (hPi : Pi * P = 1) (hPPi : P * Pi = 1) (hiso : Piᴴ * G * Pi = G) : IsCartanInv G (Pi * s * P) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hP : Pᴴ * G * P = G := by
    calc Pᴴ * G * P = Pᴴ * (Piᴴ * G * Pi) * P := by rw [hiso]
      _ = (Pi * P)ᴴ * G * (Pi * P) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGPi : G * Pi = Pᴴ * G := by
    calc G * Pi = (Pi * P)ᴴ * G * Pi := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = Pᴴ * (Piᴴ * G * Pi) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * G := by rw [hiso]
  refine ⟨?_, ?_, ?_⟩
  · calc Pi * s * P * (Pi * s * P) = Pi * s * (P * Pi) * s * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPPi, Matrix.mul_one, Matrix.mul_assoc Pi s s, h1, Matrix.mul_one, hPi]
  · calc (Pi * s * P)ᴴ * G * (Pi * s * P) = Pᴴ * (sᴴ * (Piᴴ * G * Pi) * s) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hiso, h2, hP]
  · have e : G * (Pi * s * P) = Pᴴ * (G * s) * P := by
      calc G * (Pi * s * P) = G * Pi * s * P := by simp only [Matrix.mul_assoc]
        _ = Pᴴ * (G * s) * P := by rw [hGPi]; simp only [Matrix.mul_assoc]
    rw [e]
    refine h3.conjTranspose_mul_mul_same ?_
    intro v w hvw
    have := congrArg (fun x => Pi.mulVec x) hvw
    simpa [Matrix.mulVec_mulVec, hPi] using this

end GlobalTheory.StdUnn.CartanMove
end

namespace GlobalTheory.StdUnn.CartanMove

open scoped ComplexOrder

theorem cartan_move_std : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ θ : InfFam D, IsInfFam θ → ∀ sS : RealMat (dblSp A), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (mt (dblSp A) k)) → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ τ, s' τ * compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) = compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) * sS τ := by
  intro D A μ hμ κ hκ a p hp θ hθ sS hsS hcomm
  obtain ⟨k₀, hk₀K, hk₀⟩ := GlobalTheory.T.exists_maximalCompactUnn_component_standardCartanInv D θ hθ A.rank μ hμ
  have hstd : IsStdInv A μ (fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))) := by
    intro τ
    have h := hκ (κ.symm k₀)
    rw [κ.apply_symm_apply k₀] at h
    have h2 := congrArg (compAt θ τ) h
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul] at h2
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [hr, hk₀] at h2
    exact h2.symm
  refine ⟨_, hstd, fun τ => ?_⟩
  dsimp only
  set k₁ := κ.symm k₀ with hk₁
  set P := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))) with hPdef
  set Pi := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))⁻¹) with hPidef
  set S1 := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k₁) with hS1
  have hPi : Pi * P = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, inv_mul_cancel, compAt_mt_one]
  have hPPi : P * Pi = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]
  have hmem : (p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
    rw [hp]
    have e : (p : GA D (dblSp A))⁻¹ * ((p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹) * (p : GA D (dblSp A)) = k₁ := by
      group
    rw [e, hk₁, κ.apply_symm_apply]
    exact hk₀K
  have hc := hcomm _ hmem τ
  rw [compAt_mt_mul, compAt_mt_mul] at hc
  have hcar' : IsCartanInv (gramAt D (dblSp A) τ) (Pi * sS τ * P) :=
    isCartanInv_conj (hsS τ) hPi hPPi (compAt_isom hθ _ _ τ)
  have hcar : IsCartanInv (gramAt D (dblSp A) τ) S1 := GlobalTheory.T.isCartanInv_standardInvolution_doubledGram D A μ hμ _ hstd τ
  have hcm : S1 * (Pi * sS τ * P) = Pi * sS τ * P * S1 := by
    calc S1 * (Pi * sS τ * P) = (Pi * P) * S1 * Pi * sS τ * P := by rw [hPi, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = Pi * (P * S1 * Pi * sS τ) * P := by simp only [Matrix.mul_assoc]
      _ = Pi * (sS τ * (P * S1 * Pi)) * P := by rw [hc]
      _ = Pi * sS τ * P * S1 * (Pi * P) := by simp only [Matrix.mul_assoc]
      _ = Pi * sS τ * P * S1 := by rw [hPi, Matrix.mul_one]
  have heq : S1 = Pi * sS τ * P := GlobalTheory.T.cartanInvolution_eq_of_commute _ _ _ _ hcar hcar' hcm
  rw [heq, Matrix.mul_assoc (Pi * sS τ) P Pi, hPPi, Matrix.mul_one]

end GlobalTheory.StdUnn.CartanMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateRowPairingPoincareSeriesBesselPeriods
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem perLaw_holds : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (Y : Formalism.L2.SG.Full.Full X), IsStdChar D ψ (-1) → InHH X u Y.hK → B.PerLaw Y := by
  intro D X h u ψ A B Y hψ hH
  obtain ⟨Fs, hFs⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratFund_holds X u
  obtain ⟨c, hc⟩ := GlobalTheory.T.unfoldedPeriod_eq_integral_besselPeriods D X h u ψ A B Y.hK hψ Fs hFs
  refine ⟨c, fun T f φ hf hφ => ?_⟩
  rw [GlobalTheory.T.inner_poincareSeries_eq_setIntegral_unfolding D X u Y.hK (Y.Dt u) Fs (Y.reps u) hH hFs T (hc T).1 f φ hf hφ]
  exact (hc T).2 f hf

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_flatMap_weilRepresentation_joint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) q.2.1 (om q.1 Φ) q.2.2 := by
  first | exact @GlobalTheory.FlatCont.flatAt_om_continuous | exact GlobalTheory.FlatCont.flatAt_om_continuous | (intros; apply GlobalTheory.FlatCont.flatAt_om_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatumListConsEqIdempotentTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.PutIn

theorem datJ_cons : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (i : ι) (J : List ι), i ∉ J → (∀ j ∈ J, (p i).e * (p j).e = 0) → GlobalTheory.FinPl.PutIn.datJ p α β Ψ (i :: J) = GlobalTheory.FinPl.PutIn.tens (p i).e (GlobalTheory.FinPl.PutIn.datJ p α β Ψ J) (extFun (α i) (β i) (Ψ i)) := by
  intro D k _ _ _ _ ι p n n' _ _ _ _ S T α β Ψ i J _ horth
  funext t
  have he : eSum p J * (p i).e = 0 := eSum_mul p _ J fun j hj => by rw [mul_comm]; exact horth j hj
  have hii : (p i).e * (p i).e = (p i).e := (p i).split.1

  have hhalf : IsHalf (eSum p (i :: J)) t ↔ IsHalf (eSum p J) (t - (p i).e • t) := by
    rw [eSum_cons]
    constructor
    · intro h a b
      have := h a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_sub, ← mul_assoc, he, zero_mul, sub_zero]
      linear_combination this
    · intro h a b
      have := h a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_sub, ← mul_assoc, he, zero_mul, sub_zero] at this
      linear_combination this
  have hself : IsHalf (p i).e ((p i).e • t) := by
    intro a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc, hii]
  have hrdi : rd (α i) (β i) ((p i).e • t) = rd (α i) (β i) t := by
    unfold rd
    congr 2
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, pr_e]
  have hrdj : ∀ j ∈ J, rd (α j) (β j) (t - (p i).e • t) = rd (α j) (β j) t := by
    intro j hj
    have h0 : (p j).pr (p i).e = 0 := pr_of_mul_eq_zero (p j) (by rw [mul_comm]; exact horth j hj)
    unfold rd
    congr 2
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_sub, h0]
  have hprod : (J.map fun j => Ψ j (rd (α j) (β j) (t - (p i).e • t))).prod = (J.map fun j => Ψ j (rd (α j) (β j) t)).prod := by
    congr 1
    exact List.map_congr_left fun j hj => by rw [hrdj j hj]
  simp only [datJ, tens, extFun, if_pos hself, hrdi, List.map_cons, List.prod_cons]
  by_cases h : IsHalf (eSum p J) (t - (p i).e • t)
  · rw [if_pos (hhalf.2 h), if_pos h, hprod, mul_comm]
  · rw [if_neg (fun h' => h (hhalf.1 h')), if_neg h, zero_mul]

end GlobalTheory.FinPl.PutIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DetIntegralUnitIdeleOfIntegralFinitePartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_integralUnitIdele_of_integral_finitePart : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)), finM V hn g = k.1 → (∀ i j, k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, (k⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det → finPart D (d : Formalism.L2.Theta.AE D) ∈ intAE D ∧ finPart D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ intAE D := by
  first | exact @GlobalTheory.DetIntUnit.det_int_unit | exact GlobalTheory.DetIntUnit.det_int_unit | (intros; apply GlobalTheory.DetIntUnit.det_int_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesModelHolomorphicPositiveSignsFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

open Formalism.IndefR.FWT GlobalTheory.HolDict

namespace GlobalTheory.HolLabel

theorem eq_self_of_strictMono {n : ℕ} {F K : Fin n → Fin n} (hK : StrictMono K) (hF : StrictMono F)
    (hFK : ∀ x, F (K x) = x) (x : Fin n) : K x = x :=
  le_antisymm ((hF.le_apply (x := K x)).trans_eq (hFK x)) hK.le_apply

theorem holShape_signs_first : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ), (∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ) → ∀ (i : Fin D.R.m) (M : DSModel (Wc D i) (Formalism.IndefR.Links.parAt (Wc D i) σ)), GlobalTheory.HolDict.HolShape M ∧ (∃ wt, GlobalTheory.HolDict.WtIs M wt) ∧ ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < pW D i ρ) := by
  intro D σ hσ i M
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
  have hp : ∀ ρ, Formalism.IndefR.Links.parAt (Wc D i) σ ρ =
      Formalism.L2.NTheta.holPar _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) := fun ρ => by
    unfold Formalism.IndefR.Links.parAt; rw [if_pos (hσ ρ)]
  have ho : ∀ ρ, Odd (((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2) := fun ρ => by
    rw [hpq ρ, hrk]; exact Formalism.L2.NTheta.odd_r _
  have hentL : ∀ ρ (c : Fin ((Wc D i).sig (tauE D ρ)).1),
      Formalism.L2.NTheta.holEnt _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) (Sum.inl c) =
        Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) (c : ℕ) := fun ρ c => by
    unfold Formalism.IndefR.Links.kapAt
    rw [Formalism.L2.NTheta.holEnt_kapW _ _ _ (ho ρ)]
    rfl
  have hentR : ∀ ρ (c : Fin ((Wc D i).sig (tauE D ρ)).2),
      Formalism.L2.NTheta.holEnt _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) (Sum.inr c) =
        Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) (((Wc D i).sig (tauE D ρ)).1 + (c : ℕ)) := fun ρ c => by
    unfold Formalism.IndefR.Links.kapAt
    rw [Formalism.L2.NTheta.holEnt_kapW _ _ _ (ho ρ)]
    rfl
  have heps : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < pW D i ρ) := by
    intro ρ
    obtain ⟨hanti, f, hf, hS⟩ := M.enum ρ
    rw [hp ρ] at hS
    have hpqρ := hpq ρ
    have hL := hentL ρ
    have hR := hentR ρ
    have hlt : ∀ m n : ℕ, m < n → n < (Wc D i).rank → Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n < Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) m := by
      intro m n hmn hn
      have h1 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc (Formalism.IndefR.Links.lab σ ρ)) (n - m) m (by omega)
      rw [show m + (n - m) = n by omega] at h1
      have h2 : (1 : ℚ) ≤ ((n - m : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ n - m)
      linarith
    have mem1 : ∀ a : Fin (Wc D i).rank, ∃ n : Fin (Wc D i).rank,
        f a = Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n ∧ M.ε ρ a = decide ((n : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
      intro a
      have hm : (f a, M.ε ρ a) ∈ Formalism.L2.NTheta.holPar ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) := by
        rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
      rcases x with c | c
      · simp only [hL, Sum.elim_inl, Prod.mk.injEq] at hx
        exact ⟨⟨c, by omega⟩, hx.1.symm, by rw [← hx.2]; exact (decide_eq_true c.2).symm⟩
      · simp only [hR, Sum.elim_inr, Prod.mk.injEq] at hx
        exact ⟨⟨((Wc D i).sig (tauE D ρ)).1 + c, by omega⟩, hx.1.symm, by rw [← hx.2]; exact (decide_eq_false (by simp)).symm⟩
    have mem2 : ∀ n : Fin (Wc D i).rank, ∃ a : Fin (Wc D i).rank,
        f a = Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n ∧ M.ε ρ a = decide ((n : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
      intro n
      have hm : ∀ x, (Formalism.L2.NTheta.holEnt ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) x,
          Sum.elim (fun _ => true) (fun _ => false) x) ∈ Finset.univ.image (fun a => (f a, M.ε ρ a)) := fun x => by
        rw [← hS]; unfold Formalism.L2.NTheta.holPar; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      by_cases hn : (n : ℕ) < ((Wc D i).sig (tauE D ρ)).1
      · obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hm (Sum.inl ⟨n, hn⟩))
        simp only [hL, Sum.elim_inl, Prod.mk.injEq] at ha
        exact ⟨a, ha.1, by rw [ha.2]; exact (decide_eq_true hn).symm⟩
      · obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hm (Sum.inr ⟨n - ((Wc D i).sig (tauE D ρ)).1, by omega⟩))
        simp only [hR, Sum.elim_inr, Prod.mk.injEq] at ha
        rw [show ((Wc D i).sig (tauE D ρ)).1 + (n - ((Wc D i).sig (tauE D ρ)).1) = n by omega] at ha
        exact ⟨a, ha.1, by rw [ha.2]; exact (decide_eq_false hn).symm⟩
    choose F hF1 hF2 using mem1
    choose K hK1 hK2 using mem2
    have fanti : ∀ a b : Fin (Wc D i).rank, a < b → f b < f a := fun a b hab => by
      have h1 := hanti hab
      rw [hf, hf] at h1
      exact_mod_cast h1
    have hFm : StrictMono F := fun a b hab => by
      have h1 := fanti a b hab
      rw [hF1 a, hF1 b] at h1
      by_contra hc
      rcases (not_lt.1 hc).lt_or_eq with hc | hc
      · exact lt_asymm h1 (hlt _ _ hc (F a).2)
      · rw [hc] at h1; exact lt_irrefl _ h1
    have hKm : StrictMono K := fun n m hnm => by
      have h1 := hlt _ _ hnm m.2
      rw [← hK1 n, ← hK1 m] at h1
      by_contra hc
      rcases (not_lt.1 hc).lt_or_eq with hc | hc
      · exact lt_asymm h1 (fanti _ _ hc)
      · rw [hc] at h1; exact lt_irrefl _ h1
    have hFK : ∀ n, F (K n) = n := fun n => by
      have h1 : Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) (F (K n)) = Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n := by rw [← hF1, hK1]
      rcases lt_trichotomy (F (K n)) n with hc | hc | hc
      · exact absurd h1 (hlt _ _ hc n.2).ne'
      · exact hc
      · exact absurd h1 (hlt _ _ hc (F (K n)).2).ne
    intro a
    have h1 := hK2 a
    rw [eq_self_of_strictMono hKm hFm hFK a] at h1
    exact h1
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) := fun ρ => by
    have he := M.enum ρ
    refine ⟨he.1, fun a => ?_⟩
    obtain ⟨-, f, hf, hS⟩ := he
    rw [hp ρ] at hS
    have hm : (f a, M.ε ρ a) ∈ Formalism.L2.NTheta.holPar _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
    have hx1 := congrArg Prod.fst hx
    have hn : (((Wc D i).rank : ℕ) : ℝ) = (((Wc D i).sig (tauE D ρ)).1 : ℝ) + ((Wc D i).sig (tauE D ρ)).2 := by
      rw [← hpq ρ]; push_cast; rfl
    dsimp only at hx1
    rw [hf a, ← hx1, hn]
    rcases x with c | c
    · refine ⟨Formalism.IndefR.Links.kapAt (Wc D i) σ ρ (Sum.inl c) - ((Wc D i).sig (tauE D ρ)).2 - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inl]
      push_cast
      ring
    · refine ⟨Formalism.IndefR.Links.kapAt (Wc D i) σ ρ (Sum.inr c) - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inr]
      push_cast
      ring
  refine ⟨fun ρ => ⟨hc ρ, _, (Nat.le_add_right _ _).trans (hpq ρ).le, heps ρ⟩, ?_, heps⟩
  choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ (M.ε ρ) _ (hc ρ).2 a
  exact ⟨fun ρ c => w ρ (revNeg (M.ε ρ) (arr (nNeg (M.ε ρ)) c)), fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.HolLabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralNegligibleOrbitsEqZeroCuspFormStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_integral_negligible_orbits_eq_zero_cuspForm : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = 0 := by
  first | exact @GlobalTheory.Core.Rk.NegOrbit.integral_neg_eq_zero | exact GlobalTheory.Core.Rk.NegOrbit.integral_neg_eq_zero | (intros; apply GlobalTheory.Core.Rk.NegOrbit.integral_neg_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapSpanDenseHeisenbergStable
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.DoubleSpan

variable {D : D7}

theorem span_delta_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A W : HSp D) :
    (Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂} :
      Submodule ℂ (WO (dblSp A) W → ℂ)) =
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan ((GlobalTheory.DoublingTheta.sumDec A (negSp A)).resS W) (IsThetaFunO ψ A W)
      (IsThetaFunO ψ (negSp A) W) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro φ ⟨f₁, f₂, h₁, h₂, rfl⟩
    refine Submodule.subset_span ⟨f₁, fun x => starRingEnd ℂ (f₂ (-x)), h₁,
      GlobalTheory.CjNeg.theta_negS hψ (GlobalTheory.NegWeil.theta_refl h₂), ?_⟩
    funext x
    exact (GlobalTheory.DoublingTheta.boxS_apply A W f₁ (fun x => starRingEnd ℂ (f₂ (-x))) x).symm
  · refine Submodule.span_le.2 ?_
    rintro φ ⟨g₁, g₂, h₁, h₂, rfl⟩
    refine Submodule.subset_span ⟨g₁, fun x => starRingEnd ℂ (g₂ (-x)), h₁,
      GlobalTheory.NegWeil.theta_refl (GlobalTheory.CjNeg.theta_negS' hψ h₂), ?_⟩
    funext x
    refine ((GlobalTheory.DoublingTheta.boxS_apply A W g₁ g₂ x).trans ?_)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, neg_neg, Complex.conj_conj]

theorem prodSpan_theta_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S A B : HSp D}
    (o : GlobalTheory.MixModel.OrthDec S A B) (W : HSp D) :
    (∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W), IsThetaFunO ψ S W g) ∧
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W), ∀ w,
      heisO ψ S W w g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W) := by
  refine ⟨fun g hg => ?_, fun g hg w => ?_⟩
  · induction hg using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hA, hB, rfl⟩ := hf
      exact o.isThetaFunO_boxS hA hB
    | zero => exact Formalism.IndefR.Fock.CCR.theta_zero ψ S W
    | add a b _ _ ha hb => exact Formalism.IndefR.Fock.CCR.theta_add ha hb
    | smul c a _ ha => exact Formalism.IndefR.Fock.CCR.theta_smul ha c
  · induction hg using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hA, hB, rfl⟩ := hf
      refine Submodule.subset_span ⟨_, _, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hA (o.resS W w).1,
        GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hB (o.resS W w).2, ?_⟩
      exact o.heisO_boxS ψ W fA fB w
    | zero =>
      have : heisO ψ S W w 0 = 0 := by funext x; simp [heisO]
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : heisO ψ S W w (a + b) = heisO ψ S W w a + heisO ψ S W w b := by
        funext x; simp only [heisO, Pi.add_apply]; ring
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : heisO ψ S W w (c • a) = c • heisO ψ S W w a := by
        funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact Submodule.smul_mem _ c ha

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A W : HSp D), IsStdChar D ψ (-1) → let M : Submodule ℂ (WO (dblSp A) W → ℂ) := Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂}; (∀ g ∈ M, IsThetaFunO ψ (dblSp A) W g) ∧ (∀ g ∈ M, ∀ w, heisO ψ (dblSp A) W w g ∈ M) ∧ ∀ f, IsThetaFunO ψ (dblSp A) W f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f := by
  intro D ψ A W hψ M
  have hM : M = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan ((GlobalTheory.DoublingTheta.sumDec A (negSp A)).resS W) (IsThetaFunO ψ A W)
      (IsThetaFunO ψ (negSp A) W) := span_delta_eq hψ A W
  obtain ⟨h1, h2⟩ := prodSpan_theta_heis hψ (GlobalTheory.DoublingTheta.sumDec A (negSp A)) W
  rw [hM]
  exact ⟨h1, h2, fun f hf =>
    GlobalTheory.DenseSum.unifLimit_prodSpan D ψ hψ _ A (negSp A) W (GlobalTheory.DoublingTheta.sumDec A (negSp A)) f hf⟩

end GlobalTheory.Core.Rk.DoubleSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingMap_thetaIdentity_any_weilData : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → IsWeilDatumO ψ (dblSp A) B 1 χB omh → ThetaClause ψ A B χB om omh := by
  first | exact @GlobalTheory.DoublingTheta.thetaClause | exact GlobalTheory.DoublingTheta.thetaClause | (intros; apply GlobalTheory.DoublingTheta.thetaClause <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteQuotientAnnihilatorStandardLatticeConjHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_quotient_annihilator_standardLattice_conjHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → ∃ r ∈ R, ∃ v : WO S T, IsHalf (cA D E₂) v ∧ (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x v) = 1) ∧ u = r + k • v := by
  first | exact @GlobalTheory.AnnConjHalf.ann_conj_half_finite | exact GlobalTheory.AnnConjHalf.ann_conj_half_finite | (intros; apply GlobalTheory.AnnConjHalf.ann_conj_half_finite <;> assumption)
end

