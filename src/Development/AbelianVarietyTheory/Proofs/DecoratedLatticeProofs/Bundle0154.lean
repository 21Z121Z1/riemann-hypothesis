import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapFactorIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

open scoped Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ContractionLocal

section Tens
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']

def colTens (φ : SB (n → k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := ⟨fun x => Ξ.1 x.toCols₁ * φ.1 (fun r => x r (Sum.inr ())), by
    haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n' ⊕ Unit)
    refine GlobalTheory.FinPl.Comm.prod_mem_SB Ξ.2 φ.2 (p := fun x : Matrix n (n' ⊕ Unit) k => x.toCols₁)
      (r := fun x r => x r (Sum.inr ())) (s := fun z => Matrix.fromCols z.1 (Matrix.of fun r _ => z.2 r))
      (by unfold Matrix.toCols₁; fun_prop) (continuous_pi fun r => by fun_prop) ?_ ?_
    · refine continuous_matrix fun i j => ?_
      rcases j with j | j
      · exact continuous_fst.matrix_elem i j
      · exact (continuous_apply i).comp continuous_snd
    · intro x
      ext i (j | j)
      · rfl
      · rfl⟩
  map_add' Ξ Ξ' := by ext x; simp [add_mul]
  map_smul' c Ξ := by ext x; simp [mul_assoc]

@[simp] theorem colTens_apply (φ : SB (n → k)) (Ξ : SB (Matrix n n' k)) (x : Matrix n (n' ⊕ Unit) k) :
    (colTens φ Ξ).1 x = Ξ.1 x.toCols₁ * φ.1 (fun r => x r (Sum.inr ())) := rfl

def rowTens (φ : SB (n → k)) : SB (Matrix n'' n k) →ₗ[ℂ] SB (Matrix (n'' ⊕ Unit) n k) where
  toFun Ξ := ⟨fun x => Ξ.1 x.toRows₁ * φ.1 (x (Sum.inr ())), by
    haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n'' ⊕ Unit) (n' := n)
    refine GlobalTheory.FinPl.Comm.prod_mem_SB Ξ.2 φ.2 (p := fun x : Matrix (n'' ⊕ Unit) n k => x.toRows₁)
      (r := fun x => x (Sum.inr ())) (s := fun z => Matrix.fromRows z.1 (Matrix.of fun _ => z.2))
      (by unfold Matrix.toRows₁; fun_prop) (continuous_pi fun j => continuous_id.matrix_elem _ j) ?_ ?_
    · refine continuous_matrix fun i j => ?_
      rcases i with i | i
      · exact continuous_fst.matrix_elem i j
      · exact (continuous_apply j).comp continuous_snd
    · intro x
      ext (i | i) j
      · rfl
      · rfl⟩
  map_add' Ξ Ξ' := by ext x; simp [add_mul]
  map_smul' c Ξ := by ext x; simp [mul_assoc]

@[simp] theorem rowTens_apply (φ : SB (n → k)) (Ξ : SB (Matrix n'' n k)) (x : Matrix (n'' ⊕ Unit) n k) :
    (rowTens φ Ξ).1 x = Ξ.1 x.toRows₁ * φ.1 (x (Sum.inr ())) := rfl

end Tens

section Bil
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (S : HSp D) : Continuous (l.κ S) := by
  unfold Link.κ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have h : Continuous fun w : WO S L' => giA S ⬝ (adj (rat l.τ ⬝ w) ⬝ gA B.L) :=
    Continuous.matrix_mul continuous_const (Continuous.matrix_mul
      (GlobalTheory.MixModel.continuous_adj.comp (continuous_const.matrix_mul continuous_id)) continuous_const)
  exact h.const_smul ((incA D) (-D.host.xi0⁻¹))

theorem integrable_contr (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {Ξ₁ : WO B.V₀ S → ℂ} {Ξ₂ : WO S B'.V₀ → ℂ}
    (h₁ : IsThetaFunO ψ B.V₀ S Ξ₁) (h₂ : IsThetaFunO ψ S B'.V₀ Ξ₂) (u : WO B.A S) (v : WO S B'.A) :
    Integrable (fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)))
      (vL.μ.restrict vL.𝓕) := by
  haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₁ h₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₂ h₂
  have hc : Continuous fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) :=
    (h₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp (Continuous.prodMk continuous_const continuous_id))).mul
      (h₁.cont.comp ((OrthDec.continuous_resS_symm _ _).comp
        (Continuous.prodMk continuous_const (continuous_kappa l S))))
  refine (integrable_const (C₂ * C₁)).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC₂ _) (hC₁ _) (norm_nonneg _) ((norm_nonneg _).trans (hC₂ 0))

def contrBil (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (T₁ : M₁ →ₗ[ℂ] (WO B.V₀ S → ℂ)) (T₂ : M₂ →ₗ[ℂ] (WO S B'.V₀ → ℂ))
    (h₁ : ∀ Φ, IsThetaFunO ψ B.V₀ S (T₁ Φ)) (h₂ : ∀ Φ, IsThetaFunO ψ S B'.V₀ (T₂ Φ)) :
    M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] (WO B.A S → WO S B'.A → ℂ) :=
  LinearMap.mk₂ ℂ (fun Ψ₁ Ψ₂ => GlobalTheory.Unf.contr l S vL (T₁ Ψ₁) (T₂ Ψ₂))
    (fun a a' b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_contr hψ l S vL (h₁ a) (h₂ b) u v)
        (integrable_contr hψ l S vL (h₁ a') (h₂ b) u v))
    (fun c a b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]; congr 1; funext w; ring)
    (fun a b b' => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_contr hψ l S vL (h₁ a) (h₂ b) u v)
        (integrable_contr hψ l S vL (h₁ a) (h₂ b') u v))
    (fun c a b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]; congr 1; funext w; ring)

@[simp] theorem contrBil_apply (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (T₁ : M₁ →ₗ[ℂ] (WO B.V₀ S → ℂ)) (T₂ : M₂ →ₗ[ℂ] (WO S B'.V₀ → ℂ))
    (h₁ : ∀ Φ, IsThetaFunO ψ B.V₀ S (T₁ Φ)) (h₂ : ∀ Φ, IsThetaFunO ψ S B'.V₀ (T₂ Φ)) (Ψ₁ : M₁) (Ψ₂ : M₂) :
    contrBil hψ l S vL T₁ T₂ h₁ h₂ Ψ₁ Ψ₂ = GlobalTheory.Unf.contr l S vL (T₁ Ψ₁) (T₂ Ψ₂) := rfl

end Bil

end GlobalTheory.ContractionLocal

namespace GlobalTheory.ContractionLocal

theorem exists_normPair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψk : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψk)
    (hν : ν.IsAddHaarMeasure) (n : Type) [Fintype n] [DecidableEq n] :
    ∃ φ₀ φ₀' : SB (n → k), ∫ u, φ₀'.1 u * GlobalTheory.StepData.hat ψk ν (-1) φ₀.1 u ∂(Measure.pi fun _ => ν) = 1 := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := hν
  haveI := GlobalTheory.SplitWeil.secondCountable k
  let L := GlobalTheory.LatPair.stdLat k n
  have hc := GlobalTheory.FinPl.Comm.fpair_ne_zero ψk hψ (-1) (Or.inr rfl) (Measure.pi fun _ => ν) L
  set c := GlobalTheory.FinPl.Comm.fpair ψk (-1) (Measure.pi fun _ => ν) (GlobalTheory.FinPl.vecInd L) (GlobalTheory.FinPl.dualInd L)
  refine ⟨⟨_, GlobalTheory.FinPl.Comm.vecInd_mem L⟩, c⁻¹ • ⟨_, GlobalTheory.FinPl.Comm.dualInd_mem L⟩, ?_⟩
  have e : c = ∫ u, (GlobalTheory.FinPl.dualInd L u) * GlobalTheory.StepData.hat ψk ν (-1) (GlobalTheory.FinPl.vecInd L) u
      ∂(Measure.pi fun _ => ν) := by
    simp only [c, GlobalTheory.FinPl.Comm.fpair, GlobalTheory.StepData.hat]
    congr 1; funext u; ring
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul, ← e, inv_mul_cancel₀ hc]

theorem contr_tens {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψk : AddChar k Circle) (ν : Measure k)
    {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (φ₀ φ₀' : SB (n → k)) (Ξ₁ : SB (Matrix n n' k)) (Ξ₂ : SB (Matrix n'' n k)) (q : Matrix n n' k × Matrix n'' n k) :
    GlobalTheory.LocFlat.contr ψk ν (colTens φ₀ Ξ₁).1 (rowTens φ₀' Ξ₂).1 q =
      Ξ₁.1 q.1 * Ξ₂.1 q.2 * ∫ u, φ₀'.1 u * GlobalTheory.StepData.hat ψk ν (-1) φ₀.1 u ∂(Measure.pi fun _ => ν) := by
  simp only [GlobalTheory.LocFlat.contr, colTens_apply, rowTens_apply, Matrix.toCols₁_fromCols, Matrix.toRows₁_fromRows,
    GlobalTheory.StepData.hat]
  rw [← integral_const_mul]
  congr 1; funext u
  have h1 : (Matrix.fromRows q.2 (Matrix.of fun _ : Unit => u)) (Sum.inr ()) = u := rfl
  have h2 : ∀ y : n → k, (fun r => Matrix.fromCols q.1 (Matrix.of fun r (_ : Unit) => y r) r (Sum.inr ())) = y :=
    fun y => rfl
  simp only [h1, h2]
  rw [show (∫ y, Ξ₁.1 q.1 * φ₀.1 y * ((ψk ((-1) * (u ⬝ᵥ y)) : Circle) : ℂ) ∂(Measure.pi fun _ => ν)) =
      Ξ₁.1 q.1 * ∫ y, φ₀.1 y * ((ψk ((-1) * (u ⬝ᵥ y)) : Circle) : ℂ) ∂(Measure.pi fun _ => ν) by
    rw [← integral_const_mul]; congr 1; funext y; ring]
  ring
end GlobalTheory.ContractionLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueCompletionMatrixOfRationalTwistAutStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_completionMatrix_of_rationalTwistAut : ∀ (X : Fields) (R : Ranks) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (j c : ℕ), c = cOf R j → ∀ γ : AutY X R j, ∃! g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin c) k, IsGL ι γ g := by
  first | exact @GlobalTheory.TwBridge.existsUnique_isGL | exact GlobalTheory.TwBridge.existsUnique_isGL | (intros; apply GlobalTheory.TwBridge.existsUnique_isGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstStepCompletionRepresentativesEqOneStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstStep_completionRepresentatives_eq_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ c (h : 0 + c = s), {g : GL (XIx (Fin R.k) (Fin R.t) (0) ⊕ Fin (c + 1)) k | ∃ b : L.β 0, IsGL ι (L.h 0 b P) g} = {1} := by
  first | exact @GlobalTheory.TwBridge.ZeroReps.reps_zero | exact GlobalTheory.TwBridge.ZeroReps.reps_zero | (intros; apply GlobalTheory.TwBridge.ZeroReps.reps_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapFactorIsLocalModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_bessel_flatMap_factor_isLocalModel : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (T₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix (n ⊕ Unit) n' k)), Ψ.1 = GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ.1 → flatFB st (Tm Φ) = T₀ Ψ) → p.IsModel ψ G₀ F₀ T₀ := by
  first | exact @GlobalTheory.LocFlatFB.factor_isModel | exact GlobalTheory.LocFlatFB.factor_isModel | (intros; apply GlobalTheory.LocFlatFB.factor_isModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapRowMultiplicationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_bessel_flatMap_row_multiplication : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s', r = Sum.inr l ∧ σ < l.val ∧ q = Sum.inl s') → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatFB st (Tm Φ') = flatFB st (Tm Φ) := by
  first | exact @GlobalTheory.LocMod.flatFB_mulrow | exact GlobalTheory.LocMod.flatFB_mulrow | (intros; apply GlobalTheory.LocMod.flatFB_mulrow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapUnipotentLawStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_bessel_flatMap_unipotent_law : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ u : GL (Fin c) k, embA n u ∈ N k n c (σ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → flatFB st (Tm Φ') = (ψk (-simpleSum (embA n u)) : ℂ) • flatFB st (Tm Φ) := by
  first | exact @GlobalTheory.FlatFBUnip.unip_law | exact GlobalTheory.FlatFBUnip.unip_law | (intros; apply GlobalTheory.FlatFBUnip.unip_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiHandOff_automorphic : ∀ D : D7, HandFBLaw D := by
  first | exact @GlobalTheory.handFBLaw | exact GlobalTheory.handFBLaw | (intros; apply GlobalTheory.handFBLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingCharIndicatorDualLatticeCosetsStatement
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierPairing_charIndicator_dualLattice_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n), fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red) = fpair χ e μ (vecInd Q.lat) (dualInd Q.lat) := by
  first | exact @GlobalTheory.FinPl.Comm.DualCosets.fpair_charInd_dualInd_add_cosets | exact GlobalTheory.FinPl.Comm.DualCosets.fpair_charInd_dualInd_add_cosets | (intros; apply GlobalTheory.FinPl.Comm.DualCosets.fpair_charInd_dualInd_add_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierTransformCosetIndicatorEqFiniteColumnTranStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTransform_cosetIndicator_eq_finiteColumnTransform : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → 2 * cst.M ≤ cst.D P →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e →
    ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))), (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' l)) →
      hat W.ψ ν (-1) (cosetInd (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun a => ι (y' (e' a)))) ((toLoc ι e e' y) (Sum.inr ())) =
        σ₀ (ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y') := by
  first | exact @GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY | exact GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY | (intros; apply GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumDoublingInert
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.DoublingSumU

set_option maxHeartbeats 1000000 in

theorem hasSum_doubling_inert : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ χ : Lˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ m : ℕ, ((χ ϖ : ℂˣ) : ℂ) = (-1) ^ m → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q (χ ϖ) s) α) → (∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g)) ∧ HasSum (fun a : GU σ n ⧸ KU σ n => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n a.out) * ℓ (ρ a.out x)) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL q n α (χ ϖ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac q n m s * ℓ x) := by
  intro hD L _ _ _ ϖ σ q n hU χ hχ m hm s Φ hΦ V _ _ ρ x α hx ℓ hℓ hdom
  have hright : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) := by
    intro g k hk
    obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := GlobalTheory.ZetaSumU.cartan_complete L (ϖ : L) σ q n hU g
    rw [mul_assoc (a * t) b k, GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha _ (mul_mem hb hk),
      GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha b hb]
  refine ⟨hright, ?_⟩
  obtain ⟨h0, h1⟩ := GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal L ϖ σ q n hU V ρ x α hx ℓ hℓ
  by_cases hx0 : ℓ x = 0
  · simp only [h0 hx0, hx0, mul_zero]
    exact hasSum_zero
  · have hw := h1 hx0
    letI : MeasurableSpace (GU σ n) := borel _
    haveI : BorelSpace (GU σ n) := ⟨rfl⟩
    obtain ⟨μ, hμH, hμK⟩ := GlobalTheory.ZetaSumU.exists_haar (ϖ : L) hU n
    have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1
    obtain ⟨hint, -, hval⟩ := (hD L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α _ hw).1 (hdom hx0)
    have hval' := hval m hm
    have hF : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) * (ℓ (ρ (g * k) x) / ℓ x) =
        Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x) := fun g k hk => by
      have h2 := hw.1 1 ⟨k, hk⟩ g
      simp only [OneMemClass.coe_one, one_mul] at h2
      rw [hright g k hk, h2]
    have hs := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ hF hint).of_norm
    have hci := (GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) hKo hμK
      (fun g => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x)) _ hF hs.hasSum).2
    have hS := hs.hasSum
    rw [← hci, hval'] at hS
    have h3 := hS.mul_right (ℓ x)
    simpa only [mul_assoc, div_mul_cancel₀ _ hx0] using h3

end GlobalTheory.DoublingSumU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLaws
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf.SupFin

theorem supSob_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D), (∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k f ≠ ⊤) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), (∀ U : AddSubgroup (WO S T), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, dRho (heisO ψ S T) θ τ z f ∈ GlobalTheory.Size.thetaLevel ψ S T U) ∧ ∃ C : ℝ≥0, ∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k (dRho (heisO ψ S T) θ τ z f) ≤ C * supSob ψ θ (k + 1) f) ∧ ∀ k (f g : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → supSob ψ θ k (f + g) ≤ supSob ψ θ k f + supSob ψ θ k g ∧ supSob ψ θ k (c • f) = ‖c‖ₑ * supSob ψ θ k f := by
  intro D ψ hψ θ hθ S T
  have ha : ∀ g g' : WO S T → ℂ, (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (g + g') ≤
      (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g + (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g' :=
    GlobalTheory.Size.SupWord.supN_add_le
  have hs : ∀ (c : ℂ) (g : WO S T → ℂ), (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (c • g) =
      ‖c‖ₑ * (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g := GlobalTheory.Size.SupWord.supN_smul
  refine ⟨fun k f hf => ?_, fun τ z => ⟨fun U f hf => GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ hf τ z, ?_⟩,
    fun k f g c hf hg => ⟨GlobalTheory.Size.SupWord.ws_add_le hψ hθ ha hf hg k, GlobalTheory.Size.SupWord.ws_smul hs k c f⟩⟩
  · refine GlobalTheory.Size.wordSum_ne_top_iff.2 fun l _ => ?_
    obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.Size.theta_word hψ hθ l hf)
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup_le fun w => ?_)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hC w)
  · refine ⟨Real.toNNReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)), fun k f hf => ?_⟩
    exact GlobalTheory.Size.SupWord.ws_dRho_le hψ hθ ha hs hf τ z k

end GlobalTheory.Unf.SupFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableSchwartzMajorantPullbackUnitriangular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
namespace GlobalTheory.Unf

theorem pull_integrable : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m ρ : ℕ) (vU : VolU D ρ) (x : Matrix (Fin m) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∃ N : ℕ, ∀ K : Set (Mx D m ρ), IsCompact K → Integrable (fun u : UX D ρ => maj θ K N ((rat x : Mx D m ρ) ⬝ u.1.1)) vU.ν := by
  intro D θ hθ m ρ vU x hx
  have hH : vU.ν.IsHaarMeasure := vU.unit.1
  obtain ⟨hf, hfin, hinv⟩ := GlobalTheory.T.haar_adelicUpperUnitriangular_entry_translate_invariant D ρ vU.ν hH
  have hae : ∀ᵐ y ∂(Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) vU.ν), ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j := by
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
    have hS : MeasurableSet {y : Mx D ρ ρ | ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j} := by
      have hc : IsClosed {y : Mx D ρ ρ | ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
      exact hc.measurableSet
    rw [ae_map_iff hf.aemeasurable hS]
    refine ae_of_all _ fun u i j hij => ?_
    have hU := (GlobalTheory.UniIndexPrime.mem_uniSub u.1).1 u.2
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [Matrix.one_apply_ne h.ne']
      exact hU.1 i j h
    · subst h
      rw [Matrix.one_apply_eq]
      exact hU.2 _
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_majorant_coordinate_coset_measure D θ hθ ρ ρ (fun i j => i < j) 1 _ hfin hae hinv
  obtain ⟨hmaj, hmove⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ
  refine ⟨N, fun K hK => ?_⟩
  obtain ⟨K', hK', hb⟩ := hmove m ρ ρ x hx K hK
  obtain ⟨C, hC⟩ := hb N
  have h1 : Integrable (maj θ K' N) (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) vU.ν) := hN K' hK'
  have h2 : Integrable (fun u : UX D ρ => maj θ K' N (u.1.1 : Mx D ρ ρ)) vU.ν :=
    (integrable_map_measure ((hmaj ρ ρ K' hK').2.2.1 N).aestronglyMeasurable hf.aemeasurable).1 h1
  have hmul : Measurable (fun y : Mx D ρ ρ => (rat x : Mx D m ρ) ⬝ y) := by
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : BorelSpace (Mx D m ρ) := ⟨rfl⟩
    exact (continuous_const.matrix_mul continuous_id).measurable
  refine (h2.const_mul C).mono' (((hmaj m ρ K hK).2.2.1 N).comp (hmul.comp hf)).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (maj_nonneg θ K N _)]
  exact hC _

end GlobalTheory.Unf
end

