import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AdmissiblePeriodOfPeriodInt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HypOver
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParametersStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shiftedAdditiveCharacter_archimedeanParameters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∃ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ IsCharAF D.host.F (shift ψ lam) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ lam) θ l ∧ ∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖ := by
  first | exact @GlobalTheory.StdUnn.shift_char_realPar | exact GlobalTheory.StdUnn.shift_char_realPar | (intros; apply GlobalTheory.StdUnn.shift_char_realPar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelAdaptedCharAbs
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

noncomputable section

namespace GlobalTheory.Core.Rk.SecPar

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar

open GlobalTheory.LFun

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar
open GlobalTheory.LFun

theorem cw_incA {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = q)
    (x : D.host.E) : cw h (incA D x) = algebraMap D.host.E (w.adicCompletion D.host.E) x := by
  show toCompl h (compFin _ _ q (1 ⊗ₜ x)) = _
  simp [compFin, toCompl]

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar
open GlobalTheory.LFun

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar
open GlobalTheory.LFun

end GlobalTheory.Core.Rk.SecPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewAdjointSimilitudeExchangesHalvesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewAdjointSimilitude_exchanges_halves : ∀ (D : D7) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (e : AE D) (y : WO S L''), (IsHalf (cA D e) y → IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) ∧ (IsHalf e y → IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) := by
  first | exact @GlobalTheory.KappaHalf.ofAdj_rat_mul_half | exact GlobalTheory.KappaHalf.ofAdj_rat_mul_half | (intros; apply GlobalTheory.KappaHalf.ofAdj_rat_mul_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSectionGraphSplitPlaceStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalSection_graph_splitPlace : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (e : Gv A v ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)), IsSplitChart D.sp.cm.sig A.gram L h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin A.rank → ℤ) (t : GL (Fin A.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w A.rank, ∀ k₂ ∈ KGL w A.rank, φ (ioAt A v (e.symm (k₁ * t * k₂))) = (((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV D.host.E w : ℂ) ^ (-((A.rank : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) := by
  first | exact @GlobalTheory.Core.Rk.KerSplit.sphSec_split | exact GlobalTheory.Core.Rk.KerSplit.sphSec_split | (intros; apply GlobalTheory.Core.Rk.KerSplit.sphSec_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFormHalfSkewAdjointImageStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_hermitianForm_half_skewAdjointImage : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (s : k) (z₀ : Fin L''.rank → k), s ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * s)) • (fun i => p.pr (ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : Frame k S.rank n) (FL : Frame k L.rank Unit) (FL'' : Frame k L''.rank Unit), (∀ r, FL.β r () = s * p.pr (ζ r)) → (∀ r, FL''.β r () = z₀ r) → ∀ (x : Matrix Unit n k) (a : Matrix n Unit k), p.π (hO L S (p.up FL FS a) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * p.up FS FL'' x))) = -(∑ r, x () r * a r ()) := by
  first | exact @GlobalTheory.KappaSplitPairing.key | exact GlobalTheory.KappaSplitPairing.key | (intros; apply GlobalTheory.KappaSplitPairing.key <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineColumnTranslationHeisenberg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrFrameCol

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule GlobalTheory.KappaHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul_rat (p : Place D k) {l m r : ℕ} (N : Matrix (Fin r) (Fin l) k) (M : Matrix (Fin l) (Fin m) D.host.E) :
    (N.map p.ι : Mx D r l) * rat M = (N * M.map p.pr).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, rat, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, BoxModel.incA_mul_ι, mul_comm]

theorem qB_β (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V₀.rank (n ⊕ Unit)) (h : p.IsCoreFrame B s FA F) :
    B.o.qB.map p.pr * F.β = fromCols 0 (Matrix.of fun r _ => s * p.pr (B.ζ r)) := by
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), M.map p.pr = M.map (BoxModel.prH p) :=
    fun _ => rfl
  ext r c
  rcases c with a | ⟨⟨⟩⟩
  · have : (B.o.qB.map p.pr * F.β) r (Sum.inl a) = (B.o.qB.map p.pr * (B.o.iA.map p.pr * FA.β)) r a := by
      simp only [Matrix.mul_apply (M := B.o.qB.map p.pr), h.1]
    rw [this, ← Matrix.mul_assoc, ← BoxModel.map_pr_mul, B.o.qB_iA, hm]
    simp
  · have h1 : B.o.qB *ᵥ vecB B.o B.ζ = B.ζ := by
      rw [vecB, Matrix.mulVec_mulVec, B.o.qB_iB, Matrix.one_mulVec]
    have h2 : p.pr (B.ζ r) = ∑ j, p.pr (B.o.qB r j) * p.pr (vecB B.o B.ζ j) := by
      conv_lhs => rw [← h1]
      change BoxModel.prH p (∑ j, B.o.qB r j * vecB B.o B.ζ j) = ∑ j, BoxModel.prH p _ * BoxModel.prH p _
      simp only [map_sum, map_mul]
    rw [fromCols_apply_inr, Matrix.of_apply, h2, Finset.mul_sum, Matrix.mul_apply]
    simp only [h.2, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem line_γ_iA (p : Place D k) {n m : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V₀.rank (n ⊕ Unit)) (h : p.IsCoreFrame B s FA F)
    (y : Matrix m Unit k) :
    fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr = 0 := by
  have h1 : fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr * FA.β = 0 := by
    ext r a
    have : (fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr * FA.β) r a
        = (fromCols (0 : Matrix m n k) y * F.γ * F.β) r (Sum.inl a) := by
      rw [Matrix.mul_assoc (_ * F.γ)]
      simp only [Matrix.mul_apply (M := fromCols (0 : Matrix m n k) y * F.γ), h.1]
    rw [this, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    simp
  rw [← Matrix.mul_one (_ * B.o.iA.map p.pr), ← FA.βγ, ← Matrix.mul_assoc, h1, Matrix.zero_mul]

theorem xi_mul_hO (L S : HSp D) (Y : WO L S) (z : Mx D L.rank S.rank) :
    incA D D.host.xi0 * hO L S Y (ofAdj L S z) = (z * Y).trace := by
  conv_rhs => rw [← starAdj_ofAdj L S z]
  rw [hO_eq_trace, starAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem link_frames (p : Place D k) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (s : k)
    {n' n'' : Type} [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) (h' : p.IsCoreFrame B' (s * p.xi) FA' F₀') :
    B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * F₀'.β))
      = F₀.β * (Matrix.single (Sum.inr ()) (Sum.inr ()) (-p.xi) : Matrix (n' ⊕ Unit) (n'' ⊕ Unit) k) := by
  rw [qB_β p B' _ FA' F₀' h', ← Matrix.mul_assoc, ← BoxModel.map_pr_mul]
  have h1 : (B.o.iB * l.τ) *ᵥ B'.ζ = -vecB B.o B.ζ := by
    rw [← Matrix.mulVec_mulVec, l.map, Matrix.mulVec_neg, vecB]
  ext r c
  rcases c with a | ⟨⟨⟩⟩
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · have h2 : ∑ j, p.pr ((B.o.iB * l.τ) r j) * p.pr (B'.ζ j) = -p.pr (vecB B.o B.ζ r) := by
      have := congrArg (fun v => BoxModel.prH p (v r)) h1
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.neg_apply, map_neg] at this
      exact this
    have h3 : (F₀.β * (Matrix.single (Sum.inr ()) (Sum.inr ()) (-p.xi) : Matrix (n' ⊕ Unit) (n'' ⊕ Unit) k)) r (Sum.inr ())
        = F₀.β r (Sum.inr ()) * -p.xi := by
      simp [Matrix.mul_apply, Matrix.single_apply]
    rw [h3, h.2, Matrix.mul_apply]
    simp only [fromCols_apply_inr, Matrix.of_apply, Matrix.map_apply]
    calc _ = s * p.xi * ∑ j, p.pr ((B.o.iB * l.τ) r j) * p.pr (B'.ζ j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [h2]; ring

theorem frame_col : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ y₀ : n → k, ∃ x : WO S B'.L, p.up F₀ FS (fromCols 0 (Matrix.of fun r _ => y₀ r)) = (B.o.resS S).symm (0, l.κ S x) ∧ IsHalf (cA D p.e) ((B'.o.resT S).symm (0, x)) ∧ ∀ t : Matrix (n'' ⊕ Unit) n k, ψ (symplO S B'.V₀ (p.up FS F₀' t) ((B'.o.resT S).symm (0, x))) = ((ψk (-(t (Sum.inr ()) ⬝ᵥ y₀)) : Circle) : ℂ) := by
  intro D k _ _ _ _ p ψ hψ ψk hk ρ σ B B' l S s _ n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' h h' y₀
  have hxi : p.xi ≠ 0 := (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.1
  have hτ : l.τ ≠ 0 := by
    intro h0
    have h1 := l.map
    rw [h0, Matrix.zero_mulVec, eq_comm, neg_eq_zero] at h1
    exact B.line.2 (by rw [h1, Matrix.mulVec_zero, dotProduct_zero])
  obtain ⟨τi, -, hi⟩ := LinkGram.exists_inv_of_rank_one B.line.1 B'.line.1 l.τ hτ
  set M : Matrix n (n' ⊕ Unit) k := fromCols 0 (Matrix.of fun r _ => y₀ r) with hM
  set Y : WO B.L S := p.up F₀ FS M * B.o.jB with hY
  have hYh : IsHalf p.e Y := isHalf_mul_right _ (GlobalTheory.LocSympl.up_half p F₀ FS M)
  have hκ : l.κ S (rat τi * starAdj B.L S Y) = Y := by
    rw [Link.κ, ← Matrix.mul_assoc, ← rat_mul, hi, rat_one, Matrix.one_mul, LinkGram.ofAdj_starAdj]
  refine ⟨rat τi * starAdj B.L S Y, ?_, ?_, fun t => ?_⟩
  · rw [hκ, AddEquiv.eq_symm_apply, OrthDec.resS_apply]
    refine Prod.ext ?_ rfl
    change (FS.β * M * F₀.γ).map p.ι * rat B.o.iA = 0
    rw [ι_mul_rat, Matrix.mul_assoc FS.β, Matrix.mul_assoc FS.β, hM, line_γ_iA p B s FA F₀ h]
    simp
  · rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact isHalf_mul_left _ (isHalf_mul_left _ (isHalf_smul _ (isHalf_mul_left _
      (isHalf_mul_right _ (isHalf_cA_adj hYh)))))
  · rw [GlobalTheory.LocSympl.psi_sympl_up p FS F₀' ψ ψk hk, OrthDec.hO_resT _ S, AddEquiv.apply_symm_apply,
      OrthDec.resT_apply]
    have hg := (LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
    have h0 : ∀ u : WO S B'.A, hO S B'.A u 0 = 0 := fun u => by
      rw [hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero]
    have h1 := GlobalTheory.LinkKappa.hO_ofAdj B.L B'.L S l.τ _ hg (rat τi * starAdj B.L S Y)
      (B'.o.pB * p.up FS F₀' t)
    rw [Int.cast_one, map_one, one_mul] at h1
    change hO B.L S (l.κ S _) _ = _ at h1
    rw [hκ] at h1
    have h2 := congrArg p.π (xi_mul_hO B.L S Y (rat l.τ * (B'.o.pB * p.up FS F₀' t)))
    rw [h1, map_mul] at h2
    have h3 : p.π (rat l.τ * (B'.o.pB * p.up FS F₀' t) * Y).trace = p.xi * -(t (Sum.inr ()) ⬝ᵥ y₀) := by
      have e1 : rat l.τ * (B'.o.pB * p.up FS F₀' t)
          = (l.τ.map p.pr * (B'.o.qB.map p.pr * (F₀'.β * t * FS.γ))).map p.ι := by
        rw [← BoxModel.rat_mul_ι, ← BoxModel.rat_mul_ι]; rfl
      have e2 : Y = (FS.β * M * F₀.γ * B.o.iB.map p.pr).map p.ι := by
        rw [← ι_mul_rat]; rfl
      have e3 : ∀ {a b : ℕ} (N : Matrix (Fin a) (Fin b) k), (N.map p.ι).map p.π = N := fun N => by
        ext i j; exact p.π_ι _
      rw [AddMonoidHom.map_trace p.π, Matrix.map_mul, e1, e2, e3, e3, ← Matrix.mul_assoc _ _ (B.o.iB.map p.pr),
        Matrix.trace_mul_comm]
      have e4 : B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * (F₀'.β * t * FS.γ)) * (FS.β * M * F₀.γ))
          = (B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * F₀'.β))) * (t * (FS.γ * FS.β) * M) * F₀.γ := by
        simp only [Matrix.mul_assoc]
      rw [e4, link_frames p B B' l s FA F₀ FA' F₀' h h', FS.γβ, Matrix.mul_one, Matrix.trace_mul_comm,
        ← Matrix.mul_assoc F₀.γ, ← Matrix.mul_assoc F₀.γ F₀.β, F₀.γβ, Matrix.one_mul, Matrix.trace_single_mul]
      simp [hM, Matrix.mul_apply, dotProduct]
    rw [h3] at h2
    rw [h0, zero_add, mul_left_cancel₀ hxi h2]

end GlobalTheory.ContrFrameCol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartBlockDiagonalEqLeviStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryChart_blockDiagonal_eq_levi : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (g : GA D (dblSp A)) (a : GL (Fin A.rank) (AE D)), mat (κ g) = blk4 a.1 0 0 (adj (a⁻¹).1) → g = (dblDec A).levi a := by
  first | exact @GlobalTheory.StdUnn.chart_levi | exact GlobalTheory.StdUnn.chart_levi | (intros; apply GlobalTheory.StdUnn.chart_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartUnipotentEqWittUnipotentStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryChart_unipotent_eq_wittUnipotent : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (g : GA D (dblSp A)) (b : Mx D A.rank A.rank), mat (κ g) = blk4 1 b 0 1 → ∃ c : skewA D A.rank, c.1 = incA D μ⁻¹ • b ∧ g = (dblDec A).nC c := by
  first | exact @GlobalTheory.ChartUnip.chart_unip | exact GlobalTheory.ChartUnip.chart_unip | (intros; apply GlobalTheory.ChartUnip.chart_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartWeylElementRationalStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryChart_weylElement_rational : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g : GA D (dblSp A), mat (κ g) = blk4 0 1 (-1) 0 → IsWeyl A g ∧ mt (dblSp A) g ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) ∧ mt (dblSp A) g ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX := by
  first | exact @GlobalTheory.StdUnn.chart_weyl | exact GlobalTheory.StdUnn.chart_weyl | (intros; apply GlobalTheory.StdUnn.chart_weyl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TPeriodInt
section
noncomputable section

namespace GlobalTheory.Core.Int.Inhab

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ NumberField IsDedekindDomain GlobalTheory.Core.Int GlobalTheory.Core.Int.Model
  GlobalTheory.Core.RkFamModel

set_option maxHeartbeats 1600000 in

abbrev recOne : D7 :=
  letI := (Ht 0).cmStar
  hostLevelRecord (Ht 0) (W := Unit) () (fun _ _ => hcA 0) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h) (fun _ _ => false) (fun _ _ _ => rfl)
    (fun _ _ l h => by
      have := exampleWeight_middle_entries l h
      simp only [Bool.false_eq_true, if_false, sub_zero]
      simp only [hcA, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_zero]
      exact this)
    (fun _ _ => 1) (fun _ _ => one_pos) (fun _ => 1) (fun _ => one_pos) 0 (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
    (fun _ => oneCls 1 one_pos) (fun _ => T0) (dstarOf T0) (dstarOf_pos T0) (fun _ => 1) (fun _ => one_pos) 2 one_lt_two
    (fun _ => exampleLevel_near_lower Tau0 T0) exampleHost_type_primes_split (tH 0) (fun _ => examplePrime_mem_levelPrimes) (fun _ => examplePrime_ne_split_primes) (fun _ => π0O)
    (fun _ => π0_mem_K) (fun _ => π0_norm) (fun _ => π0_cong)
    (fun _ i _ => ((hostSpacesOfNorm (Ht 0) T0 (π0O : (Ht 0).E) π0_norm).X i).L0)
    (fun _ i _ => ((hostSpacesOfNorm (Ht 0) T0 (π0O : (Ht 0).E) π0_norm).X i).standardTuple_isLattice)
    (gap 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => false) (fun _ => rfl) 1 1 1 le_rfl Unit (fun _ => ()) (fun _ => ())
    (lbl 0) (fun _ => by norm_num [T0]) (fun _ _ => linePer 1) (fun _ => (stdHLat (Ht 0).E Unit).L)
    (localDataAtServedPlace' (Ht 0) (fun _ _ => hcA 0) (fun _ : Unit => oneCls 1 one_pos) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))
    (localData_rank_eq_classes (Ht 0) (fun _ _ => hcA 0) (fun _ : Unit => oneCls 1 one_pos) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))

end GlobalTheory.Core.Int.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParametersLinearIndependent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem parIndep : ∀ D : D7, ParIndep D := by
  intro D c hc j hj s hs ι x B hpar hB
  classical
  have hlat := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2
  rw [linearIndependent_iff']
  intro t a hsum i₀ hi₀
  obtain ⟨hne0, _⟩ := hpar i₀
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val (x i₀) v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne0
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simpa [PiLocalization₂.val] using h w
  let p : ι → Prop := fun i => PiLocalization₂.val (x i) v ≠ 0
  let f : {i // p i} → (GA D s.V → ℂ) := fun i g => conj (PiLocalization₂.val (x i.1) v g)
  have hli : LinearIndependent ℂ f := by
    refine GlobalTheory.T.linearIndependent_of_ne_zero_of_isParamFunV_of_separated D s.V c.S {i // p i} f (fun i => B i.1) ?_ ?_ ?_
    · intro i h0
      apply i.2
      funext g
      have := congrFun h0 g
      simpa [f] using this
    · intro i
      have h1 := (hpar i.1).2 v i.2
      unfold ParFun at h1
      exact (hlat _ _).1 h1
    · intro i i' hii'
      exact hB i.1 i'.1 (fun h => hii' (Subtype.ext h))
  rw [linearIndependent_iff'] at hli
  have hsum' : ∀ g, ∑ i ∈ t, a i * PiLocalization₂.val (x i) v g = 0 := by
    intro g
    have := congrArg (fun y : s.CC c => PiLocalization₂.val y v g) hsum
    simpa [PiLocalization₂.val, Finset.sum_apply] using this
  have key := hli (t.subtype p) (fun i => conj (a i.1)) ?_ ⟨i₀, hv⟩ (by simp [Finset.mem_subtype, hi₀])
  · simpa using key
  · funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, f, Pi.zero_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun i => conj (a i) * conj (PiLocalization₂.val (x i) v g)) (p := p)]
    rw [Finset.sum_filter_of_ne]
    · rw [← map_zero (starRingEnd ℂ), ← hsum' g, map_sum]
      simp [map_mul]
    · intro i _ hne h0
      apply hne
      simp [h0]

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels : ∀ D : D7, ForStageQ D fun c w _ s => MeasurableSet (levSet s) ∧ MeasurableSet (intOff c s) ∧ (∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L) ∧ (∀ g ∈ levSet s, ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ (∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ ∃ mR, IsLevMeas s mR := by
  first | exact @GlobalTheory.ChainTw.LevLoc.levLoc | exact GlobalTheory.ChainTw.LevLoc.levLoc | (intros; apply GlobalTheory.ChainTw.LevLoc.levLoc <;> assumption)
end

